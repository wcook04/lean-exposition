import PCP.Complexity.ReverseSymbolsMachine
import PCP.Complexity.FiniteTransducer
import PCP.Complexity.MachineComposition

/-!
# Machine conversion from a doubled-prefix pair encoding

The binary format doubles every bit of the first argument, writes `false,true`,
then copies the second argument. This is Complexitylib's public pair format; the
definition below is a local codec, not a new definition of a complexity class.

The parser is an actual linear-time finite transducer. Composing it with the
reversal machine and any concrete relation checker gives the precise source-side
adapter required by `TapeBooleanInterface`.
-/

namespace PCP.Machine.ReferencePair

open Turing

/-- The doubled-prefix binary pair format, before conversion to tape symbols. -/
def bits : List Bool → List Bool → List Bool
  | [], y => false :: true :: y
  | b :: x, y => b :: b :: bits x y

theorem bits_length (x y : List Bool) : (bits x y).length = 2 * x.length + 2 + y.length := by
  induction x <;> simp_all [bits] <;> omega

/-- Parser phases: between doubled symbols, after their first bit, and in the suffix. -/
inductive Phase where
  | first
  | second : Bool → Phase
  | suffix
  | bad
  deriving Fintype

/-- A deterministic streaming decoder; malformed prefixes enter a silent error state. -/
def parser : TransducerSpec where
  State := Phase
  init := .first
  next := fun s a => match s, a with
    | .first, .bit b => .second b
    | .second b, .bit c => if b = c then .first else if b then .bad else .suffix
    | .suffix, _ => .suffix
    | _, _ => .bad
  emit := fun s a => match s, a with
    | .second b, .bit c => if b = c then some (.bit b) else if b then none else some .sep
    | .suffix, .bit b => some (.bit b)
    | _, _ => none

theorem output_suffix (y : List Bool) : parser.output .suffix (ofBits y) = ofBits y := by
  induction y <;> simp_all [ofBits, TransducerSpec.output, parser]

/-- The actual transducer decodes every well-formed pair to the fixed public separator format. -/
theorem parser_pair (x y : List Bool) :
    parser.output parser.init (ofBits (bits x y)) = encodePair (x, y) := by
  induction x with
  | nil =>
    change Sym.sep :: parser.output .suffix (ofBits y) = Sym.sep :: ofBits y
    rw [output_suffix]
  | cons b x ih =>
    cases b
    · exact congrArg (List.cons (.bit false)) ih
    · exact congrArg (List.cons (.bit true)) ih

/-- The parser's linear-time certificate at the pair format. -/
noncomputable def parserWitness :
    TM2ComputableInPolyTime (fun p : List Bool × List Bool => ofBits (bits p.1 p.2))
      encodePair id :=
  transducerComputable parser Empty (fun _ => Sym)
    (fun p : List Bool × List Bool => ofBits (bits p.1 p.2)) encodePair id
      (fun p => (parser_pair p.1 p.2).symm)

/-- Reverse the externally encoded word, then decode its doubled-prefix format. -/
noncomputable def prepareWitness :
    TM2ComputableInPolyTime
      (fun p : List Bool × List Bool => (ofBits (bits p.1 p.2)).reverse) encodePair id := by
  let reverse := ReverseSymbols.witness
    (fun p : List Bool × List Bool => (ofBits (bits p.1 p.2)).reverse)
  have reverse' : TM2ComputableInPolyTime
      (fun p : List Bool × List Bool => (ofBits (bits p.1 p.2)).reverse)
      (fun p => ofBits (bits p.1 p.2)) id := by
    simpa only [List.reverse_reverse] using reverse
  exact composeWitness reverse' parserWitness

/-- An arbitrary concrete relation checker receives its original encoded arguments,
after actual reversal, parsing and stack handoff. -/
noncomputable def checkerWitness (R : List Bool → List Bool → Bool)
    (hR : TM2ComputableInPolyTime encodePair encodeBool (fun p => R p.1 p.2)) :
    TM2ComputableInPolyTime
      (fun p : List Bool × List Bool => (ofBits (bits p.1 p.2)).reverse)
      encodeBool (fun p => R p.1 p.2) :=
  composeWitness prepareWitness hR

end PCP.Machine.ReferencePair
