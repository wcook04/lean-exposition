import PCP.Complexity.FiniteTransducer
import PCP.Complexity.LangTapeEncoding

/-!
# Concrete machines for the head and tail of encoded natural lists

Both machines operate on the exact separator-delimited materialized representation.
The head machine returns zero on an empty list; zero's numeral tape is empty.
The tail machine discards precisely the first numeral and its separator. These are
the data-extraction primitives needed by the structured language's list pop.
-/

namespace PCP.Machine.LangList

open Turing PCP.Lang

/-- Before the first separator discard cells; after it retain every remaining cell. -/
def tailSpec : TransducerSpec where
  State := Bool
  init := false
  next done cell := match cell with
    | .bit _ => done
    | .sep => true
  emit done cell := if done then some cell else none

theorem tail_output_true (xs : List Sym) : tailSpec.output true xs = xs := by
  induction xs with
  | nil => rfl
  | cons c xs ih => cases c <;> simpa [tailSpec, TransducerSpec.output] using ih

/-- Delimiters, rather than numeral lengths stored in control, identify the first cell. -/
theorem tail_output_chunk (xs : List Bool) (rest : List Sym) :
    tailSpec.output false (ofBits xs ++ .sep :: rest) = rest := by
  induction xs with
  | nil => simpa [ofBits, TransducerSpec.output, tailSpec] using tail_output_true rest
  | cons c xs ih => simpa [ofBits, TransducerSpec.output, tailSpec] using ih

/-- The transducer removes exactly one encoded natural, including when that natural is zero. -/
theorem tail_output_encode (xs : List ℕ) : tailSpec.output false (encodeNats xs) =
    encodeNats xs.tail := by
  cases xs with
  | nil => rfl
  | cons n xs =>
      simpa only [encodeNats, List.flatMap_cons, List.append_assoc, List.singleton_append,
        List.tail_cons] using tail_output_chunk (binDigits n) (encodeNats xs)

/-- Actual linear-time witness for list tail at the compiler's external encoding. -/
noncomputable def tailWitness : TM2ComputableInPolyTime encodeNats encodeNats List.tail :=
  transducerComputable tailSpec Empty (fun _ => Sym) encodeNats encodeNats List.tail
    (fun xs => (tail_output_encode xs).symm)

/-- Keep bits before the first separator and discard everything after it. -/
def headSpec : TransducerSpec where
  State := Bool
  init := false
  next done cell := match cell with
    | .bit _ => done
    | .sep => true
  emit done cell := match cell with
    | .bit b => if done then none else some (.bit b)
    | .sep => none

theorem head_output_true (xs : List Sym) : headSpec.output true xs = [] := by
  induction xs with
  | nil => rfl
  | cons c xs ih => cases c <;> simpa [headSpec, TransducerSpec.output] using ih

/-- Reading the first numeral preserves its least-significant-bit-first order. -/
theorem head_output_chunk (xs : List Bool) (rest : List Sym) :
    headSpec.output false (ofBits xs ++ .sep :: rest) = ofBits xs := by
  induction xs with
  | nil => simpa [ofBits, TransducerSpec.output, headSpec] using head_output_true rest
  | cons c xs ih =>
      simpa [ofBits, TransducerSpec.output, headSpec] using congrArg (Sym.bit c :: ·) ih

/-- Empty lists and zero-valued heads both yield the correct empty binary numeral. -/
theorem head_output_encode (xs : List ℕ) : headSpec.output false (encodeNats xs) =
    natTape (xs.headD 0) := by
  cases xs with
  | nil => simp [encodeNats, natTape, binDigits, ofBits, TransducerSpec.output]
  | cons n xs =>
      simpa only [encodeNats, List.flatMap_cons, List.append_assoc, List.singleton_append,
        List.headD_cons, natTape] using head_output_chunk (binDigits n) (encodeNats xs)

/-- Actual linear-time witness for the value extracted by a list pop. -/
noncomputable def headWitness :
    TM2ComputableInPolyTime encodeNats natTape (fun xs : List ℕ => xs.headD 0) :=
  transducerComputable headSpec Empty (fun _ => Sym) encodeNats natTape (fun xs => xs.headD 0)
    (fun xs => (head_output_encode xs).symm)

@[simp] theorem tailWitness_time : tailWitness.time = 2 * Polynomial.X + 2 := rfl

@[simp] theorem headWitness_time : headWitness.time = 2 * Polynomial.X + 2 := rfl

end PCP.Machine.LangList
