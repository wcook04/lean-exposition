import PCP.Complexity.LangTapeEncoding
import PCP.Complexity.ReverseTransducer
/-!
# Linear-time canonicalization of binary register tapes

Arithmetic scans may leave high zero padding. This machine removes it and returns
the exact canonical numeral tape of the decoded value. A terminal separator is
also supported as an underflow marker: such a word returns zero. The marker is
seen first in the reversed scan, so no already-produced result must be erased.
-/

namespace PCP.Machine.BinaryNormalize

open Turing PCP.Lang StateTransition

def trim (xs : List Bool) : List Bool := (xs.reverse.dropWhile Bool.not).reverse

lemma trim_cons (b : Bool) (xs : List Bool) :
    trim (b :: xs) = if trim xs = [] then cond b [true] [] else b :: trim xs := by
  cases he : xs.reverse.dropWhile Bool.not with
  | nil =>
      cases b <;> simp [trim, List.reverse_cons, List.dropWhile_append, he]
  | cons c ys =>
      simp [trim, List.reverse_cons, List.dropWhile_append, he]

lemma trim_eq_bitsValue_bits (xs : List Bool) : trim xs = (bitsValue xs).bits := by
  induction xs with
  | nil => simp [trim]
  | cons b xs ih =>
      rw [trim_cons, ih, bitsValue_cons]
      by_cases hv : bitsValue xs = 0
      · cases b <;> simp [hv, Nat.bit]
      · have hn : (bitsValue xs).bits ≠ [] := by
          intro he
          have h := congrArg bitsValue he
          simp only [bitsValue_bits, bitsValue_nil] at h
          exact hv h
        rw [ite_eq_right hn, Nat.bits_append_bit _ _ (fun h => False.elim (hv h))]

/-- `none` discards a marked word; `some false` trims; `some true` copies. -/
abbrev spec : TransducerSpec where
  State := Option Bool
  init := some false
  next state cell := match cell with
    | .sep => none
    | .bit b => state.map (· || b)
  emit state cell := match state, cell with
    | some seen, .bit b => if seen || b then some (.bit b) else none
    | _, _ => none

lemma output_invalid (xs : List Sym) : spec.output none xs = [] := by
  induction xs with
  | nil => rfl
  | cons c xs ih => cases c <;> simpa [TransducerSpec.output, spec] using ih

lemma output_copy (xs : List Bool) : spec.output (some true) (ofBits xs) = ofBits xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      simpa [TransducerSpec.output, spec, ofBits] using congrArg (Sym.bit b :: ·) ih

lemma output_trim (xs : List Bool) :
    spec.output (some false) (ofBits xs) = ofBits (xs.dropWhile Bool.not) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b with
      | false => simpa [TransducerSpec.output, spec, ofBits, List.dropWhile] using ih
      | true =>
          simpa [TransducerSpec.output, spec, ofBits, List.dropWhile] using
            congrArg (Sym.bit true :: ·) (output_copy xs)

/-- The reverse scan removes only high padding and preserves the decoded value. -/
theorem normalize_output (xs : List Bool) :
    (spec.output (some false) (ofBits xs).reverse).reverse = natTape (bitsValue xs) := by
  rw [show (ofBits xs).reverse = ofBits xs.reverse by simp [ofBits], output_trim]
  have h : (ofBits (xs.reverse.dropWhile Bool.not)).reverse = ofBits (trim xs) := by
    simp [ofBits, trim]
  rw [h, trim_eq_bitsValue_bits]
  simp only [natTape, binDigits_eq_bits]

/-- A high separator marks underflow and causes every lower cell to be discarded. -/
theorem marked_output (xs : List Sym) :
    (spec.output (some false) (xs ++ [Sym.sep]).reverse).reverse = natTape 0 := by
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
  change (spec.output none xs.reverse).reverse = natTape 0
  rw [output_invalid]
  rfl

/-- Actual finite-control canonicalization with exact two-pass cost. -/
def normalizeEvals (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)
    (xs : List Bool) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (ReverseTransducer.machine spec F Γf).step
      (ReverseTransducer.cfg spec F Γf (some .one) (some false) (ofBits xs) [] [] S)
      (some (ReverseTransducer.cfg spec F Γf none (some false)
        [] [] (natTape (bitsValue xs)) S)) (2 * xs.length + 2) where
  steps := 2 * xs.length + 2
  evals_in_steps := by
    simpa only [show spec.init = some false from rfl, normalize_output, length_ofBits] using
      (ReverseTransducer.trace (spec := spec) (ofBits xs) S)
  steps_le_m := le_refl _

/-- Underflow cleanup costs one charged visit in each pass for every physical cell. -/
def markedEvals (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)
    (xs : List Sym) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (ReverseTransducer.machine spec F Γf).step
      (ReverseTransducer.cfg spec F Γf (some .one) (some false) (xs ++ [Sym.sep]) [] [] S)
      (some (ReverseTransducer.cfg spec F Γf none (some false) [] [] (natTape 0) S))
      (2 * (xs.length + 1) + 2) where
  steps := 2 * (xs.length + 1) + 2
  evals_in_steps := by
    simpa only [show spec.init = some false from rfl, marked_output, List.length_append,
      List.length_singleton] using (ReverseTransducer.trace (spec := spec) (xs ++ [Sym.sep]) S)
  steps_le_m := le_refl _

end PCP.Machine.BinaryNormalize
