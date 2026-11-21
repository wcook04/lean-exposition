import PCP.Complexity.BinaryAdditionMachine
import PCP.Complexity.BinaryNormalizationMachine
import PCP.Complexity.SeedBits
import PCP.Complexity.FilteredZipMachine

/-!
# Natural subtraction by an actual binary tape machine

A finite borrow scan emits one raw difference bit per input position. Underflow
emits a high separator marker. The second pass sees that marker first, returning
zero on underflow; otherwise it strips high zero padding. The result is exactly
natural subtraction at the compiler's canonical binary encoding. Both sources
and scratch are cleared and arbitrary caller storage is preserved.
-/

namespace PCP.Machine.BinarySubtraction
open Turing PCP.Lang StateTransition

def borrowBit (a b borrow : Bool) : Bool := (!a && (b || borrow)) || (b && borrow)

def subtractBits (borrow : Bool) : List Bool → List Bool → List Bool × Bool
  | [], [] => ([], borrow)
  | [], b :: ys =>
      let r := subtractBits (borrowBit false b borrow) [] ys
      (BinaryAddition.sumBit false b borrow :: r.1, r.2)
  | a :: xs, ys =>
      let b := ys.headD false
      let r := subtractBits (borrowBit a b borrow) xs ys.tail
      (BinaryAddition.sumBit a b borrow :: r.1, r.2)
termination_by xs ys => xs.length + ys.length

lemma subtractBits_length (xs ys : List Bool) (borrow : Bool) :
    (subtractBits borrow xs ys).1.length = max xs.length ys.length := by
  induction xs generalizing ys borrow with
  | nil =>
      induction ys generalizing borrow with
      | nil => simp [subtractBits]
      | cons b ys ih => simp [subtractBits, ih]
  | cons a xs ih =>
      cases ys with
      | nil => simp [subtractBits, ih]
      | cons b ys => simp [subtractBits, ih, max_add_add_right]

lemma bit_borrow (a b borrow : Bool) :
    cond a 1 0 + 2 * cond (borrowBit a b borrow) 1 0 =
      cond b 1 0 + cond borrow 1 0 + cond (BinaryAddition.sumBit a b borrow) 1 0 := by
  cases a <;> cases b <;> cases borrow <;> decide

lemma subtractBits_value (xs ys : List Bool) (borrow : Bool) :
    bitsValue xs + 2 ^ max xs.length ys.length * cond (subtractBits borrow xs ys).2 1 0 =
      bitsValue ys + cond borrow 1 0 + bitsValue (subtractBits borrow xs ys).1 := by
  induction xs generalizing ys borrow with
  | nil =>
      induction ys generalizing borrow with
      | nil => simp [subtractBits]
      | cons b ys ih =>
          have h := ih (borrowBit false b borrow)
          simp only [subtractBits, List.length_nil, List.length_cons, Nat.zero_max,
            bitsValue_nil, bitsValue_cons, pow_succ] at h ⊢
          cases b <;> cases borrow <;>
            simp [borrowBit, BinaryAddition.sumBit, Nat.bit] at h ⊢ <;> (try split_ifs at h ⊢) <;> nlinarith [h]
  | cons a xs ih =>
      cases ys with
      | nil =>
          have h := ih [] (borrowBit a false borrow)
          simp only [subtractBits, List.headD_nil, List.tail_nil, List.length_nil,
            List.length_cons, Nat.max_zero, bitsValue_nil, bitsValue_cons, pow_succ] at h ⊢
          cases a <;> cases borrow <;>
            simp [borrowBit, BinaryAddition.sumBit, Nat.bit] at h ⊢ <;> (try split_ifs at h ⊢) <;> nlinarith [h]
      | cons b ys =>
          have h := ih ys (borrowBit a b borrow)
          simp only [subtractBits, List.headD_cons, List.tail_cons, List.length_cons,
            max_add_add_right, bitsValue_cons, pow_succ] at h ⊢
          cases a <;> cases b <;> cases borrow <;>
            simp [borrowBit, BinaryAddition.sumBit, Nat.bit] at h ⊢ <;> (try split_ifs at h ⊢) <;> nlinarith [h]

lemma finalBorrow_iff (xs ys : List Bool) (borrow : Bool) :
    (subtractBits borrow xs ys).2 = true ↔ bitsValue xs < bitsValue ys + cond borrow 1 0 := by
  have h := subtractBits_value xs ys borrow
  have hr := bitsValue_lt (subtractBits borrow xs ys).1
  rw [subtractBits_length] at hr
  cases borrow <;> cases hb : (subtractBits _ xs ys).2 <;> simp only [hb, Bool.cond_false,
    Bool.cond_true, mul_zero, mul_one, add_zero] at h hr ⊢ <;> simp <;> omega

lemma subtractBits_noBorrow (xs ys : List Bool) (borrow : Bool)
    (h : (subtractBits borrow xs ys).2 = false) :
    bitsValue (subtractBits borrow xs ys).1 = bitsValue xs - (bitsValue ys + cond borrow 1 0) := by
  have hv := subtractBits_value xs ys borrow
  simp only [h, Bool.cond_false, mul_zero, add_zero] at hv
  omega

/-- Finite borrow control, with a terminal separator precisely on underflow. -/
abbrev spec : BinaryZip.Spec where
  State := Bool
  init := false
  next borrow a b := borrowBit (BinaryAddition.readBit a) (BinaryAddition.readBit b) borrow
  emit borrow a b := some (.bit
    (BinaryAddition.sumBit (BinaryAddition.readBit a) (BinaryAddition.readBit b) borrow))
  finish borrow := cond borrow (some .sep) none

/-- Materialized raw difference together with its high underflow marker. -/
def rawTape (result : List Bool × Bool) : List Sym :=
  ofBits result.1 ++ cond result.2 [Sym.sep] []

lemma rawTape_cons (a : Bool) (xs : List Bool) (borrow : Bool) :
    rawTape (a :: xs, borrow) = Sym.bit a :: rawTape (xs, borrow) := rfl

lemma output_nil_nil (borrow : Bool) :
    spec.output borrow [] [] = rawTape ([], borrow) := by
  cases borrow <;> simp [BinaryZip.Spec.output, spec, rawTape, ofBits]

lemma output_nil_cons (borrow b : Bool) (ys : List Bool) :
    spec.output borrow [] (ofBits (b :: ys)) =
      Sym.bit (BinaryAddition.sumBit false b borrow) ::
        spec.output (borrowBit false b borrow) [] (ofBits ys) := by
  simp [BinaryZip.Spec.output, spec, ofBits, BinaryAddition.readBit]

lemma output_cons_nil (borrow a : Bool) (xs : List Bool) :
    spec.output borrow (ofBits (a :: xs)) [] =
      Sym.bit (BinaryAddition.sumBit a false borrow) ::
        spec.output (borrowBit a false borrow) (ofBits xs) [] := by
  simp [BinaryZip.Spec.output, spec, ofBits, BinaryAddition.readBit]

lemma output_cons_cons (borrow a b : Bool) (xs ys : List Bool) :
    spec.output borrow (ofBits (a :: xs)) (ofBits (b :: ys)) =
      Sym.bit (BinaryAddition.sumBit a b borrow) ::
        spec.output (borrowBit a b borrow) (ofBits xs) (ofBits ys) := by
  simp [BinaryZip.Spec.output, spec, ofBits, BinaryAddition.readBit]

/-- The finite scan materializes every difference bit and its final borrow status. -/
theorem output_subtractBits (xs ys : List Bool) (borrow : Bool) :
    spec.output borrow (ofBits xs) (ofBits ys) = rawTape (subtractBits borrow xs ys) := by
  induction xs generalizing ys borrow with
  | nil =>
      induction ys generalizing borrow with
      | nil => simpa [ofBits, subtractBits] using output_nil_nil borrow
      | cons b ys ih =>
          change spec.output borrow [] (ofBits (b :: ys)) = _
          change ∀ borrow, spec.output borrow [] (ofBits ys) = _ at ih
          rw [output_nil_cons, ih]
          simp only [subtractBits, rawTape_cons]
  | cons a xs ih =>
      cases ys with
      | nil =>
          change spec.output borrow (ofBits (a :: xs)) [] = _
          rw [output_cons_nil]
          have hi := ih [] (borrowBit a false borrow)
          change spec.output (borrowBit a false borrow) (ofBits xs) [] = _ at hi
          rw [hi]
          simp only [subtractBits, List.headD_nil, List.tail_nil, rawTape_cons]
      | cons b ys =>
          rw [output_cons_cons, ih]
          simp only [subtractBits, List.headD_cons, List.tail_cons, rawTape_cons]

/-- Canonicalization recovers saturated natural subtraction, even for padded input words. -/
theorem normalized_output (xs ys : List Bool) :
    (BinaryNormalize.spec.output (some false)
      (spec.output false (ofBits xs) (ofBits ys)).reverse).reverse =
        natTape (bitsValue xs - bitsValue ys) := by
  rw [output_subtractBits]
  cases hb : (subtractBits false xs ys).2 with
  | false =>
      simp only [rawTape, hb, Bool.cond_false, List.append_nil]
      rw [BinaryNormalize.normalize_output, subtractBits_noBorrow xs ys false hb]
      simp
  | true =>
      simp only [rawTape, hb, Bool.cond_true]
      rw [BinaryNormalize.marked_output]
      have h := (finalBorrow_iff xs ys false).mp hb
      simp only [Bool.cond_false, Nat.add_zero] at h
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]

/-- Exact canonical register-level semantics of the normalized borrow scan. -/
theorem output_natTape (n m : ℕ) :
    (BinaryNormalize.spec.output (some false)
      (spec.output false (natTape n) (natTape m)).reverse).reverse = natTape (n - m) := by
  simpa only [natTape, bitsValue_binDigits] using
    normalized_output (binDigits n) (binDigits m)

/-- Actual subtraction machine, including underflow, padding removal, and caller preservation. -/
def subtractionEvals (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)
    (n m : ℕ) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (FilteredZip.machine spec BinaryNormalize.spec F Γf).step
      (FilteredZip.cfg spec BinaryNormalize.spec F Γf (some .one) false
        (natTape n) (natTape m) [] [] S)
      (some (FilteredZip.cfg spec BinaryNormalize.spec F Γf none false
        [] [] [] (natTape (n - m)) S)) (2 * max (Nat.size n) (Nat.size m) + 3) := by
  simpa only [show spec.init = false from rfl,
    show BinaryNormalize.spec.init = some false from rfl, output_natTape, natTape_length] using
    (FilteredZip.evals (spec := spec) (filter := BinaryNormalize.spec) (natTape n) (natTape m) S)

end PCP.Machine.BinarySubtraction
