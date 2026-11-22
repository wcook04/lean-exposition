import PCP.Complexity.BinaryZipMachine
import PCP.Complexity.LangTapeEncoding

/-!
# Concrete binary comparison machines

The finite control records the comparison of bits already consumed. Each more
significant unequal bit overrides that record. The proof works for arbitrary
bit words, including zero padding. Equality and strict order return canonical
natural zero or one, consume both inputs, and preserve every caller tape.
-/

namespace PCP.Machine.BinaryComparison
open Turing PCP.Lang StateTransition

def readBit : Option Sym → Bool
  | some (.bit b) => b
  | _ => false

def compareStep (a b : Bool) (previous : Ordering) : Ordering :=
  if a = b then previous else if a then .gt else .lt

def compareValue (n m : ℕ) (previous : Ordering) : Ordering :=
  if n < m then .lt else if m < n then .gt else previous

lemma compareValue_bit (n m : ℕ) (a b : Bool) (previous : Ordering) :
    compareValue n m (compareStep a b previous) =
      compareValue (Nat.bit a n) (Nat.bit b m) previous := by
  have hbit : ∀ (c : Bool) (k : ℕ), Nat.bit c k = 2 * k + cond c 1 0 := by
    intro c k; cases c <;> rfl
  rw [hbit, hbit]
  unfold compareValue compareStep
  cases a <;> cases b <;> simp only [Bool.cond_true, Bool.cond_false, Nat.add_zero] <;>
    split_ifs <;> first | rfl | (exfalso; omega)

abbrev spec (accept : Ordering → Bool) : BinaryZip.Spec where
  State := Ordering
  init := .eq
  next previous a b := compareStep (readBit a) (readBit b) previous
  emit _ _ _ := none
  finish state := cond (accept state) (some (.bit true)) none

lemma output_nil_nil (accept : Ordering → Bool) (state : Ordering) :
    (spec accept).output state [] [] = cond (accept state) [Sym.bit true] [] := by
  cases he : accept state <;> simp [BinaryZip.Spec.output, spec, he]

lemma output_nil_cons (accept : Ordering → Bool) (state : Ordering) (b : Bool)
    (ys : List Bool) :
    (spec accept).output state [] (ofBits (b :: ys)) =
      (spec accept).output (compareStep false b state) [] (ofBits ys) := by
  simp [BinaryZip.Spec.output, spec, ofBits, readBit]

lemma output_cons_nil (accept : Ordering → Bool) (state : Ordering) (a : Bool)
    (xs : List Bool) :
    (spec accept).output state (ofBits (a :: xs)) [] =
      (spec accept).output (compareStep a false state) (ofBits xs) [] := by
  simp [BinaryZip.Spec.output, spec, ofBits, readBit]

lemma output_cons_cons (accept : Ordering → Bool) (state : Ordering) (a b : Bool)
    (xs ys : List Bool) :
    (spec accept).output state (ofBits (a :: xs)) (ofBits (b :: ys)) =
      (spec accept).output (compareStep a b state) (ofBits xs) (ofBits ys) := by
  simp [BinaryZip.Spec.output, spec, ofBits, readBit]

theorem output_bitsValue (accept : Ordering → Bool) (xs ys : List Bool) (state : Ordering) :
    (spec accept).output state (ofBits xs) (ofBits ys) =
      cond (accept (compareValue (bitsValue xs) (bitsValue ys) state)) [Sym.bit true] [] := by
  induction xs generalizing ys state with
  | nil =>
      induction ys generalizing state with
      | nil => simp [ofBits, output_nil_nil, bitsValue, compareValue]
      | cons b ys ih =>
          change (spec accept).output state [] (ofBits (b :: ys)) = _
          change ∀ state, (spec accept).output state [] (ofBits ys) = _ at ih
          rw [output_nil_cons, ih]
          have he := compareValue_bit 0 (bitsValue ys) false b state
          simp only [Nat.bit_false, Nat.mul_zero] at he
          simp only [bitsValue_nil, bitsValue_cons]
          rw [he]
  | cons a xs ih =>
      cases ys with
      | nil =>
          change (spec accept).output state (ofBits (a :: xs)) [] = _
          rw [output_cons_nil]
          have hi := ih [] (compareStep a false state)
          change (spec accept).output (compareStep a false state) (ofBits xs) [] = _ at hi
          rw [hi]
          have he := compareValue_bit (bitsValue xs) 0 a false state
          simp only [Nat.bit_false, Nat.mul_zero] at he
          simp only [bitsValue_nil, bitsValue_cons]
          rw [he]
      | cons b ys =>
          rw [output_cons_cons, ih]
          simp only [bitsValue_cons]
          rw [compareValue_bit]

/-- A natural Boolean uses at most one bit of tape. -/
theorem natTape_cond (b : Bool) : natTape (cond b 1 0) =
    cond b [Sym.bit true] [] := by cases b <;> rfl

/-- The scan's final finite state determines its canonical natural output. -/
theorem output_natTape (accept : Ordering → Bool) (n m : ℕ) :
    (spec accept).output .eq (natTape n) (natTape m) =
      natTape (cond (accept (compareValue n m .eq)) 1 0) := by
  rw [natTape_cond]
  simpa only [natTape, bitsValue_binDigits] using
    output_bitsValue accept (binDigits n) (binDigits m) .eq

/-- Strict natural comparison is the scan accepting the `lt` terminal state. -/
theorem lt_output_natTape (n m : ℕ) :
    (spec (· == .lt)).output .eq (natTape n) (natTape m) =
      natTape (if n < m then 1 else 0) := by
  rw [output_natTape]
  congr 1
  unfold compareValue
  split_ifs <;> rfl

/-- Equality is the same finite scan accepting the `eq` terminal state. -/
theorem eq_output_natTape (n m : ℕ) :
    (spec (· == .eq)).output .eq (natTape n) (natTape m) =
      natTape (if n = m then 1 else 0) := by
  rw [output_natTape]
  congr 1
  unfold compareValue
  split_ifs <;> simp_all
  all_goals omega

/-- The concrete comparison machine, with caller storage and cleanup included. -/
def comparisonEvals (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)
    (accept : Ordering → Bool) (n m : ℕ) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (BinaryZip.machine (spec accept) F Γf).step
      (BinaryZip.cfg (spec accept) F Γf (some .one) .eq (natTape n) (natTape m) [] [] S)
      (some (BinaryZip.cfg (spec accept) F Γf none .eq [] [] []
        (natTape (cond (accept (compareValue n m .eq)) 1 0)) S))
      (max (Nat.size n) (Nat.size m) + 3) where
  steps := max (Nat.size n) (Nat.size m) +
    (natTape (cond (accept (compareValue n m .eq)) 1 0)).length + 2
  evals_in_steps := by
    simpa only [show (spec accept).init = .eq from rfl, output_natTape,
      natTape_length] using
      (BinaryZip.trace (spec := spec accept) (natTape n) (natTape m) S)
  steps_le_m := by
    rw [natTape_cond]
    cases accept (compareValue n m .eq) <;> simp

/-- Framed equality primitive for the language's natural-register operation. -/
def equalityEvals (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)
    (n m : ℕ) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (BinaryZip.machine (spec (· == .eq)) F Γf).step
      (BinaryZip.cfg (spec (· == .eq)) F Γf (some .one) .eq
        (natTape n) (natTape m) [] [] S)
      (some (BinaryZip.cfg (spec (· == .eq)) F Γf none .eq [] [] []
        (natTape (if n = m then 1 else 0)) S))
      (max (Nat.size n) (Nat.size m) + 3) := by
  have he : natTape (cond ((compareValue n m .eq) == .eq) 1 0) =
      natTape (if n = m then 1 else 0) :=
    (output_natTape (· == .eq) n m).symm.trans (eq_output_natTape n m)
  simpa only [he] using comparisonEvals F Γf (· == .eq) n m S

/-- Framed strict-order primitive for the language's natural-register operation. -/
def lessThanEvals (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)
    (n m : ℕ) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (BinaryZip.machine (spec (· == .lt)) F Γf).step
      (BinaryZip.cfg (spec (· == .lt)) F Γf (some .one) .eq
        (natTape n) (natTape m) [] [] S)
      (some (BinaryZip.cfg (spec (· == .lt)) F Γf none .eq [] [] []
        (natTape (if n < m then 1 else 0)) S))
      (max (Nat.size n) (Nat.size m) + 3) := by
  have he : natTape (cond ((compareValue n m .eq) == .lt) 1 0) =
      natTape (if n < m then 1 else 0) :=
    (output_natTape (· == .lt) n m).symm.trans (lt_output_natTape n m)
  simpa only [he] using comparisonEvals F Γf (· == .lt) n m S

end PCP.Machine.BinaryComparison
