/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanMaskSubset
import PCP.Algebraic.BooleanCoefficientRecovery

/-!
# Stored Boolean coefficient evaluation

Coefficient lists use the exact increasing-mask order of the production codec.
The natural sum below accumulates active coefficients; reducing it modulo two
is precisely polynomial evaluation at the supplied Boolean point.
-/

namespace PCP.Lang.BooleanCoefficientList

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientIndex BooleanLoops

/-- Dense stored bits of the actual coefficient vector. -/
def encode {t r : ℕ} (p : Coefficients t r) : List ℕ :=
  List.ofFn fun i => (wordEquiv t r p i).val

@[simp] theorem encode_length {t r : ℕ} (p : Coefficients t r) :
    (encode p).length = dimension t r := by simp [encode]

theorem encode_bits {t r : ℕ} (p : Coefficients t r) : ∀ c ∈ encode p, c < 2 := by
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact ZMod.val_lt _

/-- Missing coefficients are zero, so the scalar kernel is defined for all stored lists. -/
def terms (t x : ℕ) : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | m :: ms, cs => cs.headD 0 * truth (BooleanMaskSubset.Contains t m x) +
      terms t x ms cs.tail

theorem terms_ofFn (t x n : ℕ) (ms cs : Fin n → ℕ) :
    terms t x (List.ofFn ms) (List.ofFn cs) =
      ∑ i, cs i * truth (BooleanMaskSubset.Contains t (ms i) x) := by
  induction n with
  | zero => simp [terms]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [terms, List.headD_cons, List.tail_cons, ih, Fin.sum_univ_succ]

/-- The numeric point code uses the same characteristic-mask convention. -/
def point (t : ℕ) (x : Fin (2 ^ t)) : Fin t → ZMod 2 :=
  BooleanCoefficientRecovery.indicator ((subsetCodeEquiv t).symm x)

/-- The stored mask scan evaluates exactly the semantic Boolean polynomial. -/
theorem terms_eq {t r : ℕ} (p : Coefficients t r) (x : Fin (2 ^ t)) :
    (terms t x.val (BooleanMask.masks t r) (encode p) : ZMod 2) =
      BooleanCoefficientArithmetic.evaluate (point t x) p := by
  rw [BooleanMask.masks_eq_canonicalMasks]
  unfold BooleanMask.canonicalMasks encode
  rw [terms_ofFn]
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [BooleanCoefficientArithmetic.evaluate]
  symm
  rw [← (monomialEquiv t r).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  unfold point
  rw [BooleanCoefficientRecovery.prod_indicator]
  have hm := BooleanMask.monomial_code t r i
  change p ((monomialEquiv t r).symm i) *
    (if ((monomialEquiv t r).symm i).val ⊆ (subsetCodeEquiv t).symm x then 1 else 0) =
    p ((monomialEquiv t r).symm i) *
      (truth (BooleanMaskSubset.Contains t _ x.val) : ZMod 2)
  rw [hm]
  simp only [truth, BooleanMaskSubset.contains_iff,
    (subsetCodeEquiv t).symm_apply_apply]
  by_cases h : ((monomialEquiv t r).symm i).val ⊆ (subsetCodeEquiv t).symm x <;>
    simp [h]

/-- Natural output bits agree with the semantic coefficient evaluator. -/
theorem terms_mod_eq {t r : ℕ} (p : Coefficients t r) (x : Fin (2 ^ t)) :
    terms t x.val (BooleanMask.masks t r) (encode p) % 2 =
      (BooleanCoefficientArithmetic.evaluate (point t x) p).val := by
  rw [← terms_eq]
  simp

end PCP.Lang.BooleanCoefficientList
