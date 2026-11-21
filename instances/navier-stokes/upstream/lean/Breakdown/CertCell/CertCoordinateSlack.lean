import Mathlib
import Breakdown.CertCell.CertificateStatements

open Matrix

noncomputable section

namespace Breakdown.CertCell.Certificate

private def optionValue {m : Type} [Fintype m] [DecidableEq m] (y : m → ℝ) (o : Option m) : ℝ :=
  ∑ k, if o = some k then y k else 0

private lemma optionValue_sq {m : Type} [Fintype m] [DecidableEq m] (y : m → ℝ) (o : Option m) :
    optionValue y o ^ 2 = ∑ k, if o = some k then y k ^ 2 else 0 := by
  cases o with
  | none => simp [optionValue]
  | some a => simp [optionValue]

private lemma matrix_mulVec_apply {n m : Type} [Fintype m] [DecidableEq m]
    (R : CoordinateRealification n m) (y : m → ℝ) (j : n) :
    (R.matrix *ᵥ ofRealVec y) j
      = ((optionValue y (R.realIndex j) : ℝ) : ℂ)
        + (R.imagSign j : ℂ) * Complex.I * ((optionValue y (R.imagIndex j) : ℝ) : ℂ) := by
  simp only [Matrix.mulVec, dotProduct, CoordinateRealification.matrix, ofRealVec, optionValue,
    Complex.ofReal_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> push_cast <;> ring

private lemma norm_sq_coordinate (a b s : ℝ) (hs : s ^ 2 = 1) :
    ‖(a : ℂ) + (s : ℂ) * Complex.I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have h : (a : ℂ) + (s : ℂ) * Complex.I * (b : ℂ) = (a : ℂ) + ((s * b : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
  have h' : (s * b) ^ 2 = s ^ 2 * b ^ 2 := by ring
  rw [h', hs, one_mul]

open Classical in
private lemma owned_sum {n m : Type} [Fintype m] [DecidableEq m]
    (R : CoordinateRealification n m) (y : m → ℝ) (j : n)
    (h : ∀ k, R.realIndex j = some k → R.imagIndex j ≠ some k) :
    optionValue y (R.realIndex j) ^ 2 + optionValue y (R.imagIndex j) ^ 2
      = ∑ k, if R.Owns j k then y k ^ 2 else 0 := by
  rw [optionValue_sq, optionValue_sq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h1 : R.realIndex j = some k <;> by_cases h2 : R.imagIndex j = some k
  · exact absurd h2 (h k h1)
  · simp [CoordinateRealification.Owns, h1, h2]
  · simp [CoordinateRealification.Owns, h1, h2]
  · simp [CoordinateRealification.Owns, h1, h2]

theorem coordinateSlack : CoordinateSlack := by
  intro n m _ _ _ R pivot s y hR
  classical
  have hnorm : ∀ j ∈ pivot, s j * ‖(R.matrix *ᵥ ofRealVec y) j‖ ^ 2
      = ∑ k, s j * if R.Owns j k then y k ^ 2 else 0 := by
    intro j hj
    rw [matrix_mulVec_apply, norm_sq_coordinate _ _ _ (hR.sign_sq j hj),
      owned_sum R y j (hR.real_ne_imag j hj), Finset.mul_sum]
  rw [Finset.sum_congr rfl hnorm, Finset.sum_comm, CoordinateRealification.pivotImage,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [CoordinateRealification.slackOn, Finset.sum_mul]
  split_ifs with hk
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · push Not at hk
    refine Finset.sum_eq_zero fun j hj => ?_
    simp [hk j hj]

end Breakdown.CertCell.Certificate
