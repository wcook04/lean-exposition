import Mathlib
import Breakdown.CertCell.CertificateStatements

open Matrix

noncomputable section

namespace Breakdown.CertCell.Certificate

private lemma formValue_add {n : Type*} [Fintype n] (M N : Matrix n n ℂ) (z : n → ℂ) :
    complexFormValue (M + N) z = complexFormValue M z + complexFormValue N z := by
  unfold complexFormValue
  rw [add_mulVec, dotProduct_add, Complex.add_re]

private lemma formValue_sub {n : Type*} [Fintype n] (M N : Matrix n n ℂ) (z : n → ℂ) :
    complexFormValue (M - N) z = complexFormValue M z - complexFormValue N z := by
  unfold complexFormValue
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re]

private lemma formValue_eq_sum {n : Type*} [Fintype n] (M : Matrix n n ℂ) (z : n → ℂ) :
    complexFormValue M z = ∑ i, ∑ j, (star (z i) * M i j * z j).re := by
  unfold complexFormValue
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, mul_assoc]

private lemma re_star_mul_self {z : ℂ} : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

private lemma formValue_diagonal {n : Type*} [Fintype n] [DecidableEq n] (P : Finset n)
    (δ : n → ℝ) (z : n → ℂ) :
    complexFormValue (complexDiagonal P δ) z = ∑ j ∈ P, δ j * ‖z j‖ ^ 2 := by
  rw [formValue_eq_sum]
  have h : ∀ i, ∑ j, (star (z i) * complexDiagonal P δ i j * z j).re
      = if i ∈ P then δ i * ‖z i‖ ^ 2 else 0 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp only [complexDiagonal, pivotDiagonal, map_apply, diagonal_apply_eq]
      split_ifs
      · rw [← re_star_mul_self]
        simp [Complex.mul_re]
        ring
      · simp
    · intro j _ hj
      simp [complexDiagonal, pivotDiagonal, map_apply, diagonal_apply_ne _ (Ne.symm hj)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp_rw [h]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

private lemma formValue_pairMatrix {n q : Type*} [Fintype n] [Fintype q] (F : Matrix n q ℂ)
    (z : n → ℂ) :
    complexFormValue (F * Fᴴ) z = ∑ c, ‖∑ i, star (F i c) * z i‖ ^ 2 := by
  unfold complexFormValue
  rw [← mulVec_mulVec, dotProduct_mulVec]
  have h : star z ᵥ* F = star (Fᴴ *ᵥ z) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  rw [h]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [re_star_mul_self]
  simp [mulVec, dotProduct, conjTranspose_apply]

private lemma weighted_product_le {a b u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    a * b ≤ (u / v * a ^ 2 + v / u * b ^ 2) / 2 := by
  have key : (u / v * a ^ 2 + v / u * b ^ 2) / 2 - a * b = (u * a - v * b) ^ 2 / (2 * u * v) := by
    field_simp
    ring
  have : 0 ≤ (u * a - v * b) ^ 2 / (2 * u * v) := by positivity
  linarith

private lemma remainder_lower {n : Type*} [Fintype n] (R : Matrix n n ℂ) (w r : n → ℝ)
    (hR : ∀ i j, ‖R j i‖ = ‖R i j‖) (hw : ∀ j, 0 < w j)
    (hr : ∀ i, w i * ∑ j, ‖R i j‖ / w j ≤ r i) (z : n → ℂ) :
    -∑ i, r i * ‖z i‖ ^ 2 ≤ complexFormValue R z := by
  rw [formValue_eq_sum]
  have h1 : ∀ i j, -(‖R i j‖ * ((w i / w j * ‖z i‖ ^ 2 + w j / w i * ‖z j‖ ^ 2) / 2))
      ≤ (star (z i) * R i j * z j).re := by
    intro i j
    have e1 : -‖star (z i) * R i j * z j‖ ≤ (star (z i) * R i j * z j).re := by
      have := Complex.abs_re_le_norm (star (z i) * R i j * z j)
      have := neg_abs_le (star (z i) * R i j * z j).re
      linarith
    have e2 : ‖star (z i) * R i j * z j‖ = ‖R i j‖ * (‖z i‖ * ‖z j‖) := by
      rw [norm_mul, norm_mul, norm_star]
      ring
    have e3 := weighted_product_le (a := ‖z i‖) (b := ‖z j‖) (hw i) (hw j)
    have e4 := mul_le_mul_of_nonneg_left e3 (norm_nonneg (R i j))
    linarith
  have h2 : ∑ i, ∑ j, ‖R i j‖ * ((w i / w j * ‖z i‖ ^ 2 + w j / w i * ‖z j‖ ^ 2) / 2)
      = ∑ i, (w i * ∑ j, ‖R i j‖ / w j) * ‖z i‖ ^ 2 := by
    have s1 : ∀ i j, ‖R i j‖ * ((w i / w j * ‖z i‖ ^ 2 + w j / w i * ‖z j‖ ^ 2) / 2)
        = ‖R i j‖ * (w i / w j * ‖z i‖ ^ 2) / 2 + ‖R i j‖ * (w j / w i * ‖z j‖ ^ 2) / 2 := by
      intro i j
      ring
    simp_rw [s1, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => ‖R i j‖ * (w j / w i * ‖z j‖ ^ 2) / 2)]
    simp_rw [hR]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : ∑ i, (w i * ∑ j, ‖R i j‖ / w j) * ‖z i‖ ^ 2 ≤ ∑ i, r i * ‖z i‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hr i) (by positivity)
  have h4 : -∑ i, ∑ j, ‖R i j‖ * ((w i / w j * ‖z i‖ ^ 2 + w j / w i * ‖z j‖ ^ 2) / 2)
      ≤ ∑ i, ∑ j, (star (z i) * R i j * z j).re := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => h1 i j
  linarith

private lemma complexDiagonal_conjTranspose {n : Type*} [DecidableEq n] (P : Finset n)
    (δ : n → ℝ) : (complexDiagonal P δ)ᴴ = complexDiagonal P δ := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [complexDiagonal, pivotDiagonal, conjTranspose_apply]
  · simp [complexDiagonal, pivotDiagonal, conjTranspose_apply, diagonal_apply_ne _ h,
      diagonal_apply_ne _ (Ne.symm h)]

theorem complexSignedSlackBound : ComplexSignedSlackBound := by
  intro n p q _ _ _ _ M S pivot δ w r Fp Fm hM hS hw hr z
  set R := complexSlackRemainder M S pivot δ Fp Fm with hRdef
  have hRH : Rᴴ = R := by
    simp only [hRdef, complexSlackRemainder, conjTranspose_sub, conjTranspose_add,
      conjTranspose_mul, conjTranspose_conjTranspose, hM, hS, complexDiagonal_conjTranspose]
  have hRn : ∀ i j, ‖R j i‖ = ‖R i j‖ := by
    intro i j
    have := congrFun (congrFun hRH j) i
    rw [conjTranspose_apply] at this
    rw [← this, norm_star]
  have hMdec : M = S + complexDiagonal pivot δ + Fp * Fpᴴ - Fm * Fmᴴ + R := by
    simp only [hRdef, complexSlackRemainder]
    abel
  have hrem := remainder_lower R w r hRn hw hr z
  have hFp : 0 ≤ ∑ c, ‖∑ i, star (Fp i c) * z i‖ ^ 2 :=
    Finset.sum_nonneg fun c _ => by positivity
  have hsplit := Finset.sum_sdiff (f := fun j => r j * ‖z j‖ ^ 2) (Finset.subset_univ pivot)
  have hpiv : ∑ j ∈ pivot, (δ j - r j) * ‖z j‖ ^ 2
      = ∑ j ∈ pivot, δ j * ‖z j‖ ^ 2 - ∑ j ∈ pivot, r j * ‖z j‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hval : complexFormValue M z = complexFormValue S z + ∑ j ∈ pivot, δ j * ‖z j‖ ^ 2
      + ∑ c, ‖∑ i, star (Fp i c) * z i‖ ^ 2 - ∑ c, ‖∑ i, star (Fm i c) * z i‖ ^ 2
      + complexFormValue R z := by
    rw [hMdec, formValue_add, formValue_sub, formValue_add, formValue_add, formValue_diagonal,
      formValue_pairMatrix, formValue_pairMatrix]
  have hlhs : complexFormValue (S - complexDiagonal (Finset.univ \ pivot) r) z
      = complexFormValue S z - ∑ j ∈ Finset.univ \ pivot, r j * ‖z j‖ ^ 2 := by
    rw [formValue_sub, formValue_diagonal]
  rw [hval, hlhs]
  linarith

end Breakdown.CertCell.Certificate
