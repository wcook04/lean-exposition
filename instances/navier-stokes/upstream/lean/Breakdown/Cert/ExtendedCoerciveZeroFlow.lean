import Breakdown.Cert.ExtendedCoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

open PieceWeights

namespace Internal.ZeroFlow

theorem axialRot_zero' (φ : ℝ) : axialRot φ (0 : Space) = 0 := by
  ext i; fin_cases i <;> simp [axialRot, unitVector]

theorem modeVel_zero (β : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel β (fun _ _ => (0 : Space)) σ y = 0 := by
  funext i; simp [modeVel, modeAverage, axialRot_zero']

theorem gradField_zero : gradField (fun _ _ => (0 : Space)) = fun _ _ => 0 := by
  funext σ y; simp [gradField]

theorem secondDerivField_zero : secondDerivField (fun _ _ => (0 : Space)) = fun _ _ => 0 := by
  funext σ y; simp [secondDerivField]

theorem modeGrad_zero (β : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeGrad β (fun _ _ => (0 : Space →L[ℝ] Space)) σ y = 0 := by
  funext i; simp [modeGrad, modeAverage, axialRot_zero']

theorem modeSecondDeriv_zero (β : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeSecondDeriv β (fun _ _ => (0 : Space →L[ℝ] Space →L[ℝ] Space)) σ y = 0 := by
  funext i; simp [modeSecondDeriv, modeAverage, axialRot_zero']

theorem cnormSq_zero' {ι : Type*} [Fintype ι] : cnormSq (0 : ι → ℂ) = 0 := by
  simp [cnormSq]

theorem curlOfGrad_zero : curlOfGrad (0 : Fin 3 × Fin 3 → ℂ) = 0 := by
  funext i; simp [curlOfGrad]

theorem curlGradOfSecondDeriv_zero : curlGradOfSecondDeriv (0 : Fin 3 × Fin 3 × Fin 3 → ℂ) = 0 := by
  funext i; simp [curlGradOfSecondDeriv]

theorem curlVec_zero' : curlVec (0 : Space →L[ℝ] Space) = 0 := by
  simp [curlVec]

theorem speed_bound (a : ℝ) (φ : ℝ) (y : Space) :
    ‖(0 : Space) + (1 / 2 : ℝ) • axialRot φ y
      - a • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖
      ≤ (1 / 2 + |a|) * ‖y‖ := by
  have hR : ‖axialRot φ y‖ = ‖y‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_three]
    congr 1
    simp only [axialRot, unitVector, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
      smul_eq_mul, Real.norm_eq_abs, sq_abs]
    simp
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq φ
  have hJ : ‖-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1‖ ≤ ‖axialRot φ y‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    simp only [Fin.sum_univ_three, unitVector, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
      smul_eq_mul, Real.norm_eq_abs, sq_abs]
    simp
    nlinarith [sq_nonneg (axialRot φ y 2), sq_nonneg (axialRot φ y 0), sq_nonneg (axialRot φ y 1)]
  rw [zero_add]
  calc ‖(1 / 2 : ℝ) • axialRot φ y - a • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖
      ≤ ‖(1 / 2 : ℝ) • axialRot φ y‖ + ‖a • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖ :=
        norm_sub_le _ _
    _ = 1 / 2 * ‖axialRot φ y‖ + |a| * ‖-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ 1 / 2 * ‖y‖ + |a| * ‖y‖ := by
        rw [hR] at hJ ⊢
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hJ (abs_nonneg a))
    _ = (1 / 2 + |a|) * ‖y‖ := by ring

end Internal.ZeroFlow

open Internal.ZeroFlow in
theorem zeroFlowAdmissibleHolds_proof : ZeroFlowAdmissibleHolds := by
  intro C nE nM m P h w W HW w₀ epsSup epsGradSup ratio hm
  exact
  { finite_classes := hm.finite_classes
    c_pos := hm.c_pos
    c_lt_one := hm.c_lt_one
    cμ_pos := hm.cμ_pos
    cμ_lt_one := hm.cμ_lt_one
    period_pos := hm.period_pos
    weight_pos := hm.weight_pos
    weight_lower := hm.weight_lower
    weight_measurable := hm.weight_measurable
    weight_axi := hm.weight_axi
    harmonics_neg := hm.harmonics_neg
    harmonics_zero := hm.harmonics_zero
    harmonics_span := fun σ y i => by simp [modeVel_zero]
    ampW_ge := fun β hβ σ y => by
      rw [modeVel_zero, cnormSq_zero', Real.sqrt_zero]
      exact (Real.sqrt_nonneg _).trans (hm.ampW_ge β hβ σ y)
    ampGradW_ge := fun β hβ σ y => by
      rw [gradField_zero, modeGrad_zero, cnormSq_zero', Real.sqrt_zero]
      exact (Real.sqrt_nonneg _).trans (hm.ampGradW_ge β hβ σ y)
    ampVort_ge := fun β hβ σ y => by
      rw [gradField_zero, modeGrad_zero, curlOfGrad_zero, cnormSq_zero', Real.sqrt_zero]
      exact (Real.sqrt_nonneg _).trans (hm.ampVort_ge β hβ σ y)
    ampGradVort_ge := fun β hβ σ y => by
      rw [secondDerivField_zero, modeSecondDeriv_zero, curlGradOfSecondDeriv_zero, cnormSq_zero', Real.sqrt_zero]
      exact (Real.sqrt_nonneg _).trans (hm.ampGradVort_ge β hβ σ y)
    supVort_ge := fun σ φ y => by
      have e1 : ∀ x : Space, fderiv ℝ (fun _ : Space => (0 : Space)) x = 0 := fun x => by simp
      show ‖curlVec (fderiv ℝ (fun _ : Space => (0 : Space)) (axialRot φ y))‖ ≤ _
      rw [e1, curlVec_zero', norm_zero]
      exact (norm_nonneg _).trans (hm.supVort_ge σ φ y)
    supGradVort_ge := fun σ φ y => by
      have e1 : ∀ x : Space, fderiv ℝ (fun _ : Space => (0 : Space)) x = 0 := fun x => by simp
      show ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (fun _ : Space => (0 : Space)) x)) (axialRot φ y)‖ ≤ _
      simp only [e1, curlVec_zero', fderiv_const_apply, norm_zero]
      exact (norm_nonneg _).trans (hm.supGradVort_ge σ φ y)
    epsSpeed_ge := fun β σ φ y => speed_bound _ φ y
    muSpeed_ge := fun β σ φ y => speed_bound _ φ y
    eps_oneSided := hm.eps_oneSided
    mu_oneSided := hm.mu_oneSided
    mu_ratio := hm.mu_ratio
    ratio_nonneg := hm.ratio_nonneg
    eps_wt_nonneg := hm.eps_wt_nonneg
    mu_wt_nonneg := hm.mu_wt_nonneg
    eps_increment := hm.eps_increment
    mu_increment := hm.mu_increment
    eps_axi := hm.eps_axi
    mu_axi := hm.mu_axi
    eps_sum_le := hm.eps_sum_le
    eps_grad_sum_le := hm.eps_grad_sum_le
    eps_decay := hm.eps_decay
    mu_decay := hm.mu_decay
    eps_free_pos := hm.eps_free_pos
    mu_free_pos := hm.mu_free_pos
    mu_eta_pos := hm.mu_eta_pos
    eps_free_measurable := hm.eps_free_measurable
    mu_free_measurable := hm.mu_free_measurable
    eps_free_axi := hm.eps_free_axi
    mu_free_axi := hm.mu_free_axi
    convD_even := hm.convD_even
    convZ_even := hm.convZ_even
    convD_smooth := hm.convD_smooth
    convZ_smooth := hm.convZ_smooth
    convD_nonneg := hm.convD_nonneg
    convD_axi := hm.convD_axi
    convZ_axi := hm.convZ_axi
    convD_decay := hm.convD_decay
    convZ_decay := hm.convZ_decay
    conv_le := hm.conv_le }

end CoerciveWeak

end Breakdown
