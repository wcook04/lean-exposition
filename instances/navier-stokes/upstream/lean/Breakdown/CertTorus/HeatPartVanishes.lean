import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FarField

private lemma heatKernel_eq_gaussian (τ : ℝ) (x : Space) :
    heatKernel τ x = (4 * π * τ) ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 * τ)⁻¹ * ‖x‖ ^ 2) := by
  unfold heatKernel
  rw [show -(‖x‖ ^ 2) / (4 * τ) = -(4 * τ)⁻¹ * ‖x‖ ^ 2 by ring]

private lemma heatKernel_nonneg_of_pos {τ : ℝ} (hτ : 0 < τ) (x : Space) : 0 ≤ heatKernel τ x := by
  unfold heatKernel
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

private lemma integral_gaussian_space {τ : ℝ} (hτ : 0 < τ) :
    ∫ x : Space, Real.exp (-(4 * τ)⁻¹ * ‖x‖ ^ 2) = (4 * π * τ) ^ (3 / 2 : ℝ) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity), finrank_euclideanSpace_fin,
    div_inv_eq_mul]
  norm_num
  ring_nf

private lemma integral_heatKernel_eq_one {τ : ℝ} (hτ : 0 < τ) : ∫ x : Space, heatKernel τ x = 1 := by
  simp_rw [heatKernel_eq_gaussian τ]
  rw [integral_const_mul, integral_gaussian_space hτ, Real.rpow_neg (by positivity),
    inv_mul_cancel₀ (by positivity)]

private lemma integrable_heatKernel {τ : ℝ} (hτ : 0 < τ) : Integrable (heatKernel τ) := by
  by_contra h
  have h0 := integral_undef h
  rw [integral_heatKernel_eq_one hτ] at h0
  exact one_ne_zero h0

private lemma norm_heatConv_le {τ : ℝ} (hτ : 0 < τ) (f : Space → Space) (C : ℝ)
    (hf : ∀ z, ‖f z‖ ≤ C) (y : Space) : ‖heatConv τ f y‖ ≤ C := by
  have hint : Integrable (fun z => heatKernel τ (y - z) * C) :=
    ((integrable_heatKernel hτ).comp_sub_left y).mul_const C
  have hval : ∫ z, heatKernel τ (y - z) * C = C := by
    rw [integral_mul_const, integral_sub_left_eq_self (fun z => heatKernel τ z) volume y,
      integral_heatKernel_eq_one hτ, one_mul]
  unfold heatConv
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun z => ?_)).trans hval.le
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg_of_pos hτ _)]
  exact mul_le_mul_of_nonneg_left (hf z) (heatKernel_nonneg_of_pos hτ _)

theorem heatPartVanishes_of_heat : HeatKernelBounds → HeatPartVanishes := by
  intro _ W _ C hC s y
  have hbound : ∀ T : ℝ, 0 < T → ‖similarityHeatPart W s T y‖ ≤ (Real.sqrt (1 + T))⁻¹ * C := by
    intro T hT
    unfold similarityHeatPart
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    exact mul_le_mul_of_nonneg_left (norm_heatConv_le hT _ C (fun z => hC _ _) y)
      (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hsqrt : Tendsto (fun T : ℝ => Real.sqrt (1 + T)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have hlim : Tendsto (fun T : ℝ => (Real.sqrt (1 + T))⁻¹ * C) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hsqrt).mul_const C
  exact squeeze_zero_norm' ((eventually_gt_atTop 0).mono hbound) hlim

end Breakdown.FarField
