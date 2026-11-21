import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.FarField

open Freq

private theorem heatKernel_continuous (τ : ℝ) : Continuous (heatKernel τ) := by
  unfold heatKernel
  fun_prop

private theorem heatKernel_nonneg {τ : ℝ} (hτ : 0 < τ) (x : Space) : 0 ≤ heatKernel τ x := by
  unfold heatKernel
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

private theorem heatKernel_rpow {τ : ℝ} (hτ : 0 < τ) (x : Space) :
    heatKernel τ x ^ (6 / 5 : ℝ) =
      ((4 * π * τ) ^ (-(3 / 2 : ℝ))) ^ (6 / 5 : ℝ) * Real.exp (-(3 / (10 * τ)) * ‖x‖ ^ 2) := by
  unfold heatKernel
  rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  field_simp
  ring

private theorem lintegral_heatKernel_rpow_lt_top {τ : ℝ} (hτ : 0 < τ) (y : Space) :
    ∫⁻ z, ‖heatKernel τ (y - z)‖ₑ ^ (6 / 5 : ℝ) < ∞ := by
  have hb : 0 < 3 / (10 * τ) := by positivity
  have h0 : Integrable (fun v : Space => Real.exp (-(3 / (10 * τ)) * ‖v‖ ^ 2)) := by
    apply Integrable.of_integral_ne_zero
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
    positivity
  have h1 := (h0.comp_sub_left y).const_mul (((4 * π * τ) ^ (-(3 / 2 : ℝ))) ^ (6 / 5 : ℝ))
  refine lt_of_eq_of_lt (lintegral_congr fun z => ?_) h1.2
  rw [Real.enorm_eq_ofReal (heatKernel_nonneg hτ _),
    ENNReal.ofReal_rpow_of_nonneg (heatKernel_nonneg hτ _) (by norm_num), heatKernel_rpow hτ,
    Real.enorm_eq_ofReal (by positivity)]

private theorem lintegral_heatKernel_smul_le {τ : ℝ} (y : Space) (g : Space → Space)
    (hg : AEMeasurable g) :
    ∫⁻ z, ‖heatKernel τ (y - z) • g z‖ₑ ≤
      (∫⁻ z, ‖heatKernel τ (y - z)‖ₑ ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ)) * eLpNorm g 6 volume := by
  have hpq : (6 / 5 : ℝ).HolderConjugate 6 := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hK : AEMeasurable (fun z => ‖heatKernel τ (y - z)‖ₑ) :=
    ((heatKernel_continuous τ).comp (continuous_const.sub continuous_id)).measurable.enorm.aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hK hg.enorm
  have h6 : (6 : ℝ≥0∞).toReal = 6 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h6]
  simp only [enorm_smul]
  exact h

private theorem integrable_heatKernel_smul {τ : ℝ} (hτ : 0 < τ) (y : Space) (u : L6R) :
    Integrable (fun z => heatKernel τ (y - z) • (u : Space → Space) z) := by
  refine ⟨((heatKernel_continuous τ).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable.smul (Lp.aestronglyMeasurable u), ?_⟩
  refine lt_of_le_of_lt
    (lintegral_heatKernel_smul_le y (u : Space → Space) (Lp.aestronglyMeasurable u).aemeasurable) ?_
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lintegral_heatKernel_rpow_lt_top hτ y).ne)
    (Lp.eLpNorm_lt_top u)

private theorem heatConv_sub_Lp {τ : ℝ} (hτ : 0 < τ) (y : Space) (u v : L6R) :
    heatConv τ (u : Space → Space) y - heatConv τ (v : Space → Space) y =
      heatConv τ ((u - v : L6R) : Space → Space) y := by
  unfold heatConv
  rw [← integral_sub (integrable_heatKernel_smul hτ y u) (integrable_heatKernel_smul hτ y v)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v] with z hz
  rw [hz, Pi.sub_apply, smul_sub]

private theorem norm_heatConv_sub_le {τ : ℝ} (hτ : 0 < τ) (y : Space) :
    ∃ K : ℝ, ∀ u v : L6R,
      ‖heatConv τ (u : Space → Space) y - heatConv τ (v : Space → Space) y‖ ≤ K * ‖u - v‖ := by
  set A := (∫⁻ z, ‖heatKernel τ (y - z)‖ₑ ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ)) with hA
  have hAt : A ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lintegral_heatKernel_rpow_lt_top hτ y).ne).ne
  refine ⟨A.toReal, fun u v => ?_⟩
  rw [heatConv_sub_Lp hτ y u v]
  unfold heatConv
  have h1 := (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_heatKernel_smul_le (τ := τ) y _ (Lp.aestronglyMeasurable (u - v)).aemeasurable)
  rw [← Lp.enorm_def] at h1
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top hAt enorm_ne_top) h1
  rwa [toReal_enorm, ENNReal.toReal_mul, toReal_enorm] at h2

private theorem tendsto_heatConv_of_tendsto {τ : ℝ} (hτ : 0 < τ) (y : Space) {w : ℕ → L6R}
    {w₀ : L6R} (hw : Tendsto w atTop (𝓝 w₀)) :
    Tendsto (fun n => heatConv τ (w n : Space → Space) y) atTop
      (𝓝 (heatConv τ (w₀ : Space → Space) y)) := by
  obtain ⟨K, hK⟩ := norm_heatConv_sub_le hτ y
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun n => K * ‖w n - w₀‖) atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hw).const_mul K
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => hK (w n) w₀) h0

private theorem heatVelocity_on_testSpan (hT : HeatConvTest) {τ : ℝ} (hτ : 0 < τ) (z : X)
    (hz : z ∈ testSpan) :
    (velocity (heatX τ z) : Space → Space) =ᵐ[volume]
      heatConv τ (velocity z : Space → Space) := by
  obtain ⟨φ, hφ, rfl⟩ := testSpan_holds z hz
  obtain ⟨hd, he⟩ := hT φ hφ τ hτ
  have h2 : heatConv τ (velocity (embedX φ) : Space → Space) = heatConv τ φ := by
    funext y
    unfold heatConv
    apply integral_congr_ae
    filter_upwards [Internal.BilinTestFormula.velocity_test velocity_holds hφ] with w hw
    rw [hw]
  rw [he, h2]
  exact velocityDecay_holds _ hd

theorem heatVelocity_of_heatConvTest : HeatKernelBounds → HeatConvTest → HeatVelocity := by
  intro _ hT τ hτ x
  obtain ⟨a, ha, hax⟩ := mem_closure_iff_seq_limit.1 (testDense_holds.2 x)
  have hL : Tendsto (fun n => velocity (heatX τ (a n))) atTop (𝓝 (velocity (heatX τ x))) :=
    ((velocity.continuous.comp (heatX τ).continuous).tendsto x).comp hax
  have hR : Tendsto (fun n => velocity (a n)) atTop (𝓝 (velocity x)) :=
    (velocity.continuous.tendsto x).comp hax
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂volume, ∀ n, (velocity (heatX τ (a n)) : Space → Space) y =
      heatConv τ (velocity (a n) : Space → Space) y :=
    ae_all_iff.2 fun n => heatVelocity_on_testSpan hT hτ (a n) (ha n)
  filter_upwards [hae, hall] with y hy1 hy2
  have hy3 := tendsto_heatConv_of_tendsto hτ y (hR.comp hns.tendsto_atTop)
  exact tendsto_nhds_unique hy1 (hy3.congr fun k => (hy2 (ns k)).symm)

end Breakdown.FarField
