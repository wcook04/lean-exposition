import Breakdown.CertTorus.DecayStatements
import Breakdown.Uniqueness.FundSolPotential
import Breakdown.Uniqueness.FundSolPointwiseAux2
import Breakdown.Uniqueness.FundSolEnergyAux

open MeasureTheory Set Real Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

open Breakdown.FundSol Breakdown.FundSol.Internal

private theorem ballCutoff_contDiff (ρ : ℝ) : ContDiff ℝ ∞ (ballCutoff ρ) := by
  unfold ballCutoff
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))

private theorem ballCutoff_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {z : Space} (hz : 2 * ρ < ‖z‖) :
    ballCutoff ρ z = 0 := by
  unfold ballCutoff
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : 4 * ρ ^ 2 < ‖z‖ ^ 2 := by nlinarith
  have h2 : 2 ≤ ‖z‖ ^ 2 / ρ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

private theorem ballCutoff_eq_one {ρ : ℝ} (hρ : 0 < ρ) {z : Space} (hz : ‖z‖ ≤ ρ) :
    ballCutoff ρ z = 1 := by
  unfold ballCutoff
  apply Real.smoothTransition.one_of_one_le
  have h1 : ‖z‖ ^ 2 ≤ ρ ^ 2 := by
    have := norm_nonneg z
    nlinarith
  have h2 : ‖z‖ ^ 2 / ρ ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact h1
  linarith

private theorem abs_ballCutoff_le (ρ : ℝ) (z : Space) : |ballCutoff ρ z| ≤ 1 := by
  unfold ballCutoff
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

private theorem hasCompactSupport_cutoff_mul {ρ : ℝ} (hρ : 0 < ρ) (g : Space → ℝ) :
    HasCompactSupport (fun z => ballCutoff ρ z * g z) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * ρ)) fun z hz => by
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    rw [ballCutoff_eq_zero hρ hz, zero_mul]

private def smoothKernel (δ : ℝ) (w : Space) : ℝ := -(4 * π)⁻¹ * (Real.sqrt (‖w‖ ^ 2 + δ))⁻¹

private theorem smoothKernel_contDiff {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (smoothKernel δ) := by
  have hpos : ∀ w : Space, 0 < ‖w‖ ^ 2 + δ := fun w => by positivity
  unfold smoothKernel
  exact contDiff_const.mul ((((contDiff_norm_sq ℝ).add contDiff_const).sqrt
    fun w => (hpos w).ne').inv fun w => (Real.sqrt_pos.2 (hpos w)).ne')

private theorem hasFDerivAt_smoothKernel {δ : ℝ} (hδ : 0 < δ) (w : Space) :
    HasFDerivAt (smoothKernel δ)
      (((4 * π)⁻¹ * (Real.sqrt (‖w‖ ^ 2 + δ))⁻¹ ^ 3) • innerSL ℝ w) w := by
  have hpos : 0 < ‖w‖ ^ 2 + δ := by positivity
  have hs : 0 < Real.sqrt (‖w‖ ^ 2 + δ) := Real.sqrt_pos.2 hpos
  have hss : Real.sqrt (‖w‖ ^ 2 + δ) ^ 2 = ‖w‖ ^ 2 + δ := Real.sq_sqrt hpos.le
  have h1 : HasFDerivAt (fun x : Space => ‖x‖ ^ 2 + δ) (2 • innerSL ℝ w) w :=
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt.add_const δ
  have h2 := (hasDerivAt_inv hs.ne').comp_hasFDerivAt w (h1.sqrt hpos.ne')
  have h3 := h2.const_mul (-(4 * π)⁻¹)
  refine h3.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  field_simp

private theorem abs_smoothKernel_le {δ : ℝ} (hδ : 0 < δ) {w : Space} (hw : w ≠ 0) :
    |smoothKernel δ w| ≤ |kernel w| := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hle : ‖w‖ ≤ Real.sqrt (‖w‖ ^ 2 + δ) := by
    have h := Real.sqrt_le_sqrt (show ‖w‖ ^ 2 ≤ ‖w‖ ^ 2 + δ by linarith)
    rwa [Real.sqrt_sq (norm_nonneg w)] at h
  rw [abs_kernel]
  unfold smoothKernel
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (4 * π)⁻¹),
    abs_of_pos (inv_pos.2 (hn.trans_le hle))]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hn hle) (by positivity)

private theorem tendsto_smoothKernel {w : Space} (hw : w ≠ 0) :
    Tendsto (fun δ => smoothKernel δ w) (𝓝[>] 0) (𝓝 (kernel w)) := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hc : ContinuousAt (fun δ : ℝ => -(4 * π)⁻¹ * (Real.sqrt (‖w‖ ^ 2 + δ))⁻¹) 0 :=
    continuousAt_const.mul ((Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.add continuousAt_id)).inv₀
        (by simp [Real.sqrt_sq (norm_nonneg w), hn]))
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [add_zero, Real.sqrt_sq (norm_nonneg w)] at h
  exact h

private theorem tendsto_smoothGrad (v : Space) {w : Space} (hw : w ≠ 0) :
    Tendsto (fun δ => (4 * π)⁻¹ * (Real.sqrt (‖w‖ ^ 2 + δ))⁻¹ ^ 3 * inner ℝ w v) (𝓝[>] 0)
      (𝓝 ((4 * π)⁻¹ * ‖w‖⁻¹ ^ 3 * inner ℝ w v)) := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hc : ContinuousAt
      (fun δ : ℝ => (4 * π)⁻¹ * (Real.sqrt (‖w‖ ^ 2 + δ))⁻¹ ^ 3 * inner ℝ w v) 0 :=
    (continuousAt_const.mul (((Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.add continuousAt_id)).inv₀
        (by simp [Real.sqrt_sq (norm_nonneg w), hn])).pow 3)).mul continuousAt_const
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [add_zero, Real.sqrt_sq (norm_nonneg w)] at h
  exact h

private theorem abs_smoothGrad_le {δ : ℝ} (hδ : 0 < δ) (v w : Space) :
    |(4 * π)⁻¹ * (Real.sqrt (‖w‖ ^ 2 + δ))⁻¹ ^ 3 * inner ℝ w v| ≤
      (4 * π)⁻¹ * ‖w‖⁻¹ ^ 2 * ‖v‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hle : ‖w‖ ≤ Real.sqrt (‖w‖ ^ 2 + δ) := by
    have h := Real.sqrt_le_sqrt (show ‖w‖ ^ 2 ≤ ‖w‖ ^ 2 + δ by linarith)
    rwa [Real.sqrt_sq (norm_nonneg w)] at h
  have hi : (Real.sqrt (‖w‖ ^ 2 + δ))⁻¹ ≤ ‖w‖⁻¹ := inv_anti₀ hn hle
  have hin : |inner ℝ w v| ≤ ‖w‖ * ‖v‖ := abs_real_inner_le_norm w v
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (4 * π)⁻¹),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt (‖w‖ ^ 2 + δ))⁻¹ ^ 3)]
  calc (4 * π)⁻¹ * (Real.sqrt (‖w‖ ^ 2 + δ))⁻¹ ^ 3 * |inner ℝ w v|
      ≤ (4 * π)⁻¹ * ‖w‖⁻¹ ^ 3 * (‖w‖ * ‖v‖) := by
        gcongr
    _ = (4 * π)⁻¹ * ‖w‖⁻¹ ^ 2 * ‖v‖ := by
        rw [← inv_pow_three_mul ‖w‖]
        ring

private theorem abs_gradKernel_le (v w : Space) :
    |(4 * π)⁻¹ * ‖w‖⁻¹ ^ 3 * inner ℝ w v| ≤ (4 * π)⁻¹ * ‖w‖⁻¹ ^ 2 * ‖v‖ := by
  have hin : |inner ℝ w v| ≤ ‖w‖ * ‖v‖ := abs_real_inner_le_norm w v
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * π)⁻¹ * ‖w‖⁻¹ ^ 3)]
  calc (4 * π)⁻¹ * ‖w‖⁻¹ ^ 3 * |inner ℝ w v| ≤ (4 * π)⁻¹ * ‖w‖⁻¹ ^ 3 * (‖w‖ * ‖v‖) := by
        gcongr
    _ = (4 * π)⁻¹ * ‖w‖⁻¹ ^ 2 * ‖v‖ := by
        rw [← inv_pow_three_mul ‖w‖]
        ring

private theorem hasCompactSupport_fderiv_dir {h : Space → ℝ} (hc : HasCompactSupport h) (v : Space) :
    HasCompactSupport (fun t => fderiv ℝ h t v) :=
  (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L v)
    (ContinuousLinearMap.zero_apply v)

private theorem continuous_fderiv_dir {h : Space → ℝ} (hh : ContDiff ℝ ∞ h) (v : Space) :
    Continuous (fun t => fderiv ℝ h t v) :=
  (hh.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem continuous_smoothGrad {δ : ℝ} (hδ : 0 < δ) (x v : Space) :
    Continuous (fun t : Space =>
      (4 * π)⁻¹ * (Real.sqrt (‖x - t‖ ^ 2 + δ))⁻¹ ^ 3 * inner ℝ (x - t) v) := by
  have hcs : Continuous (fun t : Space => (Real.sqrt (‖x - t‖ ^ 2 + δ))⁻¹) :=
    (Real.continuous_sqrt.comp (((continuous_const.sub continuous_id).norm.pow 2).add
      continuous_const)).inv₀ fun t => (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ)).ne'
  exact (continuous_const.mul (hcs.pow 3)).mul
    ((continuous_const.sub continuous_id).inner continuous_const)

private theorem integral_deriv_mul_smoothKernel {h : Space → ℝ} (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {δ : ℝ} (hδ : 0 < δ) (x v : Space) :
    ∫ t, fderiv ℝ h t v * smoothKernel δ (x - t) =
      ∫ t, h t * ((4 * π)⁻¹ * (Real.sqrt (‖x - t‖ ^ 2 + δ))⁻¹ ^ 3 * inner ℝ (x - t) v) := by
  have hkd : ContDiff ℝ ∞ (fun t => smoothKernel δ (x - t)) :=
    (smoothKernel_contDiff hδ).comp (contDiff_const.sub contDiff_id)
  have hkf : ∀ t, fderiv ℝ (fun t => smoothKernel δ (x - t)) t v =
      -((4 * π)⁻¹ * (Real.sqrt (‖x - t‖ ^ 2 + δ))⁻¹ ^ 3 * inner ℝ (x - t) v) := by
    intro t
    have h1 : HasFDerivAt (fun t => smoothKernel δ (x - t)) _ t :=
      (hasFDerivAt_smoothKernel hδ (x - t)).comp t ((hasFDerivAt_id t).const_sub x)
    rw [h1.fderiv]
    simp [inner_sub_left]
  have hdk : Continuous (fun t => fderiv ℝ (fun t => smoothKernel δ (x - t)) t v) :=
    continuous_fderiv_dir hkd v
  have i1 : Integrable (fun t => fderiv ℝ h t v * smoothKernel δ (x - t)) :=
    ((continuous_fderiv_dir hh v).mul hkd.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_dir hc v).mul_right
  have i2 : Integrable (fun t => h t * fderiv ℝ (fun t => smoothKernel δ (x - t)) t v) :=
    (hh.continuous.mul hdk).integrable_of_hasCompactSupport hc.mul_right
  have i3 : Integrable (fun t => h t * smoothKernel δ (x - t)) :=
    (hh.continuous.mul hkd.continuous).integrable_of_hasCompactSupport hc.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (g := fun t => smoothKernel δ (x - t)) i1 i2 i3
    (fun t _ => hh.differentiable (by simp) t) (fun t _ => hkd.differentiable (by simp) t)
  simp only [hkf, mul_neg, integral_neg, neg_inj] at hibp
  exact hibp.symm

private theorem fderiv_potential_eq_integral {h : Space → ℝ} (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (x v : Space) :
    fderiv ℝ (potential h) x v =
      ∫ t, h t * ((4 * π)⁻¹ * ‖x - t‖⁻¹ ^ 3 * inner ℝ (x - t) v) := by
  have hdh := continuous_fderiv_dir hh v
  have hcd := hasCompactSupport_fderiv_dir hc v
  have hae : ∀ᵐ t ∂(volume : Measure Space), t ≠ x :=
    compl_mem_ae_iff.2 (measure_singleton x)
  have hL : Tendsto (fun δ => ∫ t, fderiv ℝ h t v * smoothKernel δ (x - t)) (𝓝[>] 0)
      (𝓝 (∫ t, fderiv ℝ h t v * kernel (x - t))) := by
    have hex : Integrable (fun t => fderiv ℝ h t v * kernel (x - t)) := by
      have := hcd.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hdh
        locallyIntegrable_kernel x
      simpa [ConvolutionExistsAt, smul_eq_mul] using this
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => ‖fderiv ℝ h t v * kernel (x - t)‖) ?_ ?_ hex.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (hdh.mul ((smoothKernel_contDiff hδ).continuous.comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      filter_upwards [hae] with t ht
      have hxt : x - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
      rw [norm_mul, norm_mul, Real.norm_eq_abs (smoothKernel δ (x - t)),
        Real.norm_eq_abs (kernel (x - t))]
      exact mul_le_mul_of_nonneg_left (abs_smoothKernel_le hδ hxt) (norm_nonneg _)
    · filter_upwards [hae] with t ht
      exact (tendsto_smoothKernel (sub_ne_zero.2 (Ne.symm ht))).const_mul _
  have hR : Tendsto (fun δ => ∫ t, h t *
        ((4 * π)⁻¹ * (Real.sqrt (‖x - t‖ ^ 2 + δ))⁻¹ ^ 3 * inner ℝ (x - t) v)) (𝓝[>] 0)
      (𝓝 (∫ t, h t * ((4 * π)⁻¹ * ‖x - t‖⁻¹ ^ 3 * inner ℝ (x - t) v))) := by
    have hex : Integrable (fun t => h t • kernelGrad (x - t)) := by
      have := hc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hh.continuous
        locallyIntegrable_kernelGrad x
      simpa [ConvolutionExistsAt] using this
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => ‖h t • kernelGrad (x - t)‖ * ‖v‖) ?_ ?_ (hex.norm.mul_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (hh.continuous.mul (continuous_smoothGrad hδ x v)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      refine Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_mul]
      calc |h t| * |(4 * π)⁻¹ * (Real.sqrt (‖x - t‖ ^ 2 + δ))⁻¹ ^ 3 * inner ℝ (x - t) v|
          ≤ |h t| * ((4 * π)⁻¹ * ‖x - t‖⁻¹ ^ 2 * ‖v‖) :=
            mul_le_mul_of_nonneg_left (abs_smoothGrad_le hδ v (x - t)) (abs_nonneg _)
        _ = ‖h t • kernelGrad (x - t)‖ * ‖v‖ := by
            rw [norm_smul, norm_kernelGrad, Real.norm_eq_abs]
            ring
    · filter_upwards [hae] with t ht
      exact (tendsto_smoothGrad v (sub_ne_zero.2 (Ne.symm ht))).const_mul _
  have hR' : Tendsto (fun δ => ∫ t, fderiv ℝ h t v * smoothKernel δ (x - t)) (𝓝[>] 0)
      (𝓝 (∫ t, h t * ((4 * π)⁻¹ * ‖x - t‖⁻¹ ^ 3 * inner ℝ (x - t) v))) := by
    refine hR.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (integral_deriv_mul_smoothKernel hh hc hδ x v).symm
  rw [fderiv_potential hh hc, potential_apply]
  exact tendsto_nhds_unique hL hR'

private theorem weight_pointwise (y t : Space) :
    ‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4 ≤
      (4 / 3) ^ 4 * (1 + ‖y‖)⁻¹ ^ 4 * ballPow 2 ((1 + ‖y‖) / 4) (y - t) +
        16 * (1 + ‖y‖)⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4 := by
  have hy0 := norm_nonneg y
  have ht0 : 0 < 1 + ‖t‖ := by positivity
  have hapos : 0 < 1 + ‖y‖ := by positivity
  by_cases hlt : ‖y - t‖ < (1 + ‖y‖) / 4
  · rw [ballPow_of_lt hlt]
    have htri := norm_add_le (y - t) t
    rw [sub_add_cancel] at htri
    have h1 : 3 * (1 + ‖y‖) / 4 ≤ 1 + ‖t‖ := by linarith
    have h2 : (1 + ‖t‖)⁻¹ ≤ 4 / 3 * (1 + ‖y‖)⁻¹ := by
      calc (1 + ‖t‖)⁻¹ ≤ (3 * (1 + ‖y‖) / 4)⁻¹ := inv_anti₀ (by positivity) h1
        _ = 4 / 3 * (1 + ‖y‖)⁻¹ := by field_simp
    have h3 : (1 + ‖t‖)⁻¹ ^ 4 ≤ (4 / 3) ^ 4 * (1 + ‖y‖)⁻¹ ^ 4 := by
      calc (1 + ‖t‖)⁻¹ ^ 4 ≤ (4 / 3 * (1 + ‖y‖)⁻¹) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4
        _ = (4 / 3) ^ 4 * (1 + ‖y‖)⁻¹ ^ 4 := by ring
    calc ‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4
        ≤ ‖y - t‖⁻¹ ^ 2 * ((4 / 3) ^ 4 * (1 + ‖y‖)⁻¹ ^ 4) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (4 / 3) ^ 4 * (1 + ‖y‖)⁻¹ ^ 4 * ‖y - t‖⁻¹ ^ 2 := by ring
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · rw [ballPow_of_le (not_lt.1 hlt)]
    have hr : 0 < (1 + ‖y‖) / 4 := by positivity
    have h1 : ‖y - t‖⁻¹ ≤ 4 * (1 + ‖y‖)⁻¹ := by
      calc ‖y - t‖⁻¹ ≤ ((1 + ‖y‖) / 4)⁻¹ := inv_anti₀ hr (not_lt.1 hlt)
        _ = 4 * (1 + ‖y‖)⁻¹ := by field_simp
    have h2 : ‖y - t‖⁻¹ ^ 2 ≤ 16 * (1 + ‖y‖)⁻¹ ^ 2 := by
      calc ‖y - t‖⁻¹ ^ 2 ≤ (4 * (1 + ‖y‖)⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = 16 * (1 + ‖y‖)⁻¹ ^ 2 := by ring
    calc ‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4 ≤ 16 * (1 + ‖y‖)⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by ring

private theorem integrable_decay_four : Integrable (fun t : Space => (1 + ‖t‖)⁻¹ ^ 4) :=
  integrable_of_abs_le_decay (C := 1) (m := 4)
    (((continuous_const.add continuous_norm).inv₀
      fun t => (add_pos_of_pos_of_nonneg one_pos (norm_nonneg t)).ne').pow 4) le_rfl
    fun t => by rw [one_mul, abs_of_nonneg (by positivity)]

private theorem integrable_ballPart (y : Space) :
    Integrable (fun t : Space =>
      (4 / 3) ^ 4 * (1 + ‖y‖)⁻¹ ^ 4 * ballPow 2 ((1 + ‖y‖) / 4) (y - t)) :=
  ((integrable_ballPow (n := 2) (by norm_num) ((1 + ‖y‖) / 4)).comp_sub_left y).const_mul _

private theorem integrable_weight (y : Space) :
    Integrable (fun t : Space => ‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4) := by
  have hm : Measurable (fun t : Space => ‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4) := by fun_prop
  refine ((integrable_ballPart y).add (integrable_decay_four.const_mul
    (16 * (1 + ‖y‖)⁻¹ ^ 2))).mono' hm.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact weight_pointwise y t

private theorem integral_weight_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Space,
    ∫ t, ‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4 ≤ K * (1 + ‖y‖)⁻¹ ^ 2 := by
  have hV : 0 ≤ volume.real (ball (0 : Space) 1) := measureReal_nonneg
  have hI : 0 ≤ ∫ t : Space, (1 + ‖t‖)⁻¹ ^ 4 := integral_nonneg fun t => by positivity
  refine ⟨(4 / 3) ^ 4 * (3 * volume.real (ball (0 : Space) 1) / 4) +
    16 * ∫ t : Space, (1 + ‖t‖)⁻¹ ^ 4, by positivity, fun y => ?_⟩
  have hy0 := norm_nonneg y
  have hapos : 0 < 1 + ‖y‖ := by positivity
  have hinv : (1 + ‖y‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hinv0 : 0 ≤ (1 + ‖y‖)⁻¹ := by positivity
  have hua : (1 + ‖y‖)⁻¹ * (1 + ‖y‖) = 1 := inv_mul_cancel₀ hapos.ne'
  have hu3 : (1 + ‖y‖)⁻¹ ^ 3 ≤ (1 + ‖y‖)⁻¹ ^ 2 := pow_le_pow_of_le_one hinv0 hinv (by norm_num)
  have hb := integrable_ballPart y
  have hd := integrable_decay_four.const_mul (16 * (1 + ‖y‖)⁻¹ ^ 2)
  calc ∫ t, ‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4
      ≤ ∫ t, ((4 / 3) ^ 4 * (1 + ‖y‖)⁻¹ ^ 4 * ballPow 2 ((1 + ‖y‖) / 4) (y - t) +
          16 * (1 + ‖y‖)⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4) :=
        integral_mono (integrable_weight y) (hb.add hd) fun t => weight_pointwise y t
    _ = (4 / 3) ^ 4 * (1 + ‖y‖)⁻¹ ^ 4 *
          (3 * volume.real (ball (0 : Space) 1) * ((1 + ‖y‖) / 4)) +
          16 * (1 + ‖y‖)⁻¹ ^ 2 * ∫ t : Space, (1 + ‖t‖)⁻¹ ^ 4 := by
        rw [integral_add hb hd, integral_const_mul, integral_const_mul,
          integral_sub_left_eq_self (ballPow 2 ((1 + ‖y‖) / 4)) volume y,
          integral_ballPow_two (by positivity)]
    _ = (4 / 3) ^ 4 * (3 * volume.real (ball (0 : Space) 1) / 4) * (1 + ‖y‖)⁻¹ ^ 3 *
          ((1 + ‖y‖)⁻¹ * (1 + ‖y‖)) +
          16 * (1 + ‖y‖)⁻¹ ^ 2 * ∫ t : Space, (1 + ‖t‖)⁻¹ ^ 4 := by ring
    _ ≤ _ := by
        rw [hua, mul_one]
        have h := mul_le_mul_of_nonneg_left hu3
          (by positivity : (0 : ℝ) ≤ (4 / 3) ^ 4 * (3 * volume.real (ball (0 : Space) 1) / 4))
        nlinarith

private theorem integrand_bound {A : ℝ} {g c : Space → ℝ} (hA : ∀ z, |g z| ≤ A / (1 + ‖z‖) ^ 4)
    (hc : ∀ z, |c z| ≤ 1) (y v t : Space) :
    |c t * g t * ((4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3 * inner ℝ (y - t) v)| ≤
      A * (4 * π)⁻¹ * ‖v‖ * (‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4) := by
  have hg : |g t| ≤ A * (1 + ‖t‖)⁻¹ ^ 4 := by
    rw [inv_pow, ← div_eq_mul_inv]
    exact hA t
  have hcg : |c t * g t| ≤ A * (1 + ‖t‖)⁻¹ ^ 4 := by
    rw [abs_mul]
    calc |c t| * |g t| ≤ 1 * |g t| := mul_le_mul_of_nonneg_right (hc t) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hg
  rw [abs_mul]
  calc |c t * g t| * |(4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3 * inner ℝ (y - t) v|
      ≤ (A * (1 + ‖t‖)⁻¹ ^ 4) * ((4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 2 * ‖v‖) :=
        mul_le_mul hcg (abs_gradKernel_le v (y - t)) (abs_nonneg _) ((abs_nonneg _).trans hcg)
    _ = _ := by ring

theorem truncatedNewton_holds : TruncatedNewton := by
  intro g A hg hA
  have hA0 : 0 ≤ A := by
    have := (abs_nonneg (g 0)).trans (hA 0)
    simpa using this
  obtain ⟨K, hK0, hK⟩ := integral_weight_le
  have hgm : Measurable g := hg.continuous.measurable
  have hform : ∀ ρ : ℝ, 0 < ρ → ∀ y v : Space,
      fderiv ℝ (potential (fun z => ballCutoff ρ z * g z)) y v =
        ∫ t, ballCutoff ρ t * g t * ((4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3 * inner ℝ (y - t) v) :=
    fun ρ hρ y v => fderiv_potential_eq_integral ((ballCutoff_contDiff ρ).mul hg)
      (hasCompactSupport_cutoff_mul hρ g) y v
  have hmeas : ∀ c : Space → ℝ, Continuous c → ∀ y v : Space,
      AEStronglyMeasurable
        (fun t => c t * g t * ((4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3 * inner ℝ (y - t) v)) volume := by
    intro c hc y v
    have h1 : Measurable (fun t : Space => (4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3) := by fun_prop
    have h2 : Measurable (fun t : Space => inner ℝ (y - t) v) :=
      ((continuous_const.sub continuous_id).inner continuous_const).measurable
    exact ((hc.measurable.mul hgm).mul (h1.mul h2)).aestronglyMeasurable
  refine ⟨⟨A * (4 * π)⁻¹ * K, fun ρ hρ y => ?_⟩, fun i y => ?_⟩
  · have hM : 0 ≤ A * (4 * π)⁻¹ * K / (1 + ‖y‖) ^ 2 := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun v => ?_
    rw [Real.norm_eq_abs, hform ρ (by linarith) y v]
    calc |∫ t, ballCutoff ρ t * g t * ((4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3 * inner ℝ (y - t) v)|
        ≤ ∫ t, A * (4 * π)⁻¹ * ‖v‖ * (‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4) := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le ((integrable_weight y).const_mul _)
            (Eventually.of_forall fun t => ?_)
          rw [Real.norm_eq_abs]
          exact integrand_bound hA (abs_ballCutoff_le ρ) y v t
      _ = A * (4 * π)⁻¹ * ‖v‖ * ∫ t, ‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4 := integral_const_mul _ _
      _ ≤ A * (4 * π)⁻¹ * ‖v‖ * (K * (1 + ‖y‖)⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left (hK y) (by positivity)
      _ = A * (4 * π)⁻¹ * K / (1 + ‖y‖) ^ 2 * ‖v‖ := by
          rw [inv_pow]
          ring
  · have hT : Tendsto (fun ρ => ∫ t, ballCutoff ρ t * g t *
          ((4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3 * inner ℝ (y - t) (unitVector i))) atTop
        (𝓝 (∫ t, g t * ((4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3 * inner ℝ (y - t) (unitVector i)))) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun t => A * (4 * π)⁻¹ * ‖unitVector i‖ * (‖y - t‖⁻¹ ^ 2 * (1 + ‖t‖)⁻¹ ^ 4))
        (Eventually.of_forall fun ρ => hmeas _ (ballCutoff_contDiff ρ).continuous y _)
        (Eventually.of_forall fun ρ => Eventually.of_forall fun t => ?_)
        ((integrable_weight y).const_mul _) (Eventually.of_forall fun t => ?_)
      · rw [Real.norm_eq_abs]
        exact integrand_bound hA (abs_ballCutoff_le ρ) y _ t
      · have hev : (fun _ : ℝ =>
            g t * ((4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3 * inner ℝ (y - t) (unitVector i))) =ᶠ[atTop]
            fun ρ => ballCutoff ρ t * g t *
              ((4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3 * inner ℝ (y - t) (unitVector i)) := by
          filter_upwards [eventually_ge_atTop (max ‖t‖ 1)] with ρ hρ
          rw [ballCutoff_eq_one (by linarith [le_max_right ‖t‖ 1])
            ((le_max_left _ _).trans hρ), one_mul]
        exact tendsto_const_nhds.congr' hev
    have hN : ∫ t, g t * ((4 * π)⁻¹ * ‖y - t‖⁻¹ ^ 3 * inner ℝ (y - t) (unitVector i)) =
        newtonGradientComp g i y := by
      unfold newtonGradientComp
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [kernelGrad, unitVector, PiLp.smul_apply, smul_eq_mul,
        EuclideanSpace.inner_single_right, one_mul, conj_trivial]
      ring
    rw [← hN]
    refine hT.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with ρ hρ
    exact (hform ρ (by linarith) y _).symm

end Breakdown.FarField
