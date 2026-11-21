import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Breakdown.FarField

private def inverseSquareTrunc (ρ : ℝ) (t : ℝ) : ℝ :=
  (Iio ρ).indicator (fun s : ℝ => s⁻¹ ^ 2) t

private theorem finrank_space_eq_three : Module.finrank ℝ Space = 3 :=
  finrank_euclideanSpace_fin

private theorem radial_inverseSquareTrunc (ρ : ℝ) :
    EqOn (fun t : ℝ => t ^ (Module.finrank ℝ Space - 1) • inverseSquareTrunc ρ t)
      ((Iio ρ).indicator (fun _ => (1 : ℝ))) (Ioi 0) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  rw [finrank_space_eq_three]
  simp only [inverseSquareTrunc, smul_eq_mul]
  by_cases h : t < ρ
  · rw [indicator_of_mem (show t ∈ Iio ρ from h), indicator_of_mem (show t ∈ Iio ρ from h)]
    field_simp
  · rw [indicator_of_notMem (show t ∉ Iio ρ from h), indicator_of_notMem (show t ∉ Iio ρ from h)]
    simp

private theorem integrable_inverseSquareTrunc (ρ : ℝ) :
    Integrable (fun x : Space => inverseSquareTrunc ρ ‖x‖) := by
  rw [integrable_fun_norm_addHaar volume (f := inverseSquareTrunc ρ),
    integrableOn_congr_fun (radial_inverseSquareTrunc ρ) measurableSet_Ioi]
  unfold IntegrableOn
  rw [integrable_indicator_iff measurableSet_Iio]
  unfold IntegrableOn
  rw [Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  exact integrableOn_const measure_Ioo_lt_top.ne

private theorem integral_inverseSquareTrunc (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∫ x : Space, inverseSquareTrunc ρ ‖x‖ =
      3 * (volume.real (Metric.ball (0 : Space) 1) * ρ) := by
  rw [integral_fun_norm_addHaar volume (inverseSquareTrunc ρ),
    setIntegral_congr_fun measurableSet_Ioi (radial_inverseSquareTrunc ρ),
    integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Iio_inter_Ioi, setIntegral_const, Real.volume_real_Ioo_of_le hρ, finrank_space_eq_three]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

private theorem abs_kernelGrad_apply_le (w : Space) (i : Fin 3) :
    |FundSol.kernelGrad w i| ≤ (4 * π)⁻¹ * ‖w‖⁻¹ ^ 2 := by
  have h1 : |FundSol.kernelGrad w i| ≤ ‖FundSol.kernelGrad w‖ := by
    have h := PiLp.norm_apply_le (FundSol.kernelGrad w) i
    rwa [Real.norm_eq_abs] at h
  have h2 : ‖FundSol.kernelGrad w‖ = (4 * π)⁻¹ * ‖w‖⁻¹ ^ 2 := by
    rcases eq_or_ne w 0 with rfl | hw
    · simp [FundSol.kernelGrad]
    · have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      rw [FundSol.kernelGrad, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
  exact h2 ▸ h1

private theorem measurable_kernelGrad : Measurable FundSol.kernelGrad := by
  unfold FundSol.kernelGrad
  fun_prop

private theorem nearCutoff_eq_zero_of_le {y z : Space} (h : max 1 ‖y‖ / 2 ≤ ‖y - z‖) :
    nearCutoff y z = 0 := by
  unfold nearCutoff
  apply Real.smoothTransition.zero_of_nonpos
  have hr : 0 < max 1 ‖y‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [norm_sub_rev] at h
  have h4 : (max 1 ‖y‖) ^ 2 ≤ 4 * ‖z - y‖ ^ 2 := by nlinarith
  rw [sub_nonpos, le_div_iff₀ (by positivity)]
  nlinarith

private theorem one_add_norm_le_of_near {y z : Space} (h : ‖y - z‖ < max 1 ‖y‖ / 2) :
    1 + ‖y‖ ≤ 2 * (1 + ‖z‖) := by
  have h1 : ‖y‖ - ‖z‖ ≤ ‖y - z‖ := norm_sub_norm_le y z
  have h2 : max 1 ‖y‖ ≤ 1 + ‖y‖ := max_le (by linarith [norm_nonneg y]) (by linarith)
  linarith

private theorem decay_bound_of_near {g : Space → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hg : ∀ z, |g z| ≤ A / (1 + ‖z‖) ^ 4) {y z : Space} (h : ‖y - z‖ < max 1 ‖y‖ / 2) :
    |g z| ≤ 16 * A / (1 + ‖y‖) ^ 4 := by
  refine (hg z).trans ?_
  have hz : 0 < 1 + ‖z‖ := by positivity
  have hy : 0 < 1 + ‖y‖ := by positivity
  have hle : (1 + ‖y‖) ^ 4 ≤ 16 * (1 + ‖z‖) ^ 4 := by
    have := pow_le_pow_left₀ hy.le (one_add_norm_le_of_near h) 4
    calc (1 + ‖y‖) ^ 4 ≤ (2 * (1 + ‖z‖)) ^ 4 := this
      _ = 16 * (1 + ‖z‖) ^ 4 := by ring
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc A * (1 + ‖y‖) ^ 4 ≤ A * (16 * (1 + ‖z‖) ^ 4) := mul_le_mul_of_nonneg_left hle hA
    _ = 16 * A * (1 + ‖z‖) ^ 4 := by ring

theorem newtonNear_holds : NewtonNear := by
  refine ⟨(4 * π)⁻¹ * 16 * (3 * volume.real (Metric.ball (0 : Space) 1)), ?_⟩
  intro g A hg hgA i y
  have hV0 : 0 ≤ volume.real (Metric.ball (0 : Space) 1) := measureReal_nonneg
  have hA : 0 ≤ A := by
    have h0 := hgA 0
    simp only [norm_zero, add_zero, one_pow, div_one] at h0
    exact (abs_nonneg _).trans h0
  have hr : 0 < max 1 ‖y‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hρ0 : 0 ≤ max 1 ‖y‖ / 2 := by positivity
  have hy : 0 < 1 + ‖y‖ := by positivity
  have hK : 0 ≤ (4 * π)⁻¹ * (16 * A / (1 + ‖y‖) ^ 4) := by positivity
  have hmeas : AEStronglyMeasurable
      (fun z => FundSol.kernelGrad (y - z) i * (nearCutoff y z * g z)) volume := by
    have hk : Measurable fun z : Space => FundSol.kernelGrad (y - z) i :=
      (PiLp.continuous_apply 2 _ i).measurable.comp
        (measurable_kernelGrad.comp (measurable_const.sub measurable_id))
    have hc : Continuous fun z : Space => nearCutoff y z := by
      unfold nearCutoff
      exact Real.smoothTransition.continuous.comp (by fun_prop)
    exact (hk.mul (hc.measurable.mul hg.measurable)).aestronglyMeasurable
  have hmaj : Integrable (fun z : Space =>
      (4 * π)⁻¹ * (16 * A / (1 + ‖y‖) ^ 4) * inverseSquareTrunc (max 1 ‖y‖ / 2) ‖y - z‖) :=
    ((integrable_inverseSquareTrunc (max 1 ‖y‖ / 2)).comp_sub_left y).const_mul _
  have hpt : ∀ z, ‖FundSol.kernelGrad (y - z) i * (nearCutoff y z * g z)‖ ≤
      (4 * π)⁻¹ * (16 * A / (1 + ‖y‖) ^ 4) * inverseSquareTrunc (max 1 ‖y‖ / 2) ‖y - z‖ := by
    intro z
    rw [Real.norm_eq_abs]
    by_cases hz : ‖y - z‖ < max 1 ‖y‖ / 2
    · rw [inverseSquareTrunc, indicator_of_mem (show ‖y - z‖ ∈ Iio (max 1 ‖y‖ / 2) from hz),
        abs_mul, abs_mul]
      have hc : |nearCutoff y z| ≤ 1 := by
        unfold nearCutoff
        rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _
      have hgz := decay_bound_of_near hA hgA hz
      have hkz := abs_kernelGrad_apply_le (y - z) i
      calc |FundSol.kernelGrad (y - z) i| * (|nearCutoff y z| * |g z|)
          ≤ ((4 * π)⁻¹ * ‖y - z‖⁻¹ ^ 2) * (1 * (16 * A / (1 + ‖y‖) ^ 4)) := by
            gcongr
        _ = (4 * π)⁻¹ * (16 * A / (1 + ‖y‖) ^ 4) * (fun s : ℝ => s⁻¹ ^ 2) ‖y - z‖ := by
            simp only
            ring
    · rw [nearCutoff_eq_zero_of_le (not_lt.mp hz), inverseSquareTrunc,
        indicator_of_notMem (show ‖y - z‖ ∉ Iio (max 1 ‖y‖ / 2) from hz)]
      simp
  refine ⟨hmaj.mono' hmeas (ae_of_all _ hpt), ?_⟩
  have hint : ∫ z, (4 * π)⁻¹ * (16 * A / (1 + ‖y‖) ^ 4) *
      inverseSquareTrunc (max 1 ‖y‖ / 2) ‖y - z‖ =
      (4 * π)⁻¹ * (16 * A / (1 + ‖y‖) ^ 4) *
        (3 * (volume.real (Metric.ball (0 : Space) 1) * (max 1 ‖y‖ / 2))) := by
    rw [integral_const_mul,
      integral_sub_left_eq_self (μ := volume)
        (f := fun z : Space => inverseSquareTrunc (max 1 ‖y‖ / 2) ‖z‖) y,
      integral_inverseSquareTrunc _ hρ0]
  have hρle : max 1 ‖y‖ / 2 ≤ 1 + ‖y‖ := by
    have : max 1 ‖y‖ ≤ 1 + ‖y‖ := max_le (by linarith [norm_nonneg y]) (by linarith)
    linarith
  rw [← Real.norm_eq_abs]
  calc ‖∫ z, FundSol.kernelGrad (y - z) i * (nearCutoff y z * g z)‖
      ≤ ∫ z, (4 * π)⁻¹ * (16 * A / (1 + ‖y‖) ^ 4) *
          inverseSquareTrunc (max 1 ‖y‖ / 2) ‖y - z‖ :=
        norm_integral_le_of_norm_le hmaj (ae_of_all _ hpt)
    _ = (4 * π)⁻¹ * (16 * A / (1 + ‖y‖) ^ 4) *
          (3 * (volume.real (Metric.ball (0 : Space) 1) * (max 1 ‖y‖ / 2))) := hint
    _ ≤ (4 * π)⁻¹ * (16 * A / (1 + ‖y‖) ^ 4) *
          (3 * (volume.real (Metric.ball (0 : Space) 1) * (1 + ‖y‖))) := by
        gcongr
    _ = (4 * π)⁻¹ * 16 * (3 * volume.real (Metric.ball (0 : Space) 1)) * A / (1 + ‖y‖) ^ 3 := by
        field_simp

end Breakdown.FarField
