import Breakdown.CellReduction.PotentialShape
import Breakdown.FracCell.GivenAuxDualPartsRestOpenLeaves

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown

namespace PotentialShape

namespace Internal.RadialFlux

open CellCert.GivenFields.OpenLeavesInternal (test_bounds j2_deriv ind_integrable)

theorem smul_norm_pos {s : ℝ} (hs : 0 < s) (y : Space) : ‖s • y‖ = s * ‖y‖ := by
  rw [norm_smul, Real.norm_of_nonneg hs.le]

theorem rescaled_integral (φ : Space → ℝ) (u : Space → ℂ) {s : ℝ} (hs : 0 < s) :
    ∫ y, (φ y * ‖y‖⁻¹) • (s ^ 2 • u (s • y)) = ∫ z, (φ (s⁻¹ • z) * ‖z‖⁻¹) • u z := by
  have hcv := Measure.integral_comp_smul (volume : Measure Space)
    (fun z => (φ (s⁻¹ • z) * ‖z‖⁻¹) • u z) s
  rw [finrank_euclideanSpace_fin] at hcv
  have e : (fun y : Space => (φ y * ‖y‖⁻¹) • (s ^ 2 • u (s • y))) =
      fun y => (s ^ 3) • ((φ (s⁻¹ • s • y) * ‖s • y‖⁻¹) • u (s • y)) := by
    funext y
    rw [inv_smul_smul₀ hs.ne', smul_norm_pos hs, smul_smul, smul_smul]
    congr 1
    rcases (norm_nonneg y).eq_or_lt with h | h
    · rw [← h]; simp
    · field_simp
  rw [e, integral_smul, hcv, smul_smul, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), one_smul]

theorem radialWeak (u : Space → ℂ) (hu : Measurable u) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, ‖u y‖ ≤ B)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hSlopeBound : ∀ y : Space, y ≠ 0 →
      LipschitzOnWith (Real.toNNReal C) (fun s : ℝ => s ^ 2 • u (s • y)) (Metric.ball 1 (1 / 2)))
    (D : Space → ℂ) (hD : ∀ᵐ y, HasDerivAt (fun s : ℝ => s ^ 2 • u (s • y)) (D y) 1)
    (hDm : AEStronglyMeasurable D volume) (φ : Space → ℝ) (hφ : IsTestFunction φ) :
    Integrable (fun y => fderiv ℝ φ y (‖y‖⁻¹ • y) • u y) ∧
      ∫ y, fderiv ℝ φ y (‖y‖⁻¹ • y) • u y = -∫ y, φ y • (‖y‖⁻¹ • D y) := by
  obtain ⟨R, Mφ, Mφ', hR, hM0, hM0', hM, hM', hz, hz'⟩ := test_bounds φ hφ
  have hcd : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by simp)
  have hφm : Measurable φ := hφ.1.continuous.measurable
  have hsm : ∀ s : ℝ, Measurable (fun y : Space => u (s • y)) := fun s => hu.comp (measurable_const_smul s)
  refine ⟨?_, ?_⟩
  · have e : (fun y => fderiv ℝ φ y (‖y‖⁻¹ • y) • u y) =
        fun y => (‖y‖⁻¹ * fderiv ℝ φ y y) • u y := by
      funext y; rw [map_smul, smul_eq_mul]
    rw [e]
    refine Integrable.mono' ((ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Space) R)
      (continuousOn_const (c := Mφ' * B))).integrable_indicator measurableSet_closedBall)
      ((measurable_norm.inv.mul (hcd.clm_apply continuous_id).measurable).smul hu).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    by_cases hyR : ‖y‖ ≤ R
    · rw [Set.indicator_of_mem (by rwa [Metric.mem_closedBall, dist_zero_right])]
      have hzz : ‖y‖⁻¹ * ‖y‖ ≤ 1 := by
        rcases (norm_nonneg y).eq_or_lt with h | h
        · rw [← h]; simp
        · rw [inv_mul_cancel₀ h.ne']
      rw [norm_smul, norm_mul, norm_inv, norm_norm]
      have h1 : ‖fderiv ℝ φ y y‖ ≤ Mφ' * ‖y‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hM' y)
      calc ‖y‖⁻¹ * ‖fderiv ℝ φ y y‖ * ‖u y‖ ≤ ‖y‖⁻¹ * (Mφ' * ‖y‖) * B := by gcongr; exact hB y
        _ = Mφ' * (‖y‖⁻¹ * ‖y‖) * B := by ring
        _ ≤ Mφ' * 1 * B := by gcongr
        _ = Mφ' * B := by ring
    · rw [hz' y (le_of_lt (not_le.1 hyR))]
      simp only [zero_apply, mul_zero, zero_smul, norm_zero]
      exact Set.indicator_nonneg (fun y _ => by positivity) y
  · have h0 : ∀ᵐ y ∂(volume : Measure Space), y ∈ ({0} : Set Space)ᶜ :=
      compl_mem_ae_iff.2 (measure_singleton 0)
    have hJ1 := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume) (x₀ := (1 : ℝ))
      (F := fun (s : ℝ) (y : Space) => (φ y * ‖y‖⁻¹) • (s ^ 2 • u (s • y)))
      (F' := fun y : Space => (φ y * ‖y‖⁻¹) • D y)
      (bound := fun y => (Metric.ball (0 : Space) R).indicator (fun y => Mφ * C * ‖y‖⁻¹) y)
      (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
      (Eventually.of_forall fun s =>
        ((hφm.mul measurable_norm.inv).smul ((measurable_const (a := (s ^ 2 : ℝ))).smul (hsm s))).aestronglyMeasurable)
      ?_ ((hφm.mul measurable_norm.inv).aestronglyMeasurable.smul hDm) ?_
      (ind_integrable R (Mφ * C)) ?_
    · have hJ2 := j2_deriv u hu hB0 hB φ hφ
      have hJ1' : HasDerivAt (fun s : ℝ => ∫ z, (φ (s⁻¹ • z) * ‖z‖⁻¹) • u z)
          (∫ y, (φ y * ‖y‖⁻¹) • D y) 1 := by
        refine hJ1.2.congr_of_eventuallyEq ?_
        filter_upwards [eventually_gt_nhds one_pos] with s hs
        exact (rescaled_integral φ u hs).symm
      have hu' := hJ1'.unique hJ2
      have e2 : (fun y : Space => φ y • (‖y‖⁻¹ • D y)) = fun y => (φ y * ‖y‖⁻¹) • D y :=
        funext fun y => (mul_smul _ _ _).symm
      rw [e2, hu', neg_neg]
    · refine Integrable.mono' (ind_integrable R (Mφ * B))
        ((hφm.mul measurable_norm.inv).smul ((measurable_const (a := ((1 : ℝ) ^ 2 : ℝ))).smul (hsm 1))).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      by_cases hyR : ‖y‖ < R
      · rw [Set.indicator_of_mem (by rwa [Metric.mem_ball, dist_zero_right])]
        simp only [one_pow, one_smul]
        rw [norm_smul, norm_mul, norm_inv, norm_norm]
        calc ‖φ y‖ * ‖y‖⁻¹ * ‖u y‖ ≤ Mφ * ‖y‖⁻¹ * B := by
              gcongr; exact hM y; exact hB y
          _ = Mφ * B * ‖y‖⁻¹ := by ring
      · rw [hz y (not_lt.1 hyR)]
        simp only [zero_mul, zero_smul, norm_zero]
        exact Set.indicator_nonneg (fun y _ => by positivity) y
    · filter_upwards [h0] with y hy
      have hy' : y ≠ 0 := hy
      refine LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => ?_
      rw [Real.coe_nnabs, dist_eq_norm, ← smul_sub, norm_smul, ← dist_eq_norm]
      have hl := (hSlopeBound y hy').dist_le_mul s hs s' hs'
      rw [Real.coe_toNNReal _ hC0] at hl
      by_cases hyR : ‖y‖ < R
      · rw [Set.indicator_of_mem (by rwa [Metric.mem_ball, dist_zero_right]),
          abs_of_nonneg (by positivity), norm_mul, norm_inv, norm_norm]
        calc ‖φ y‖ * ‖y‖⁻¹ * dist _ _ ≤ Mφ * ‖y‖⁻¹ * (C * dist s s') := by
              gcongr; exact hM y
          _ = Mφ * C * ‖y‖⁻¹ * dist s s' := by ring
      · rw [hz y (not_lt.1 hyR)]
        simp only [zero_mul, norm_zero]
        positivity
    · filter_upwards [hD] with y hy
      exact hy.const_smul (φ y * ‖y‖⁻¹)

theorem rayDeriv_aestronglyMeasurable (u : Space → ℂ) (hu : Measurable u)
    (hd : ∀ᵐ y, DifferentiableAt ℝ (fun s : ℝ => s ^ 2 • u (s • y)) 1) :
    AEStronglyMeasurable (fun y => deriv (fun s : ℝ => s ^ 2 • u (s • y)) 1) volume := by
  have hm : ∀ n : ℕ, Measurable (fun y : Space => ((n : ℝ) + 1) •
      ((1 + ((n : ℝ) + 1)⁻¹) ^ 2 • u ((1 + ((n : ℝ) + 1)⁻¹) • y) - (1 : ℝ) ^ 2 • u ((1 : ℝ) • y))) := by
    intro n
    have h1 : Measurable (fun y : Space => u ((1 + ((n : ℝ) + 1)⁻¹) • y)) := hu.comp (measurable_const_smul _)
    have h2 : Measurable (fun y : Space => u ((1 : ℝ) • y)) := hu.comp (measurable_const_smul _)
    exact ((h1.const_smul ((1 + ((n : ℝ) + 1)⁻¹) ^ 2)).sub (h2.const_smul ((1 : ℝ) ^ 2))).const_smul ((n : ℝ) + 1)
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hm n).aestronglyMeasurable) ?_
  filter_upwards [hd] with y hy
  have hs := hasDerivAt_iff_tendsto_slope.1 hy.hasDerivAt
  have ht : Tendsto (fun n : ℕ => 1 + ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Eventually.of_forall fun n => ?_)
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
      simpa [one_div] using this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left]
      positivity
  refine (hs.comp ht).congr fun n => ?_
  simp only [Function.comp_apply, slope, vsub_eq_sub, add_sub_cancel_left, inv_inv]

end Internal.RadialFlux

end PotentialShape

end Breakdown
