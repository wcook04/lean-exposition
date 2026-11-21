import Breakdown.Uniqueness.FundSolDefs

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FundSol

def bumpRadius (u : ℝ) : ℝ := smoothTransition (1 - u)

def centeredBump (x y : Space) : ℝ := bumpRadius (‖y - x‖ ^ 2)

def bumpSumSecondPartialsProfile (u : ℝ) : ℝ :=
  6 * deriv bumpRadius u + 4 * u * deriv (deriv bumpRadius) u

theorem contDiff_bumpRadius : ContDiff ℝ ∞ bumpRadius :=
  smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem contDiff_deriv_bumpRadius : ContDiff ℝ ∞ (deriv bumpRadius) :=
  (contDiff_infty_iff_deriv.1 contDiff_bumpRadius).2

theorem contDiff_deriv_deriv_bumpRadius : ContDiff ℝ ∞ (deriv (deriv bumpRadius)) :=
  (contDiff_infty_iff_deriv.1 contDiff_deriv_bumpRadius).2

theorem differentiable_bumpRadius : Differentiable ℝ bumpRadius :=
  (contDiff_infty_iff_deriv.1 contDiff_bumpRadius).1

theorem differentiable_deriv_bumpRadius : Differentiable ℝ (deriv bumpRadius) :=
  (contDiff_infty_iff_deriv.1 contDiff_deriv_bumpRadius).1

theorem bumpRadius_eq_zero {u : ℝ} (hu : 1 ≤ u) : bumpRadius u = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

theorem deriv_bumpRadius_eq_zero {u : ℝ} (hu : 1 < u) : deriv bumpRadius u = 0 := by
  have h : bumpRadius =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [lt_mem_nhds hu] with v hv
    exact bumpRadius_eq_zero hv.le
  rw [h.deriv_eq]
  simp

theorem deriv_deriv_bumpRadius_eq_zero {u : ℝ} (hu : 1 < u) : deriv (deriv bumpRadius) u = 0 := by
  have h : deriv bumpRadius =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [lt_mem_nhds hu] with v hv
    exact deriv_bumpRadius_eq_zero hv
  rw [h.deriv_eq]
  simp

theorem bumpSumSecondPartialsProfile_eq_zero {u : ℝ} (hu : 1 < u) : bumpSumSecondPartialsProfile u = 0 := by
  simp [bumpSumSecondPartialsProfile, deriv_bumpRadius_eq_zero hu, deriv_deriv_bumpRadius_eq_zero hu]

theorem continuous_bumpSumSecondPartialsProfile : Continuous bumpSumSecondPartialsProfile := by
  unfold bumpSumSecondPartialsProfile
  have h1 := contDiff_deriv_bumpRadius.continuous
  have h2 := contDiff_deriv_deriv_bumpRadius.continuous
  fun_prop

private theorem hasDerivAt_radial_antiderivative (y : ℝ) :
    HasDerivAt (fun r : ℝ => bumpRadius (r ^ 2) + 2 * r ^ 2 * deriv bumpRadius (r ^ 2))
      (y * bumpSumSecondPartialsProfile (y ^ 2)) y := by
  have hs : HasDerivAt (fun r : ℝ => r ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have h1 := HasDerivAt.comp y (differentiable_bumpRadius (y ^ 2)).hasDerivAt hs
  have h2 := HasDerivAt.comp y (differentiable_deriv_bumpRadius (y ^ 2)).hasDerivAt hs
  have h3 : HasDerivAt (fun r : ℝ => bumpRadius (r ^ 2) + 2 * r ^ 2 * deriv bumpRadius (r ^ 2))
      (deriv bumpRadius (y ^ 2) * (2 * y) + (2 * (2 * y) * deriv bumpRadius (y ^ 2) +
        2 * y ^ 2 * (deriv (deriv bumpRadius) (y ^ 2) * (2 * y)))) y :=
    h1.add ((hs.const_mul 2).mul h2)
  convert h3 using 1
  simp only [bumpSumSecondPartialsProfile]
  ring

private theorem integral_Ioi_radial :
    ∫ y in Ioi (0 : ℝ), y * bumpSumSecondPartialsProfile (y ^ 2) = -1 := by
  have hcs : HasCompactSupport (fun y : ℝ => y * bumpSumSecondPartialsProfile (y ^ 2)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 2) ?_
    intro y hy
    have hy' : 2 < |y| := by simpa [Metric.mem_closedBall, Real.dist_eq] using hy
    have : 1 < y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    simp [bumpSumSecondPartialsProfile_eq_zero this]
  have hcont : Continuous (fun y : ℝ => y * bumpSumSecondPartialsProfile (y ^ 2)) := by
    have := continuous_bumpSumSecondPartialsProfile
    fun_prop
  have hlim : Tendsto (fun r : ℝ => bumpRadius (r ^ 2) + 2 * r ^ 2 * deriv bumpRadius (r ^ 2))
      atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with r hr
    have : 1 < r ^ 2 := by nlinarith
    simp [bumpRadius_eq_zero this.le, deriv_bumpRadius_eq_zero this]
  have hA := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun r : ℝ => bumpRadius (r ^ 2) + 2 * r ^ 2 * deriv bumpRadius (r ^ 2))
    (hasDerivAt_radial_antiderivative 0).continuousAt.continuousWithinAt
    (fun y _ => hasDerivAt_radial_antiderivative y)
    (hcont.integrable_of_hasCompactSupport hcs).integrableOn hlim
  rw [hA]
  simp [bumpRadius]

theorem integral_bumpSumSecondPartialsProfile_mul_kernel :
    ∫ t : Space, bumpSumSecondPartialsProfile (‖t‖ ^ 2) * kernel t = 1 := by
  have h := integral_fun_norm_addHaar (volume : Measure Space)
    (fun r => bumpSumSecondPartialsProfile (r ^ 2) * (-(4 * π)⁻¹ * r⁻¹))
  simp only [kernel]
  rw [h]
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ Space - 1) •
      (bumpSumSecondPartialsProfile (y ^ 2) * (-(4 * π)⁻¹ * y⁻¹)) =
      -(4 * π)⁻¹ * ∫ y in Ioi (0 : ℝ), y * bumpSumSecondPartialsProfile (y ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy' : y ≠ 0 := ne_of_gt hy
    simp only [finrank_euclideanSpace_fin, smul_eq_mul]
    field_simp
  rw [hI, integral_Ioi_radial, measureReal_def, EuclideanSpace.volume_ball_fin_three,
    finrank_euclideanSpace_fin]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, nsmul_eq_mul, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  field_simp
  ring

theorem contDiff_centeredBump (x : Space) : ContDiff ℝ ∞ (centeredBump x) := by
  exact contDiff_bumpRadius.comp ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_centeredBump (x : Space) : HasCompactSupport (centeredBump x) := by
  refine HasCompactSupport.intro (isCompact_closedBall x 1) ?_
  intro y hy
  have hy' : 1 < ‖y - x‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
  exact bumpRadius_eq_zero (by nlinarith)

theorem centeredBump_self (x : Space) : centeredBump x x = 1 := by
  simp [centeredBump, bumpRadius]

private theorem hasFDerivAt_normSq_sub (x z : Space) :
    HasFDerivAt (fun w : Space => ‖w - x‖ ^ 2)
      (2 • (innerSL ℝ (z - x)).comp (ContinuousLinearMap.id ℝ Space)) z :=
  ((hasFDerivAt_id z).sub_const x).norm_sq

private theorem hasFDerivAt_centeredBump (x z : Space) :
    HasFDerivAt (centeredBump x) ((2 * deriv bumpRadius (‖z - x‖ ^ 2)) • innerSL ℝ (z - x)) z := by
  have h := (differentiable_bumpRadius (‖z - x‖ ^ 2)).hasDerivAt.comp_hasFDerivAt z
    (hasFDerivAt_normSq_sub x z)
  have e : (2 * deriv bumpRadius (‖z - x‖ ^ 2)) • innerSL ℝ (z - x) =
      deriv bumpRadius (‖z - x‖ ^ 2) • 2 • (innerSL ℝ (z - x)).comp (ContinuousLinearMap.id ℝ Space) := by
    ext v
    simp [innerSL_apply_apply]
    ring
  rw [e]
  exact h

theorem scalarSumSecondPartials_centeredBump (x y : Space) :
    scalarSumSecondPartials (centeredBump x) y = bumpSumSecondPartialsProfile (‖y - x‖ ^ 2) := by
  have hfd : fderiv ℝ (centeredBump x) =
      fun z => (2 * deriv bumpRadius (‖z - x‖ ^ 2)) • innerSL ℝ (z - x) :=
    funext fun z => (hasFDerivAt_centeredBump x z).fderiv
  have hc := ((differentiable_deriv_bumpRadius (‖y - x‖ ^ 2)).hasDerivAt.comp_hasFDerivAt y
      (hasFDerivAt_normSq_sub x y)).const_mul 2
  have hl : HasFDerivAt (fun z : Space => innerSL ℝ (z - x))
      ((innerSL ℝ).comp (ContinuousLinearMap.id ℝ Space)) y :=
    (innerSL ℝ).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
  have hd2 := (hc.smul hl).congr_of_eventuallyEq (f₁ := fderiv ℝ (centeredBump x))
    (Filter.Eventually.of_forall fun z => by rw [hfd]; rfl)
  simp only [scalarSumSecondPartials, secondPartial, iteratedFDeriv_two_apply, hd2.fderiv]
  have hyx : ∀ i, (y - x).ofLp i = y.ofLp i - x.ofLp i := fun i => rfl
  simp [unitVector, EuclideanSpace.inner_single_right,
    innerSL_apply_apply, bumpSumSecondPartialsProfile, Fin.sum_univ_three]
  have he : ∀ i : Fin 3, (innerSL ℝ (EuclideanSpace.single i (1 : ℝ) : Space))
      (EuclideanSpace.single i 1) = 1 := by
    intro i
    rw [innerSL_apply_apply]
    simp
  have hn : ‖y - x‖ ^ 2 = (y.ofLp 0 - x.ofLp 0) ^ 2 + (y.ofLp 1 - x.ofLp 1) ^ 2 +
      (y.ofLp 2 - x.ofLp 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, hyx, hyx, hyx]
  rw [he 0, he 1, he 2, hn]
  ring

end Breakdown.FundSol
