import Breakdown.Uniqueness.PressureMollifyAux
import Breakdown.Uniqueness.FundSolMeanValue

open scoped ContDiff ENNReal Convolution
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Internal.PressureMollify

theorem hasCompactSupport_mollifier {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport (FundSol.mollifier ρ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) ρ) fun x hx =>
    FundSol.mollifier_eq_zero hρ (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx; exact hx.le)

theorem contDiff_mollify (ρ : ℝ) {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ)
    (hc : HasCompactSupport ϕ) : ContDiff ℝ ∞ (FundSol.mollify ρ ϕ) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (FundSol.contDiff_mollifier ρ).continuous.locallyIntegrable hϕ

theorem hasCompactSupport_mollify {ρ : ℝ} (hρ : 0 < ρ) {ϕ : Space → Space}
    (hc : HasCompactSupport ϕ) : HasCompactSupport (FundSol.mollify ρ ϕ) :=
  (hasCompactSupport_mollifier hρ).convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hc

theorem lsmul_flip :
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  ext a b; simp [mul_comm]

theorem divergenceAt_mollify_apply (ρ : ℝ) {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ)
    (hc : HasCompactSupport ϕ) (x : Space) :
    divergenceAt (FundSol.mollify ρ ϕ) x =
      (FundSol.mollifier ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] divergenceAt ϕ) x := by
  have hm : LocallyIntegrable (FundSol.mollifier ρ) volume :=
    (FundSol.contDiff_mollifier ρ).continuous.locallyIntegrable
  have hd : Continuous (fderiv ℝ ϕ) := hϕ.continuous_fderiv infty_ne_zero
  have hdc : HasCompactSupport (fderiv ℝ ϕ) := hc.fderiv (𝕜 := ℝ)
  have hF : HasFDerivAt (FundSol.mollify ρ ϕ)
      ((FundSol.mollifier ρ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR Space, volume]
        fderiv ℝ ϕ) x) x :=
    hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hm
      (hϕ.of_le (by exact_mod_cast le_top)) x
  rw [divergenceAt_eq_comp, Function.comp_apply, hF.fderiv, convolution_def, convolution_def,
    ← divergenceMap.integral_comp_comm (hdc.convolutionExists_right _ hm hd x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [divergenceMap_apply, divergenceAt, Finset.mul_sum]

theorem divergenceAt_mollify (ρ : ℝ) {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ)
    (hc : HasCompactSupport ϕ) :
    divergenceAt (FundSol.mollify ρ ϕ) =
      (divergenceAt ϕ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] FundSol.mollifier ρ) := by
  funext x
  rw [divergenceAt_mollify_apply ρ hϕ hc x, ← convolution_flip, lsmul_flip]

theorem measurable_kernel : Measurable FundSol.kernel := by
  unfold FundSol.kernel; fun_prop

theorem potential_convolution_mollifier {ρ : ℝ} (hρ : 0 < ρ) {ζ : Space → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) (x₀ : Space) :
    FundSol.potential (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] FundSol.mollifier ρ) x₀ =
      (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] FundSol.potential (FundSol.mollifier ρ)) x₀ := by
  have hm : Continuous (FundSol.mollifier ρ) := (FundSol.contDiff_mollifier ρ).continuous
  have hmc := hasCompactSupport_mollifier hρ
  have hK := FundSol.locallyIntegrable_kernel
  have hKn : LocallyIntegrable (fun x => ‖FundSol.kernel x‖) volume := fun x => (hK x).norm
  have hmK : Continuous ((fun x => ‖FundSol.mollifier ρ x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      fun x => ‖FundSol.kernel x‖) :=
    hmc.norm.continuous_convolution_left _ hm.norm hKn
  exact convolution_assoc (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (fun a b c => by simp [mul_assoc]) hζ.continuous.aestronglyMeasurable
    hm.aestronglyMeasurable measurable_kernel.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y =>
      hζc.convolutionExists_left_of_continuous_right _ hζ.continuous.locallyIntegrable hm y)
    (Filter.Eventually.of_forall fun y =>
      hmc.norm.convolutionExists_left _ hm.norm hKn y)
    (hζc.norm.convolutionExists_left_of_continuous_right _ hζ.continuous.norm.locallyIntegrable
      hmK x₀)

theorem potential_mollified_eq {ρ : ℝ} (hρ : 0 < ρ) {ζ : Space → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) {x₀ : Space}
    (hx : ∀ s ∈ tsupport ζ, ρ ≤ ‖x₀ - s‖) :
    FundSol.potential (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] FundSol.mollifier ρ) x₀ =
      FundSol.potential ζ x₀ := by
  rw [potential_convolution_mollifier hρ hζ hζc, convolution_def]
  conv_rhs => rw [FundSol.potential, convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ tsupport ζ
  · simp only
    rw [FundSol.potential_mollifier_eq_kernel hρ (hx s hs)]
  · simp [image_eq_zero_of_notMem_tsupport hs]

theorem hasCompactSupport_potential_sub {ρ : ℝ} (hρ : 0 < ρ) {ζ : Space → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) :
    HasCompactSupport (FundSol.potential (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      FundSol.mollifier ρ) - FundSol.potential ζ) := by
  refine HasCompactSupport.intro (hζc.isCompact.add (isCompact_closedBall (0 : Space) ρ))
    fun x hx => ?_
  have h : ∀ s ∈ tsupport ζ, ρ ≤ ‖x - s‖ := by
    intro s hs
    by_contra hlt'
    have hlt := not_le.1 hlt'
    apply hx
    have hmem : x - s ∈ Metric.closedBall (0 : Space) ρ := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hlt.le
    simpa using Set.add_mem_add hs hmem
  rw [Pi.sub_apply, potential_mollified_eq hρ hζ hζc h, sub_self]

end Breakdown.Internal.PressureMollify
