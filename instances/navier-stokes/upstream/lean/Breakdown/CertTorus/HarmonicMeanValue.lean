import Breakdown.CertTorus.DecayStatements
import Breakdown.Uniqueness.FundSolByParts
import Breakdown.Uniqueness.FundSolPointwiseAux4

open MeasureTheory Set Real Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

open Breakdown.FundSol Breakdown.FundSol.Internal

private theorem integral_mollifier_mul_eq_laplacian {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {ρ : ℝ} (hρ : 0 < ρ) (y : Space) :
    ∫ z, mollifier ρ (y - z) * f z =
      ∫ z, scalarSumSecondPartials f z * potential (mollifier ρ) (y - z) := by
  have hP : ContDiff ℝ ∞ (potential (mollifier ρ)) :=
    contDiff_potential (contDiff_mollifier ρ) (hasCompactSupport_mollifier hρ)
  have hsub : Continuous (fun z : Space => y - z) := continuous_const.sub continuous_id
  calc ∫ z, mollifier ρ (y - z) * f z
      = ∫ z, ∑ i, f z * secondPartial (potential (mollifier ρ)) i i (y - z) := by
        congr 1; ext z
        rw [← Finset.mul_sum, mul_comm]
        congr 1
        exact (scalarSumSecondPartials_potential (contDiff_mollifier ρ)
          (hasCompactSupport_mollifier hρ) (y - z)).symm
    _ = ∑ i, ∫ z, f z * secondPartial (potential (mollifier ρ)) i i (y - z) := by
        refine integral_finsetSum _ fun i _ => ?_
        exact integrable_mul_of_cpt hf.continuous ((continuous_secondPartial hP i i).comp hsub)
          (Or.inl hc)
    _ = ∑ i, ∫ z, secondPartial f i i z * potential (mollifier ρ) (y - z) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (integral_secondPartial_mul hf hc hP y i i).symm
    _ = ∫ z, scalarSumSecondPartials f z * potential (mollifier ρ) (y - z) := by
        rw [← integral_finsetSum]
        · congr 1; ext z; rw [scalarSumSecondPartials, Finset.sum_mul]
        · intro i _
          exact integrable_mul_of_cpt (continuous_secondPartial hf i i) (hP.continuous.comp hsub)
            (Or.inl (hasCompactSupport_secondPartial hf hc i i))

theorem harmonicMeanValue_holds : HarmonicMeanValue := by
  intro g y r hr hg hharm ρ hρ hρr
  let c : ContDiffBump y := ⟨(ρ + r) / 2, r + 1, by linarith, by linarith⟩
  set f : Space → ℝ := fun z => c z * g z with hfdef
  have hfs : ContDiff ℝ ∞ f := c.contDiff.mul hg
  have hfc : HasCompactSupport f := c.hasCompactSupport.mul_right
  have hfg : ∀ z ∈ ball y ((ρ + r) / 2), f z = g z := fun z hz => by
    simp only [hfdef, c.one_of_mem_closedBall (ball_subset_closedBall hz), one_mul]
  have hin : ∀ z : Space, ‖y - z‖ < ρ → z ∈ ball y ((ρ + r) / 2) := fun z hz => by
    rw [mem_ball, dist_eq_norm, norm_sub_rev]; linarith
  have hlap : ∀ z, ‖y - z‖ < ρ → scalarSumSecondPartials f z = 0 := by
    intro z hz
    have hzb := hin z hz
    have hev : f =ᶠ[𝓝 z] g := Filter.eventually_of_mem (isOpen_ball.mem_nhds hzb) hfg
    rw [scalarSumSecondPartials_congr_nhds hev]
    exact hharm z (ball_subset_ball (by linarith) hzb)
  calc g y = f y := (hfg y (mem_ball_self (by linarith))).symm
    _ = potential (scalarSumSecondPartials f) y := (potential_scalarSumSecondPartials hfs hfc y).symm
    _ = ∫ z, scalarSumSecondPartials f z * kernel (y - z) := potential_apply _ _
    _ = ∫ z, scalarSumSecondPartials f z * potential (mollifier ρ) (y - z) := by
        congr 1; ext z
        by_cases hz : ‖y - z‖ < ρ
        · rw [hlap z hz, zero_mul, zero_mul]
        · rw [potential_mollifier_eq_kernel hρ (not_lt.1 hz)]
    _ = ∫ z, mollifier ρ (y - z) * f z := (integral_mollifier_mul_eq_laplacian hfs hfc hρ y).symm
    _ = ∫ z, mollifier ρ (y - z) * g z := by
        congr 1; ext z
        by_cases hz : ‖y - z‖ < ρ
        · rw [hfg z (hin z hz)]
        · rw [mollifier_eq_zero hρ (not_lt.1 hz), zero_mul, zero_mul]

end Breakdown.FarField
