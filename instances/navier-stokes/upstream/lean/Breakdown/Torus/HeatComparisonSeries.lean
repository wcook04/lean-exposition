import Breakdown.Torus.HeatComparisonStatements

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace TorusSeriesEval.Internal

open TorusSeries.Internal

theorem norm_term (c : Lattice → Coef) (k : Lattice) (x : Space) : ‖term c k x‖ = ‖c k‖ := by
  rw [term, norm_smul, FreqTrSeries.Internal.norm_character, one_mul]

def limitFn (c : Lattice → Coef) (x : Space) : Coef := ∑' k, term c k x

theorem continuous_limitFn (c : Lattice → Coef) (hc : Summable fun k => ‖c k‖) :
    Continuous (limitFn c) :=
  continuous_tsum (continuous_term c) hc fun k x => (norm_term c k x).le

theorem norm_limitFn_sub_le (c : Lattice → Coef) (hc : Summable fun k => ‖c k‖)
    (s : Finset Lattice) (x : Space) :
    ‖limitFn c x - partialSum c s x‖ ≤ ∑' k, ‖c k‖ - ∑ k ∈ s, ‖c k‖ := by
  have hn : Summable fun k => ‖term c k x‖ := by
    simp only [norm_term]
    exact hc
  have hs : Summable fun k => term c k x := hn.of_norm
  have e1 := hs.sum_add_tsum_compl (s := s)
  have e2 := hc.sum_add_tsum_compl (s := s)
  have hsub : limitFn c x - partialSum c s x = ∑' k : ↑((s : Set Lattice)ᶜ), term c k x := by
    rw [limitFn, ← e1]
    exact add_sub_cancel_left _ _
  rw [hsub]
  calc ‖∑' k : ↑((s : Set Lattice)ᶜ), term c k x‖
      ≤ ∑' k : ↑((s : Set Lattice)ᶜ), ‖term c k x‖ := norm_tsum_le_tsum_norm (hn.subtype _)
    _ = ∑' k : ↑((s : Set Lattice)ᶜ), ‖c k‖ := by simp only [norm_term]
    _ = ∑' k, ‖c k‖ - ∑ k ∈ s, ‖c k‖ := by linarith

theorem hasSum_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : Lattice → Coef) (hc : Summable fun k => ‖c k‖) :
    HasSum (fun k => lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k))
      ((memLp_of_continuous p (continuous_limitFn c hc)).toLp (limitFn c)) := by
  have := finite_cell
  rw [HasSum, SummationFilter.unconditional_filter]
  simp_rw [sum_lpOrZero]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hT : Tendsto (fun s : Finset Lattice => ∑' k, ‖c k‖ - ∑ k ∈ s, ‖c k‖) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ∑' k, ‖c k‖)).sub hc.hasSum
    simpa only [sub_self, SummationFilter.unconditional_filter] using h
  have hM := hT.const_mul ((measureUnivNNReal (volume.restrict cell) : ℝ) ^ p.toReal⁻¹)
  rw [mul_zero] at hM
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hM
  have hT0 : 0 ≤ ∑' k, ‖c k‖ - ∑ k ∈ s, ‖c k‖ :=
    (norm_nonneg _).trans (norm_limitFn_sub_le c hc s 0)
  rw [← MemLp.toLp_sub]
  refine Lp.norm_le_of_ae_bound hT0 ?_
  filter_upwards [MemLp.coeFn_toLp ((memLp_of_continuous p (continuous_partialSum c s)).sub
    (memLp_of_continuous p (continuous_limitFn c hc)))] with x hx
  rw [hx, Pi.sub_apply, norm_sub_rev]
  exact norm_limitFn_sub_le c hc s x

theorem coeFn_torusSeries (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : Lattice → Coef)
    (hc : Summable fun k => ‖c k‖) :
    (torusSeries p c : Space → Coef) =ᵐ[volume.restrict cell]
      (fun x => ∑' k, character (-k) x • c k) := by
  rw [torusSeries, (hasSum_toLp p c hc).tsum_eq]
  exact MemLp.coeFn_toLp _

end TorusSeriesEval.Internal

theorem torusSeriesPointwise : TorusSeriesPointwise := fun c hc =>
  ⟨TorusSeriesEval.Internal.coeFn_torusSeries 2 c hc,
    TorusSeriesEval.Internal.coeFn_torusSeries 6 c hc⟩

end Breakdown.Periodic
