import Breakdown.FracCell.SharpModeExpansionRegular
import Breakdown.FracCell.SharpYChargeRegular

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

namespace SharpMxGradSeries.Internal

theorem weighted_le (K : CellBox) (hK : IsCellBox K) (h0 : K.r₁ ≠ 0) (g : ℝ × ℝ → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hgi : IntegrableOn (fun p : ℝ × ℝ => p.1 * g p) K.rect) :
    ∫ p in K.rect, K.lineWeight p.1 * g p ≤ K.r₁⁻¹ * ∫ p in K.rect, p.1 * g p := by
  have hr : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
  have hw : ∀ r, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, h0]
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => ?_) (hgi.const_mul _) ?_
  · simp only [hw, one_mul]; exact hg0 p
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    simp only [hw, one_mul]
    have h1 : K.r₁ ≤ p.1 := hp.1.1
    rw [← mul_assoc]
    have h2 : 1 ≤ K.r₁⁻¹ * p.1 := by
      rw [inv_mul_eq_div, le_div_iff₀ hr, one_mul]; exact h1
    nlinarith [hg0 p]

end SharpMxGradSeries.Internal

open SharpMxGradSeries.Internal in
theorem gradSeries_holds : GradSeriesStatement := by
  intro K hK m hm E hE1 hE2 a b
  have H := SharpYChargeRegular.Internal.gm_sum K hK m (by omega) hE1 hE2 a b
  by_cases h0 : K.r₁ = 0
  · have hw : ∀ r, K.lineWeight r = r := fun r => by simp [CellBox.lineWeight, h0]
    simp only [hw]
    exact H.2
  · refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => weighted_le K hK h0 _ (fun p => by positivity) (H.1 n))
      (H.2.mul_left K.r₁⁻¹)
    have hw : ∀ r, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, h0]
    simp only [hw, one_mul]
    exact integral_nonneg fun p => by positivity

end Breakdown.CellCert.CellAnalysis
