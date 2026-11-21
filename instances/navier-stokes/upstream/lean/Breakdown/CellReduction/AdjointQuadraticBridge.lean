import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

theorem adjointQuadCoeff_nonneg {w₀ : ℝ} (hw : 0 < w₀) (cubic : Bool) :
    0 ≤ adjointQuadCoeff w₀ cubic := by
  unfold adjointQuadCoeff supBoundFactor
  split_ifs
  · exact div_nonneg (by positivity) hw.le
  · positivity

theorem adjointQuadraticBridge_of (hQ : AdjointQuadTermHolds) (hP : PeriodGlueHolds) :
    AdjointQuadraticBridgeHolds := by
  intro k d r hs hc j hj q hq v G H g hv
  have hw : 0 < d.weight := hs.weight_pos
  have hz : 0 ≤ r.sizeNum j := hc.sizeNum_nonneg j hj
  have h1 := hQ d.symmetries (d.period q) d.weight (r.sizeNum j) (r.cubicForm j) v G H g
    (d.adjoint j q) hw hz hv (hs.adjoint_measurable j hj q hq) (fun σ => hc.size_bound j hj q hq σ)
  have hcoef : 0 ≤ adjointQuadCoeff d.weight (r.cubicForm j) := adjointQuadCoeff_nonneg hw _
  have hE : 0 ≤ weightedEnergy (fun _ => d.weight) G H := ENNReal.toReal_nonneg
  have hB : 0 ≤ adjointQuadCoeff d.weight (r.cubicForm j) * r.sizeNum j *
      weightedEnergy (fun _ => d.weight) G H := mul_nonneg (mul_nonneg hcoef hz) hE
  have h2 := hP.2.1 (fun σ y => G σ y (v σ y)) (d.adjoint j q) _ hB h1
  rw [hs.weightFn_const]
  exact h2.trans (mul_le_mul_of_nonneg_right (hc.coeff_le j hj) hE)

end CertReduction

end Breakdown
