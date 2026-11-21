import Breakdown.Frac.StRealize
import Breakdown.FreqTr.FieldOp
import Breakdown.FreqTr.Rotation

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace FracInternal.Rotation

open Internal.Rotation

theorem rotL2_fracHeatL2 (R : Space ≃ₗᵢ[ℝ] Space) (α t : ℝ) (y : L2C) :
    rotL2 R (fracHeatL2 α t y) = fracHeatL2 α t (rotL2 R y) := by
  have hR := rotL2_realized fieldOpRealized R
  rcases fieldOp_cases id (fun ξ => fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace) with h | h
  · simp only [fracHeatL2, h, zero_apply, map_zero]
  · change IsRealizedBy (fracHeatL2 α t) _ _ at h
    apply Lp.ext
    filter_upwards [hR (fracHeatL2 α t y), ae_comp (qmp_liso R.symm) (h y), h (rotL2 R y), hR y]
      with ξ a b c d
    simp only [id] at b c
    rw [a, b, c, d]
    simp [fracHeatFactor, map_smul]

theorem rotL2_fracDilL2 (R : Space ≃ₗᵢ[ℝ] Space) (α : ℝ) {μ : ℝ} (hμ : 0 < μ) (y : L2C) :
    rotL2 R (fracDilL2 α μ y) = fracDilL2 α μ (rotL2 R y) := by
  have hR := rotL2_realized fieldOpRealized R
  have hc : μ ^ (-(1 / (2 * α))) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  rcases fieldOp_cases (fun ξ => (μ ^ (-(1 / (2 * α)))) • ξ)
      (fun _ => (μ ^ (1 - 3 / (2 * α))) • ContinuousLinearMap.id ℝ CSpace) with h | h
  · simp only [fracDilL2, h, zero_apply, map_zero]
  · change IsRealizedBy (fracDilL2 α μ) _ _ at h
    apply Lp.ext
    filter_upwards [hR (fracDilL2 α μ y), ae_comp (qmp_liso R.symm) (h y), h (rotL2 R y),
      ae_comp (qmp_smul hc) (hR y)] with ξ a b c d
    rw [a, b, c, d]
    simp [map_smul]

end FracInternal.Rotation

open Internal.Rotation FracInternal.Rotation in
theorem fracRotationAlgebra (α : ℝ) (hα : 0 < α) (h1 : FracHeatSemigroup α)
    (h2 : FracDilationAlgebra α) : FracRotationAlgebra α := by
  intro R
  refine ⟨fun t x => ?_, fun μ x => ?_⟩
  · apply Subtype.ext
    rw [rotX_coe fieldOpRealized, h1.2.2.2.2.2, h1.2.2.2.2.2, rotX_coe fieldOpRealized,
      rotL2_fracHeatL2]
  · by_cases hμ : 0 < μ
    · apply Subtype.ext
      rw [rotX_coe fieldOpRealized, h2.2.2.2.2 μ hμ, h2.2.2.2.2 μ hμ, rotX_coe fieldOpRealized,
        rotL2_fracDilL2 R α hμ]
    · simp [fracDilX, hμ]

end Breakdown.Freq
