import Breakdown.FracCell.ReductionAdjointFrameInverseSquareLower
import Breakdown.FracCell.ReductionAdjointFrameInverseSquareHalfPlane

open scoped ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert FracInternal.FrameInverseSquareParts

theorem frameInverseSquare_of (hS : SmoothModeBoundStatement) (hA : MirrorApproxStatement)
    (hL : ModeWeightedLowerStatement) (hR : ModeGradientLimitStatement) : FrameInverseSquareStatement := by
  intro m v G H hf k
  obtain ⟨u, hu, hG, hv⟩ := hA m v G H hf
  have h1 := hL v u hf.measurable_velocity (fun n => (hu n).1.continuous) hv k
  have h2 := hR G (fun n y => fderiv ℝ (u n) y) hf.measurable_gradient
    (fun n => ((hu n).1.continuous_fderiv (by simp)).aestronglyMeasurable) hf.gradient_two hG k
  have h3 : liminf (fun n => modeWeightedSide (u n) k) atTop ≤
      liminf (fun n => modeGradientSide (fun y => fderiv ℝ (u n) y) k) atTop :=
    liminf_le_liminf (Eventually.of_forall fun n => hS (u n) (hu n).1 (hu n).2.1 (hu n).2.2 k)
  rw [h2.liminf_eq] at h3
  exact h1.trans h3

theorem frameInverseSquare : FrameInverseSquareStatement :=
  frameInverseSquare_of (smoothModeBound_of frameModeCalculus halfPlaneBound') mirrorApprox modeWeightedLower modeGradientLimit

end Reduction

end CellCert

end Breakdown
