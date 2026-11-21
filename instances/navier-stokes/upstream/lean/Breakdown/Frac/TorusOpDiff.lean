import Breakdown.Frac.StTorusInverse
import Breakdown.Torus.OpBounds

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

open OpBounds.Internal in
theorem fracOpDiffBounds (α : ℝ) (hα : 1 < α) (hS : SeqOpSpec) (hP : PieceOperatorStatement) :
    FracOpDiffBounds α hα := by
  constructor
  · intro F P k θ M E _ _ J f g hL hL1 h
    unfold fracR3Op
    exact norm_chain_sub_le hS hP (fun _ => F.toHeatBilinear) F.CK
      (MildFramework.stepLength P k) M (fun _ => rfl) hL hL1 _ _ f g h
  · intro T lam θ M hT hT1 hl hl1 E _ _ Jt f g hlam h
    have hck : ∀ n, (fracStepFrame α hα (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1 n)).CK = fracStepCK α hα := fun _ => rfl
    have hL : 0 < 1 - lam := by linarith
    have hL1 : 1 - lam ≤ 1 := by linarith
    unfold fracTorusOp
    exact norm_chain_sub_le hS hP _ (fracStepCK α hα) (1 - lam) M hck hL hL1 _ _ f g h

end Breakdown.Periodic
