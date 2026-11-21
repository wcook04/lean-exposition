import Breakdown.CertCell.ShapeStatements
import Breakdown.CertCell.InstancePairStatements
import Breakdown.CertCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

def CompactFieldSupportRadius : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (tb : ℝ), IsShapeParams P → IsCompactTimeFieldData tb D →
    HasEdgeBreak tb D → ∀ σ y, P.chartLength * tb / (1 - tb) < ‖y‖ → shapeInfoField P D σ y = 0

theorem actuatorSupportInCells_of_shape (hs : CompactFieldSupportRadius) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (F : GivenShapeEntry k) (H : ℝ) (h : ActuatorSupportFacts D F H) :
    InstancePair.ActuatorSupportInCells D := by
  intro i σ y hne
  have hle : ‖y‖ ≤ H := by
    by_contra hlt
    push_neg at hlt
    apply hne
    rw [h.actuator_eq i]
    exact hs _ _ _ (h.actuatorParams_valid i) (h.actuators_valid i) (h.edge_break i) σ y
      (lt_of_le_of_lt (h.radius_le i) hlt)
  have hn : ‖y‖ = Real.sqrt (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
  refine h.mesh_covers _ ⟨⟨Real.sqrt_nonneg _, ?_⟩, ⟨abs_nonneg _, ?_⟩⟩
  · refine le_trans ?_ hle
    rw [hn]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (y 2)])
  · refine le_trans ?_ hle
    rw [hn, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)])

end GivenShape

end CertCell

end Breakdown
