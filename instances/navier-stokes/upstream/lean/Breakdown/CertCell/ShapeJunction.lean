import Breakdown.CertCell.ShapeStatements
import Breakdown.CertCell.InstanceClauseSplit
import Breakdown.CertCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

theorem shapeAdmissible_of_layer {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM) (hL : LayerShapeFacts D X) (hT : ShapeValuesFacts D) :
    ∀ q ∈ D.cert.params, InstanceSplit.ShapeAdmissibleClauses (D.cert.period q) (D.bounds q) D.cert.weightFn
      D.given D.cert.weight := by
  intro q hq
  have hw : D.cert.weightFn = fun _ => D.cert.weight := funext hT.weight_const
  refine ⟨hT.period_pos q hq, hT.weight_pos, fun y => (hT.weight_const y).ge, ?_, ?_, hT.harmonics_neg q hq,
    hT.harmonics_zero q hq, hL.harmonics_span _ (hT.labels_in q hq) (hT.harmonics_neg q hq)⟩
  · rw [hw]
    exact measurable_const
  · intro φ y
    rw [hT.weight_const, hT.weight_const]

theorem shapeFlip_of_values {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)
    (hT : ShapeValuesFacts D) :
    ∀ q ∈ D.cert.params, InstanceSplit.ShapeFlipClauses (D.bounds q) D.cert.weightFn := by
  intro q hq
  exact ⟨fun y => by rw [hT.weight_const, hT.weight_const], hT.harmonics_flip q hq⟩

end GivenShape

end CertCell

end Breakdown
