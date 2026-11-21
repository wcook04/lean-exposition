import Breakdown.CertCell.RowsMatchKinds
import Breakdown.CertCell.RowsMatchKeyData
import Breakdown.CertCell.RowsMatchKeySplit
import Breakdown.CertCell.RowsMatchKeyFlux
import Breakdown.CertCell.RowsMatchKeyFlip
import Breakdown.CertCell.RowsMatchNormalSegment

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCalculus

theorem rowsMatchFieldsHolds_of_lift (hPF : PlanePairInternal.PlaneTraceFacts)
    (hPS : PlaneFlipFacts.PeriodicSecondOrderHolds) (hL : HarmonicLiftStatement)
    (hHT : ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), HarmonicTraceIndependence D) :
    RowsMatchFieldsHolds :=
  rowsMatchFieldsHolds_of_parts
    (fun D _ _ _ _ h => keyHeadMatch_holds (hHT D) h.cell_conditions h.rows.key_order)
    (fun _ _ _ T _ h => keyEvalTransfer_holds (keyPlaneFlip_holds hPF T.keyLayout h.rows.key_order))
    (fun D _ _ T _ _ => keySplitAdditive_of_lift hPS hL D T.keyLayout)
    (fun D _ _ _ _ _ => keyFluxHolds_of_lift hPS hL D)
    (fun D _ _ _ _ h => sideVelocityKeyMatch_holds (hHT D) h.cell_conditions h.rows.key_order)
    hPS
    (SegmentNormal.normalSegmentHolds_of hL hPS)

end Assembly

end CertCell

end Breakdown
