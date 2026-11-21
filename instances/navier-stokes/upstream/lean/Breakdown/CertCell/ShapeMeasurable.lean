import Breakdown.CertCell.ShapeStatements
import Breakdown.CertCell.ShapeScalarStatements
import Breakdown.CertCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (ChartParams)

theorem measurableBoundData_of_valueSets (hcb : ScalarShape.ChartBoundFacts) {C : Type} {nE nM : ℕ}
    (m : PieceWeights C nE nM) (T : ScalarShape.BoundValues) (P : ChartParams)
    (epsSpeed : Fin nE → ScalarShape.ChartBound) (muSpeed : Fin nM → ScalarShape.ChartBound)
    (heps : ∀ β, (m.epsP β).speed = (epsSpeed β).eval P) (hmu : ∀ β, (m.muP β).speed = (muSpeed β).eval P) :
    Bridge.HasMeasurableBoundData m T.bounds where
  eps_speed_measurable β := by
    rw [heps β]
    exact (hcb P (epsSpeed β)).1
  mu_speed_measurable β := by
    rw [hmu β]
    exact (hcb P (muSpeed β)).1
  amplitudes_measurable β :=
    ⟨(hcb T.chart (T.ampW β)).1, (hcb T.chart (T.ampGradW β)).1, (hcb T.chart (T.ampVort β)).1,
      (hcb T.chart (T.ampGradVort β)).1⟩
  sups_measurable := ⟨(hcb T.chart T.supVort).1, (hcb T.chart T.supGradVort).1⟩

theorem boundsMeasurable_of_entry (hcb : ScalarShape.ChartBoundFacts) {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM) (B : BoundValuesEntry D) (hB : IsBoundValuesEntry D B) :
    ∀ q ∈ D.cert.params, Bridge.HasMeasurableBoundData (D.pieces q) (D.bounds q) := by
  intro q hq
  rw [hB.bounds_eq q hq]
  exact measurableBoundData_of_valueSets hcb (D.pieces q) (B.valueSets q) B.speedChart B.epsSpeed B.muSpeed
    (hB.eps_speed_eq q hq) (hB.mu_speed_eq q hq)

end GivenShape

end CertCell

end Breakdown
