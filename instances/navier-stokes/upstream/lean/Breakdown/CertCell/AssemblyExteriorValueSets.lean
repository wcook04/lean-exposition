import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.ShapeScalarStatements
import Breakdown.CertCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

def ExteriorValuesChargeHolds : Prop :=
  ScalarShape.ChartBoundFacts →
    ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (Tb : FarFieldValueSets), FarFieldConditions D Tb →
      IsRegionChargeBound D.azimuthOrder (D.mesh.exterior ∩ halfPlane) D.given D.givenHess (D.charges none)

end Assembly

end CertCell

end Breakdown
