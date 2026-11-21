import Breakdown.CertCell.BridgeTraceStatements
import Breakdown.FracCell.MeshGaugeLinearPotential

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

theorem potentialOfGradient : PotentialOfGradientHolds :=
  fun Q hQ => CellCert.CellFormula.MeshGaugeLinearPotential.potentialOf_spec Q hQ

end SideTrace

end CertCell

end Breakdown
