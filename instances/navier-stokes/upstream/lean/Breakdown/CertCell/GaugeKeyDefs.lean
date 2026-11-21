import Breakdown.FracCell.MeshDefs
import Breakdown.FracCell.MeshSkeletonPair
import Breakdown.CertCell.StatementDefs

noncomputable section

namespace Breakdown.CertCell.GaugeKey

open Breakdown.CellCert.CellCoordinates Breakdown.CellCert.CellFormula
open Breakdown.CellCert.CellCoordinates.MeshSkeletonInternal

namespace GaugeKeyValues

variable (G : GaugeKeyValues)

def inverse : Matrix (Fin G.count) (Fin G.count) ℂ :=
  fun c e => (G.incidenceInv c e : ℂ) / (G.deletedWeight e : ℂ)

end GaugeKeyValues

end Breakdown.CertCell.GaugeKey
