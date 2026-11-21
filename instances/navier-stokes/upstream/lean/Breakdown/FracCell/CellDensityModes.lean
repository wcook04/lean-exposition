import Breakdown.FracCell.CellDensityModesCoupling
import Breakdown.FracCell.CellDensityModesTurn

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

theorem cellDensityModes_of (h₃ : DensitySliceStatement) : CellDensityModesStatement :=
  cellDensityModes_of_parts (densityIntegrable_of jFormIntegrable) (densityMirror_of gradientMirror) h₃

end CellAnalysis

end CellCert

end Breakdown
