import Breakdown.FracCell.SharpRowIdentity
import Breakdown.FracCell.ModeGradSquare
import Breakdown.FracCell.ModeVelSquare

namespace Breakdown

namespace CellCert

namespace CellAnalysis

theorem fieldModeSquare_holds : FieldModeSquareStatement := fun K hK m v G H hs n =>
  ⟨fun i q => modeGradSquare K hK m v G H hs n i q, fun i => modeVelSquare K hK m v G H hs n i⟩

end CellAnalysis

end CellCert

end Breakdown
