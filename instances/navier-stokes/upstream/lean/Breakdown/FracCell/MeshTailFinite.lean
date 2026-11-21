import Breakdown.FracCell.MeshTailModes
import Breakdown.FracCell.MeshTailCoef
import Breakdown.FracCell.MeshTailAngle

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

theorem tailFinite_holds : TailFiniteStatement := MeshTail.tailFinite_of coefMode_holds angleTail_holds

end CellAnalysis

end CellCert

end Breakdown
