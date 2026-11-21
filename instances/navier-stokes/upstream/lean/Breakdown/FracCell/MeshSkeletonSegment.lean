import Breakdown.FracCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

namespace MeshSkeletonInternal

def keySegment (rad : Bool) (lev lo hi : ℝ) (t : ℕ → ℕ → ℝ) : FaceSegment := ⟨rad, lev, lev + 1, lo, hi, t⟩

end MeshSkeletonInternal

end Breakdown.CellCert.CellCoordinates

end
