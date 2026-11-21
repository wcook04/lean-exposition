import Breakdown.FracCell.CellDataDefs
import Breakdown.FracCell.FormulaDefs
import Breakdown.FracCell.MeshDefs
import Breakdown.FracCell.SpectralDefs
import Breakdown.FracCell.ReductionLossDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis

namespace CellMesh

variable (M : CellMesh)

end CellMesh

namespace ModelData

variable {M : CellMesh} {k : ℕ} (D : ModelData M k) (m : ℕ)

end ModelData

structure IsCentreRegular {k N : ℕ} (c : FracCellData k N) : Prop where
  smooth : ContDiff ℝ 1 c.centre
  second_measurable : AEStronglyMeasurable c.centreSecond volume
  second_symm : ∀ y (u w : Space), c.centreSecond y u w = c.centreSecond y w u

end GivenModel

namespace GivenModel

open SteadyCert CellAnalysis

namespace RowData

variable {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ)

open Classical in
def pairSign (a : Fin N) : ℝ := if R.positive a then 1 else -1

def turnMode (a : Fin N) : ℤ := (if R.positive a then 1 else -1) * ((m : ℤ) * (R.harmonic a : ℤ))

end RowData

end GivenModel

namespace GivenModel

open SteadyCert CellAnalysis CellFormula

end GivenModel

end CellCert

end Breakdown
