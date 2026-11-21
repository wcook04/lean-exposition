import Breakdown.FracCell.GivenChartDefs
import Breakdown.FracCell.Defs
import Breakdown.FracCell.StatementDefs

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace ProfileData

variable {k : ℕ} (D : ProfileData k)

def tangentField (i : Fin k) (y : Space) : Space :=
  fderiv ℝ (fun q : Fin k → ℝ => D.profile q y) 0 (Pi.single i 1)

end ProfileData

end GivenFields

end CellCert

end Breakdown
