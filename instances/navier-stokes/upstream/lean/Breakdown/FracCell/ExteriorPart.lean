import Breakdown.FracCell.StExterior

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Exterior

open SteadyCert Assembly

theorem exteriorPartNonneg_of (h1 : ExteriorNonnegStatement) : ExteriorPartNonnegStatement := by
  intro α hα1 hα2 k N c hc e he S hcover x hx
  unfold CellSplit.exteriorPart
  rw [hcover]
  exact h1 α hα1 hα2 c hc e he x hx

end Exterior

end CellCert

end Breakdown
