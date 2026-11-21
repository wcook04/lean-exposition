import Breakdown.FracCell.AxisLiftDeriv

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

theorem axisLift : AxisLiftStatement :=
  axisLift_of_parts liftSlope_holds liftDeriv_holds

end Spectral

end CellCert

end Breakdown
