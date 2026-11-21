import Breakdown.FracCell.StrainFaceFaceTraceFree
import Breakdown.FracCell.RadialTrace

noncomputable section

namespace Breakdown.CellCert.CellFormula

theorem axisGradModeIntegrable_holds : AxisGradModeIntegrableStatement := by
  intro m v G H hs K hK _ n a b
  exact Breakdown.CellCert.CellEnergy.RadialTraceInternal.grad_int hs K hK a b n

end Breakdown.CellCert.CellFormula
