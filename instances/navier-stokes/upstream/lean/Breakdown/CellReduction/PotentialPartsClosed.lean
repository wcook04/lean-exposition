import Breakdown.CellReduction.PotTheta
import Breakdown.CellReduction.PotPhi
import Breakdown.CellReduction.PotScalarOff
import Breakdown.CellReduction.PotScalarOrigin
import Breakdown.CellReduction.PotScalarDecay
import Breakdown.CellReduction.PotFlux
import Breakdown.CellReduction.PotFluxDivergence
import Breakdown.CellReduction.PotFluxRadial
import Breakdown.CellReduction.PotFluxPolar
import Breakdown.CellReduction.PotFluxDecay
import Breakdown.CellReduction.PotPressure
import Breakdown.CellReduction.PotPressureWeak
import Breakdown.CellReduction.PotPressureDecay
import Breakdown.CellReduction.PotCell
import Breakdown.CellReduction.PotGenerator
import Breakdown.CertCell.CellLayerClosed
import Breakdown.CertCell.ShapeSupportRadius
import Breakdown.CertCell.InstanceRegular

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect

theorem radialFluxPartWeak_holds : RadialFluxPartWeak :=
  fun P F hP hF κ hκ c σ => radialFluxPart_weakDivergence P F hP hF κ hκ c σ

theorem polarFluxPartWeak_holds : PolarFluxPartWeak :=
  fun P F hP hF κ hκ c σ => polarFluxPart_weakDivergence P F hP hF κ hκ c σ

theorem potentialParts_holds : PotentialPieces where
  theta := thetaPotentialRegular_of scalarSmoothAwayFromOrigin scalarSmoothNearOrigin
    (scalarDecayOrder_of scalarSmoothAwayFromOrigin scalarSmoothNearOrigin 2)
  phi := phiPotentialRegular_of scalarSmoothAwayFromOrigin scalarSmoothNearOrigin
    (scalarDecayOrder_of scalarSmoothAwayFromOrigin scalarSmoothNearOrigin 1)
  flux := fluxPotentialRegular_of
    (fun P F hP hF σ => fluxMap_weakMatrixDivergence_of radialFluxPartWeak_holds polarFluxPartWeak_holds P F hP hF σ)
    fluxMap_measurable_decay
  pressure := pressurePotentialRegular_of pressureValue_measurable_weak pressureValue_decay_bounds
  cell := cellPotentialRegular_holds
  generator := compactFieldSecondRegular_holds
  field_smooth := fieldJointSmooth_of typeOneKeySmooth_closed typeTwoKeySmooth_closed
  support := compactFieldSupportRadius_holds
  pin_cells := Instance.cellMatFieldRegular

end PotentialShape

end Breakdown
