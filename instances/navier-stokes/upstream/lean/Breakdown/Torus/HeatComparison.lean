import Breakdown.Torus.HeatComparisonStep
import Breakdown.Torus.HeatComparisonPartition
import Breakdown.Torus.HeatComparisonSeries
import Breakdown.Torus.HeatComparisonCoef
import Breakdown.Torus.HeatComparisonTorusSide
import Breakdown.Torus.HeatComparisonProj
import Breakdown.Torus.HeatComparisonInverse
import Breakdown.Torus.HeatComparisonFreeR3
import Breakdown.Torus.HeatComparisonDensity
import Breakdown.Torus.HeatComparisonFreeDensity
import Breakdown.Torus.HeatComparisonAssembly
import Breakdown.Torus.HeatComparisonFreeAssembly

noncomputable section

namespace Breakdown.Periodic

theorem heatDivFreeComparison (h1 : Freq.FieldOpRealized) (h2 : Freq.FreqTrL1L2) (h3 : Freq.FreqTrConjSym)
    (h4 : Freq.VelocityInvertsHalfSsp) (h5 : Freq.FreqTrInvL1L2) : HeatDivFreeComparison :=
  heatDivFreeComparison_of (partitionSumBound_of_step stepIntegral)
    (torusSourceSeries_of torusSeriesPointwise sourceCoefFormula)
    (r3ValueFormula_of (heatDivFreeFactor h1 h2 h3) h1 h4 h5) sourceDensityBounds sourceDensitySlope

theorem freeHeatComparison (hD : CoefDeriv) (hTS : TransplantSmooth) (h1 : Freq.FieldOpRealized)
    (h2 : Freq.HeatSemigroup) (h3 : Freq.VelocityInvertsHalfSsp) (h4 : Freq.FreqTrInvL1L2)
    (h5 : Freq.FreqTrL1L2) (h6 : Freq.FreqTrConjSym) : FreeHeatComparison :=
  freeHeatComparison_of (partitionSumBound_of_step stepIntegral)
    (torusFreeSeries_of torusSeriesPointwise transplantCoefFormula hD hTS stepIntegral freeDensityBounds)
    (r3FreeFormula h1 h2 h3 h4 h5 h6) freeDensityBounds freeDensitySlope

end Breakdown.Periodic
