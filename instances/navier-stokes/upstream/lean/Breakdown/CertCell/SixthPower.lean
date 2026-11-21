import Breakdown.CertCell.TripleSlice
import Breakdown.CertCell.LineGradient
import Breakdown.CertCell.ThreeHalves
import Breakdown.CertCell.SmoothSixthPower
import Breakdown.CertCell.SixthPowerWeak

namespace Breakdown

theorem sixthPowerGradientBound_four_thirds : SixthPowerGradientBound (4 / 3) :=
  sixthPowerGradientBound_of (by norm_num)
    (smoothSixthPowerBound_of (threeHalvesGradientBound_of tripleSliceBound lineGradientBound))

end Breakdown
