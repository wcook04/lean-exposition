import Breakdown.Uniqueness.Main
import Breakdown.Uniqueness.RegGlue
import Breakdown.FreqTr.Realization
import Breakdown.Transfer.Exports
import Breakdown.Spectral.RealDichotomy
import Breakdown.Profile.Orbit

open MeasureTheory

noncomputable section

namespace Breakdown

theorem fieldReading_realization : FieldReading Freq.realization Freq.velocity where
  injective := Freq.velocityInjective_holds
  rot := Freq.velocityCov_holds.1
  dil := Freq.velocityCov_holds.2

theorem mildRegular_realization : MildRegular Freq.realization Freq.velocity :=
  SmoothFlow.mildRegular_of_freq Freq.realization (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    Freq.heat_holds Freq.fieldOpRealized_holds Freq.h1Consistency_holds Freq.bilinH1Formula_holds
    Freq.bilin_holds.1 Freq.bilin_holds.2

theorem breakdownOnSpace_of_profile : PeriodicSimilarityProfileExists → BreakdownOnSpace :=
  breakdownOnSpace_of_exports (transferHolds_of_dichotomy dichotomyHolds) profileOrbit_holds
    Freq.realization Freq.velocity fieldReading_realization mildRegular_realization

end Breakdown
