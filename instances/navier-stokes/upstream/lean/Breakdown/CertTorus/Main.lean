import Breakdown.CertTorus.TopStatements
import Breakdown.CertTorus.SmoothFieldClosed
import Breakdown.CertTorus.IntegralEquationClosed
import Breakdown.CertTorus.FarFieldDecayClosed

namespace Breakdown.FarField

theorem periodicLerayProfileExists_of_weak :
    WeakPeriodicSimilarityProfileExists → PeriodicSimilarityProfileExists :=
  periodicLerayProfileExists_of_weak_of_parts smoothFieldOfOrbit_holds integralEquationOfOrbit_holds
    farFieldDecay_holds

theorem breakdownOnTorus_of_weak : WeakPeriodicSimilarityProfileExists → BreakdownOnTorus :=
  breakdownOnTorus_of_weak_of_parts smoothFieldOfOrbit_holds integralEquationOfOrbit_holds
    farFieldDecay_holds

end Breakdown.FarField
