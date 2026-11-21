import Breakdown.Profile.Dilate
import Breakdown.Profile.DilateDecay
import Breakdown.Profile.Parts
import Breakdown.Profile.Slice
import Breakdown.Profile.SliceContinuity
import Breakdown.Profile.TimeDeriv
import Breakdown.Profile.Momentum
import Breakdown.Profile.Difference
import Breakdown.Profile.L2
import Breakdown.Profile.PairingDeriv
import Breakdown.Profile.Weak
import Breakdown.Profile.Mild
import Breakdown.Profile.FrameAlgebra
import Breakdown.Profile.ChangeOfVariables
import Breakdown.Profile.FlowMild
import Breakdown.Profile.OrbitParts

noncomputable section

namespace Breakdown

theorem physicalMild_unconditional : PhysicalMild :=
  physicalMild_holds (decayFieldDilate_holds dilateCalculus_holds) sliceDecay_holds
    (physicalL2_holds (physicalDifference_holds physicalTimeDeriv_holds similarityDerivBound_holds))
    (physicalWeak_holds
      (physicalPairingDeriv_holds physicalTimeDeriv_holds
        (physicalMomentum_holds physicalTimeDeriv_holds dilateCalculus_holds gradientScale_holds)
        similarityDerivBound_holds)
      sumSecondPartialsPairing_holds gradientPairingZero_holds)
    dilateJointContinuous_holds

theorem flowOfMild_unconditional : FlowOfMild :=
  flowOfMild_holds kernelDilate_holds expChangeOfVariables_holds

theorem embeddedProfileOrbit_holds : EmbeddedProfileOrbit :=
  embeddedOrbitOfParts_holds decayFieldSub_holds sliceDecay_holds sliceGradientContinuous_holds
    physicalMild_unconditional flowOfMild_unconditional

theorem profileOrbit_holds : ProfileOrbitHolds :=
  orbitOfParts_holds decayFieldSub_holds sliceDecay_holds sliceGradientContinuous_holds
    physicalMild_unconditional flowOfMild_unconditional

end Breakdown
