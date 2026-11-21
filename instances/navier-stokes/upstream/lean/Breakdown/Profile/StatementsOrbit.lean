import Breakdown.Profile.StatementsPhysical
import Breakdown.Profile.StatementsFlow

open MeasureTheory Set Real

noncomputable section

namespace Breakdown

def OrbitOfParts : Prop :=
  DecayFieldSub → SliceDecay → SliceGradientContinuous → PhysicalMild → FlowOfMild →
    ProfileOrbitHolds

end Breakdown
