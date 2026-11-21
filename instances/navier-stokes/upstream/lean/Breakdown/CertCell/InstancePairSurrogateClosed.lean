import Breakdown.CertCell.InstancePairSurrogate
import Breakdown.CertCell.InstancePairGradModes
import Breakdown.CertCell.InstancePairByParts
import Breakdown.CertCell.InstanceRegular

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

theorem pairSharesFromSurrogateProfiles_holds : PairSharesFromSurrogateProfiles :=
  pairSharesFromSurrogateProfiles Instance.cellMatFieldRegular actuatorGradientModes halfPlanePairing
    (actuatorPairingByParts actuatorGradientModes)

end InstancePair

end CertCell

end Breakdown
