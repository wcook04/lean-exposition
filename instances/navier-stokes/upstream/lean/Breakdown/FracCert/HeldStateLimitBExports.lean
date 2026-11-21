import Breakdown.FracCert.HeldStateLimitB
import Breakdown.FracCert.SecondOrderWeakLimit
import Breakdown.FracCert.WeakPowerLimit
import Breakdown.FracCert.DriftWeakLimit
import Breakdown.FracCert.HeldResidualLimit
import Breakdown.FracCert.DriftPowerSolenoidal

namespace Breakdown

namespace SteadyCert

theorem heldStateLimit_b (hs : DriftPowerSolenoidalStatement) : HeldStateLimitStatement :=
  heldStateLimit_of_bounds (heldUniformBound_of hs) (heldBoundedLimit_of (heldLimitIdentify_of
    (heldLimitClosure_of secondOrderWeakLimit_holds weakPowerLimit_holds driftWeakLimit_holds
      heldResidualLimit_holds)))

theorem heldStateLimitProved : HeldStateLimitStatement := heldStateLimit_b driftPowerSolenoidal

end SteadyCert

end Breakdown
