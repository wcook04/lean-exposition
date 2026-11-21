import Breakdown.CellReduction.ConvectionIdentity
import Breakdown.CellReduction.ProfileFieldApprox

namespace Breakdown

namespace CertReduction

theorem convectionIdentity_holds : ConvectionIdentityHolds :=
  convectionIdentityHolds_of_approx (fun _ _ _ _ h => profileFieldApprox h)

end CertReduction

end Breakdown
