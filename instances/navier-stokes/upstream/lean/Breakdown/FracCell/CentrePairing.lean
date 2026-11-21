import Breakdown.FracCell.ModelForm
import Breakdown.FracCell.StCentrePairing
import Breakdown.FracCell.CentrePairingCentre
import Breakdown.FracCell.CentrePairingActuator

noncomputable section

namespace Breakdown

namespace CellCert

theorem centrePairing_of (h : CentreIdentityStatement) : CentrePairingStatement :=
  fun α _ _ c hc v G H hs => ⟨h α c hc v G H hs, fun i => actuatorPairing α c hc hs i⟩

theorem centrePairing : CentrePairingStatement := centrePairing_of centreIdentity

end CellCert

end Breakdown
