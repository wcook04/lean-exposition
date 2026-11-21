import Breakdown.FracCell.GivenProfileDefs

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

theorem rotationRate_continuous_of {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (hD : IsProfileData D) (hd : IsProfileInstance D d) :
    ContinuousOn d.rotationRate (box d.radius) := by
  rw [hd.rate_eq]
  apply Continuous.continuousOn
  unfold ProfileData.rate
  fun_prop

theorem multiplier_continuous_of {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (hD : IsProfileData D) (hd : IsProfileInstance D d) :
    ContinuousOn d.multiplier (box d.radius) := by
  rw [hd.multiplier_eq]
  apply Continuous.continuousOn
  apply continuous_pi
  intro j
  unfold ProfileData.multiplier ProfileData.monomialOf
  fun_prop

end GivenFields

end CellCert

end Breakdown
