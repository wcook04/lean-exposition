import Breakdown.FracCert.StHeld

namespace Breakdown

namespace SteadyCert

theorem certificateWeakProfile (h1 : HeldZeroStatement) (h2 : HeldWeakProfileStatement) :
    CertificateWeakProfileStatement := by
  intro α hα1 hα2 hcert
  obtain ⟨k, N, d, hd⟩ := hcert
  obtain ⟨p, hp, u, G, H, P, κ, hheld, hsize, hzero⟩ := h1 α hα1 hα2 d hd
  exact h2 α hα1 hα2 d hd p hp u G H P κ hheld hsize hzero

end SteadyCert

end Breakdown
