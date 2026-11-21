import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.AssemblyAnnihilatorGradientClosure

noncomputable section

namespace Breakdown.CertCell.Assembly

theorem annihilatorGradient_holds : AnnihilatorGradientHolds :=
  fun Q hQm hQ2 hann => AnnihilatorGradient.Internal.gradient_of_annihilator Q hQm hQ2
    (fun φ h1 h2 h3 => hann φ ⟨h1, h2, h3⟩)

end Breakdown.CertCell.Assembly
