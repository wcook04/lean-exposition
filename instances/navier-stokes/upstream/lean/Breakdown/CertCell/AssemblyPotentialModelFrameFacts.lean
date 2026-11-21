import Breakdown.CertCell.AssemblyPotentialModelFrameFactsAlgebra
import Breakdown.CertCell.AssemblyPotentialModelFrameFactsModel
import Breakdown.CertCell.AssemblyPotentialModelFrameFactsSection
import Breakdown.CertCell.AssemblyPotentialModelFrameFactsGiven

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

theorem frameFacts : FrameFacts where
  model_field := modelFieldFrame
  strain := strainFrame
  vorticity_grad := vorticityGradFrame
  rotated_bound := rotatedBound
  orbit_solid := orbitSolid
  grad_section := gradSection
  secondDeriv_section := secondDerivSection
  given_expansion := givenExpansion

end Internal

end Assembly

end CertCell

end Breakdown
