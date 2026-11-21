import Breakdown.CertCell.AssemblyPotentialEpsCore
import Breakdown.CertCell.AssemblyPotentialSharpRegular

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

theorem epsResolvedStage_holds : EpsResolvedStageHolds :=
  epsResolvedStage_holds_of Internal.Sharp.sharpRegular

end Assembly

end CertCell

end Breakdown
