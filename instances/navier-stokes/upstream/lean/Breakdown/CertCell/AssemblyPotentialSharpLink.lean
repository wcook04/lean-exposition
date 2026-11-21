import Breakdown.CertCell.AssemblyPotentialSharpAbsorb
import Breakdown.CertCell.AssemblyPotentialSharpRegular

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

theorem absorbSplitStatement : Internal.Sharp.AbsorbSplitStatement := by
  intro k C nE nM D R A P states hreg htrue hchk hLT K q v G H g κ F Pg ht ζ η
  exact Internal.Sharp.absorb_split D R A P hreg htrue hchk hLT K q v G H g κ F Pg ht ζ η

theorem sharpStageHolds : SharpStageHolds :=
  Internal.Sharp.sharpStageHolds_of absorbSplitStatement Internal.Sharp.sharpRegular

end Assembly

end CertCell

end Breakdown
