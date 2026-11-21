import Breakdown.CertCell.AssemblyPotentialExpand

namespace Breakdown

namespace CertCell

namespace Assembly

theorem stretchExpansionHolds : StretchExpansionHolds :=
  fun D R A P states _ hreg htrue hchk => stretchExpansion_of_modeClass D R A P states hreg htrue hchk hreg.field.mode_class

end Assembly

end CertCell

end Breakdown
