import Breakdown.CertCell.RowLowPartCore
import Breakdown.CertCell.RowLowPartBasis
import Breakdown.CertCell.LabelRowProfileSsp
import Breakdown.CertCell.LabelRowProfilePressure

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

theorem rowLowPart_holds (h1 : HarmonicLiftStatement) (h2 : HarmonicPressureLiftStatement)
    (h3 : HarmonicSideDataStatement) : RowLowPartStatement :=
  rowLowPart_of_parts segmentTestExpansion cellBasisExpansion h1 h2 h3
    (fun K hK m v G H Pg hv ι hax φ hφ => labelRowProfile_sumSecondPartials h1 K hK m v G H Pg hv ι hax φ hφ)
    (fun K hK m v G H Pg hp ι hax φ hs hφ => labelRowProfile_pressure h2 K hK m v G H Pg hp ι hax φ hs hφ)

end CellCalculus

end CertCell

end Breakdown
