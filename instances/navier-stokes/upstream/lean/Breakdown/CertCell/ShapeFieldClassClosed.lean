import Breakdown.CertCell.ShapeFieldClass
import Breakdown.CertCell.ShapeKeyFlip

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

theorem fieldClassInvariant_holds : FieldClassInvariant :=
  fieldClassInvariant_of_keyFlip keyFlip_holds

end GivenShape

end CertCell

end Breakdown
