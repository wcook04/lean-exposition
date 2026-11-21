import Breakdown.CellReduction.InstanceStatements

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

theorem profileSplit_holds : ProfileSplitHolds := by
  intro k C nE nM D R hR q σ y
  rw [hR.profile_eq q]
  rfl

end Instantiation

end CellReduction

end Breakdown
