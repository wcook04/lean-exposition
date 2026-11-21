import Breakdown.FracCell.Defs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

def CentreIdentityStatement : Prop :=
  ∀ (α : ℝ) {k N : ℕ} (c : FracCellData k N), IsFracCell α c →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField c.order v G H →
      l2Pair (fun y => (2 : ℝ) • symProduct c.centre c.centreGrad v G y) (negSecondTrace H)
          = ∫ y, jForm (c.centreStrain y) (c.centreCurlGrad y) (G y) (v y)

end CellCert

end Breakdown
