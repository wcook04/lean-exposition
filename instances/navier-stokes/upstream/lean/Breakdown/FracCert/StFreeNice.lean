import Breakdown.FracCert.StFree
import Breakdown.Frac.StRealize

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

def FreeExistsNiceStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (s : Space → Freq.CSpace), Freq.IsNiceSymbol s →
    IsClassField m (Freq.niceField s) →
    ∃ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
      (P : Space → Space), IsSecondOrderField m v G H ∧ IsWeakFractionalPower α v P ∧
      MemLp (driftField α a v G) 2 volume ∧ ∀ᵐ y ∂volume, driftField α a v G y + P y = Freq.niceField s y

def NiceClassDenseStatement : Prop :=
  ∀ (m : ℕ) (F : Space → Space), IsSolenoidalL2 F → IsClassField m F → ∀ ε : ℝ, 0 < ε →
    ∃ s : Space → Freq.CSpace, Freq.IsNiceSymbol s ∧ IsClassField m (Freq.niceField s) ∧
      ∫ y, ‖F y - Freq.niceField s y‖ ^ 2 < ε

end SteadyCert

end Breakdown
