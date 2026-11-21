import Breakdown.FracCert.StHeldParts
import Breakdown.FracCert.StFree

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

def ProductSquareStatement : Prop :=
  ∀ (m : ℕ) (u : Space → Space) (Gu : Space → (Space →L[ℝ] Space))
    (Hu : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (w : Space → Space) (Gw : Space → (Space →L[ℝ] Space))
    (Hw : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m u Gu Hu →
    IsSecondOrderField m w Gw Hw → MemLp (symProduct u Gu w Gw) 2 volume

def GradientDifferenceStatement : Prop :=
  ∀ Q Q' : Space → Space, IsGradientField Q → IsGradientField Q' → IsGradientField (fun y => Q y - Q' y)

def WeakPowerDifferenceStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P u : Space → Space) (K : Space → (Space →L[ℝ] Space))
    (L : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (R : Space → Space),
    IsSecondOrderField m v G H → IsSecondOrderField m u K L → IsWeakFractionalPower α v P →
    IsWeakFractionalPower α u R → IsWeakFractionalPower α (fun y => v y - u y) (fun y => P y - R y)

end SteadyCert

end Breakdown
