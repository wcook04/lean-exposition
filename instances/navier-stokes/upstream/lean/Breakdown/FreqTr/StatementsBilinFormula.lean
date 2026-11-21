import Breakdown.FreqTr.StatementsExport

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

def BilinH1Formula : Prop :=
  ∀ f, IsH1Field f → (∃ C, ∀ x, ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C) → ∀ τ, 0 < τ →
    bilinX τ (embedX f) (embedX f) = -heatDivFree τ (toLpOrZero 2 (fun x => advectionAt f x))

end Breakdown.Freq
