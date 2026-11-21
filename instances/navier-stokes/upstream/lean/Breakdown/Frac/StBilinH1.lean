import Breakdown.Frac.StRealize
import Breakdown.FreqTr.H1Consistency

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Freq

def FracBilinH1Formula (α : ℝ) : Prop :=
  ∀ f, IsH1Field f → (∃ C, ∀ x, ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C) → ∀ τ, 0 < τ →
    fracBilinX α τ (embedX f) (embedX f) = -fracHeatSolenoidal α τ (toLpOrZero 2 (fun x => advectionAt f x))

end Breakdown.Freq
