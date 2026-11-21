import Breakdown.FracCert.DecayFixedPointParts

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

def FarFieldTimeSplitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (B : ℝ), Continuous F →
    (∀ y, ‖F y‖ ≤ B) → ∀ g : Space → Space, Continuous g → Integrable g →
      ∫ y, inner ℝ (farFieldOp α a F y) (g y) =
        -∫ τ in Ioi (0 : ℝ), ∫ y, inner ℝ (pushForward (axialRotation (a * τ))
          (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) F)) y) (g y)

def HeatDivGradientFreeStatement : Prop :=
  ∀ α : ℝ, 1 < α → ∀ t μ : ℝ, 0 < t → 0 < μ → ∀ (R : Space ≃ₗᵢ[ℝ] Space)
    (F : Space → Fin 3 → Fin 3 → ℝ) (B : ℝ), Continuous F → (∀ y, ‖F y‖ ≤ B) →
    ∀ q : Space → CSpace, ContDiff ℝ ∞ q → HasCompactSupport q →
      (∃ c : Space → ℂ, ∀ ξ, q ξ = c ξ • freqVec ξ) →
      ∫ y, inner ℝ (pushForward R (scaleField α μ (heatDivConv α t F)) y) (physField q y) = 0

end Breakdown.FracCert
