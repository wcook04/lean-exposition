import Breakdown.FracCert.StFreeNiceParts
import Breakdown.Frac.StProfile

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

def axialRotationC (θ : ℝ) (z : Freq.CSpace) : Freq.CSpace :=
  EuclideanSpace.single 0 ((Real.cos θ : ℂ) * z 0 - (Real.sin θ : ℂ) * z 1) +
    EuclideanSpace.single 1 ((Real.sin θ : ℂ) * z 0 + (Real.cos θ : ℂ) * z 1) + EuclideanSpace.single 2 (z 2)

def freeWeight (α : ℝ) (τ : ℝ) (ξ : Space) : ℝ :=
  Real.exp (-((1 - 2 / α) * τ)) * Real.exp (-((Real.exp τ - 1) * freqPow (2 * α) ξ))

def freeSolution (α a : ℝ) (s : Space → Freq.CSpace) (ξ : Space) : Freq.CSpace :=
  ∫ τ in Set.Ioi (0 : ℝ), freeWeight α τ ξ •
    axialRotationC (a * τ) (s (Real.exp (τ / (2 * α)) • axialRotationFormula (-(a * τ)) ξ))

def FreeSolutionSmoothStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (s : Space → Freq.CSpace), Freq.IsNiceSymbol s →
    ContDiffOn ℝ ∞ (freeSolution α a s) {ξ | ξ ≠ 0}

def FreeSolutionBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (s : Space → Freq.CSpace), Freq.IsNiceSymbol s →
    ∀ j : ℕ, ∃ C : ℝ, ∀ ξ : Space, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ j (freeSolution α a s) ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 4 - (j : ℝ))

def FreeSolutionSmallBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (s : Space → Freq.CSpace), Freq.IsNiceSymbol s →
    ∀ j : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ ξ : Space, ξ ≠ 0 → ‖ξ‖ < ρ →
      ‖iteratedFDeriv ℝ j (freeSolution α a s) ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 4 - (j : ℝ))

def FreeSolutionEquationStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (s : Space → Freq.CSpace), Freq.IsNiceSymbol s →
    ∀ ξ : Space, ξ ≠ 0 → profileSymbolLhs α a (freeSolution α a s) ξ = s ξ

def FreeSolutionClassStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (s : Space → Freq.CSpace), Freq.IsNiceSymbol s →
    IsClassField m (Freq.niceField s) → IsClassField m (Freq.niceField (freeSolution α a s))

end SteadyCert

end Breakdown
