import Breakdown.FracCert.StWeak
import Breakdown.FracCert.StatementsSmooth

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

def HasAllSymbolL1Moments (f : Space → CSpace) : Prop :=
  ∀ j : ℕ, Integrable (fun ξ => (1 + ‖ξ‖) ^ j * ‖f ξ‖)

def SymbolL1OfMomentsStatement : Prop :=
  ∀ x : X, HasAllMoments x → HasAllSymbolL1Moments (symbolX x) ∧
    (velocity x : Space → Space) =ᵐ[volume] physField (symbolX x)

def FieldSmoothOfMomentsStatement : Prop :=
  ∀ f : Space → CSpace, HasAllSymbolL1Moments f → (∀ ξ, f (-ξ) = conjVec (f ξ)) →
    ContDiff ℝ ∞ (physField f) ∧ ∀ j : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (physField f) y‖ ≤ C

def WeakProfileRegularStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ContDiff ℝ ∞ (physField (symbolX U)) ∧ (∀ y, divergenceAt (physField (symbolX U)) y = 0) ∧
    ∃ P : Space → ℝ, ContDiff ℝ ∞ P ∧ ∀ y, rotatingProfileResidual α a 1 (physField (symbolX U)) P y = 0

def LowFrequencyRemovalStatement : Prop :=
  ∀ Θ : Space → Space, Continuous Θ → MemLp (fun y => (1 + ‖y‖)⁻¹ • Θ y) 2 volume →
    (∀ m : Space → CSpace, (∀ ξ, m (-ξ) = conjVec (m ξ)) → ContDiff ℝ ∞ m →
      HasCompactSupport m → (∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → m ξ = 0) →
      ∫ y, inner ℝ (Θ y) (physField m y) = 0) → ∀ y, Θ y = 0

end Breakdown.FracCert
