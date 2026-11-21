import Breakdown.FracCert.StWeakRegular

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

def profilePressure (U : X) : Space → ℝ := physScalar (pressureSymbol (symbolX U))

def profileResidual (α a : ℝ) (U : X) : Space → Space :=
  rotatingProfileResidual α a 1 (physField (symbolX U)) (profilePressure U)

def PressureSmoothStatement : Prop :=
  ∀ U : X, HasAllMoments U → ContDiff ℝ ∞ (profilePressure U)

def ResidualGrowthStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), HasAllMoments U →
    Continuous (profileResidual α a U) ∧
      MemLp (fun y => (1 + ‖y‖)⁻¹ • profileResidual α a U y) 2 volume

def ResidualWeightedStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), HasAllMoments U →
    MemLp (fun y => (1 + ‖y‖)⁻¹ • profileResidual α a U y) 2 volume

def VelocityInverseWeightStatement : Prop :=
  ∀ U : X, HasAllMoments U → MemLp (fun y => (1 + ‖y‖)⁻¹ • physField (symbolX U) y) 2 volume

def VelocityGradientSquareStatement : Prop :=
  ∀ U : X, HasAllMoments U → MemLp (fun y => ‖fderiv ℝ (physField (symbolX U)) y‖) 2 volume

def PowerSquareStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ U : X, HasAllMoments U →
    MemLp (fractionalPowerAt α (physField (symbolX U))) 2 volume

def AdvectionSquareStatement : Prop :=
  ∀ U : X, HasAllMoments U → MemLp (advectionAt (physField (symbolX U))) 2 volume

def PressureGradientSquareStatement : Prop :=
  ∀ U : X, HasAllMoments U → MemLp (gradientAt (profilePressure U)) 2 volume

def ResidualAnnulusStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ∀ m : Space → CSpace, (∀ ξ, m (-ξ) = conjVec (m ξ)) → ContDiff ℝ ∞ m →
      HasCompactSupport m → (∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → m ξ = 0) →
      ∫ y, inner ℝ (profileResidual α a U y) (physField m y) = 0

def ResidualNiceStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ∀ φ, IsNiceField φ → ∫ y, inner ℝ (profileResidual α a U y) (φ y) = 0

def ResidualGradientStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), HasAllMoments U →
    ∀ q : Space → CSpace, (∀ ξ, q (-ξ) = conjVec (q ξ)) → ContDiff ℝ ∞ q →
      HasCompactSupport q → (∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → q ξ = 0) →
      (∃ c : Space → ℂ, ∀ ξ, q ξ = c ξ • freqVec ξ) →
      ∫ y, inner ℝ (profileResidual α a U y) (physField q y) = 0

end Breakdown.FracCert

