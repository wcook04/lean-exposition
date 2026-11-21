import Breakdown.Torus.StatementsCoeff
import Breakdown.Frac.StOperator

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def PlaneWaveEigen (α : ℝ) : Prop :=
  ∀ (ξ c : Space) (φ₀ : ℝ) (x : Space),
    fractionalPowerAt α (fun y => Real.cos (inner ℝ ξ y + φ₀) • c) x =
      (‖ξ‖ ^ (2 * α) * Real.cos (inner ℝ ξ x + φ₀)) • c

def PeriodicSymmetry (α : ℝ) : Prop :=
  ∀ f g : Space → Space, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → IsPeriodic f → IsPeriodic g →
    IntegrableOn (fractionalPowerAt α f) cell ∧
      ∫ x in cell, inner ℝ (fractionalPowerAt α f x) (g x) =
        ∫ x in cell, inner ℝ (f x) (fractionalPowerAt α g x)

def CoefFractional (α : ℝ) : Prop :=
  ∀ f : Space → Space, ContDiff ℝ ∞ f → IsPeriodic f → ∀ k : Lattice,
    freqTrCoef (fractionalPowerAt α f) k = ((2 * π * ‖freq k‖) ^ (2 * α) : ℝ) • freqTrCoef f k

end Breakdown.Periodic
