import Breakdown.Defs

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

def secondOrderRemainder (f : Space → Space) (x z : Space) : Space :=
  f (x + z) - f x - fderiv ℝ f x z - (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]

def fractionalNormalizer (α : ℝ) : ℝ :=
  ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (z 0) - 1 + (z 0) ^ 2 / 2)

def fractionalPowerAt (α : ℝ) (f : Space → Space) (x : Space) : Space :=
  (fractionalNormalizer α)⁻¹ • ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder f x z

structure IsFractionalSolution (α ν : ℝ) (u₀ : Space → Space)
    (u : ℝ → Space → Space) (p : ℝ → Space → ℝ) : Prop where
  smooth_velocity : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Set.Ici 0 ×ˢ Set.univ)
  smooth_pressure : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (Set.Ici 0 ×ˢ Set.univ)
  initial : ∀ x, u 0 x = u₀ x
  momentum : ∀ t > 0, ∀ x,
    deriv (fun τ => u τ x) t + advectionAt (u t) x + ν • fractionalPowerAt α (u t) x =
      -gradientAt (p t) x
  incompressible : ∀ t > 0, ∀ x, divergenceAt (u t) x = 0

def FractionalBreakdownOnSpace (α : ℝ) : Prop :=
  ∀ ν > 0, ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
    (∀ x, divergenceAt u₀ x = 0) ∧
    ¬ ∃ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ), IsFractionalSolution α ν u₀ u p ∧
      ∃ C : ℝ, ∀ t ≥ 0, ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ 2) ≤ ENNReal.ofReal C

def FractionalBreakdownOnTorus (α : ℝ) : Prop :=
  ∀ ν > 0, ∃ u₀ : Space → Space, ContDiff ℝ ∞ u₀ ∧
    (∀ i x, u₀ (x + unitVector i) = u₀ x) ∧ (∀ x, divergenceAt u₀ x = 0) ∧
    ¬ ∃ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ), IsFractionalSolution α ν u₀ u p ∧
      ∀ t ≥ 0, ∀ i x, u t (x + unitVector i) = u t x

def axialTurn (y : Space) : Space :=
  EuclideanSpace.single 0 (-(y 1)) + EuclideanSpace.single 1 (y 0)

def rotatingProfileResidual (α a ν : ℝ) (U : Space → Space) (P : Space → ℝ) (y : Space) :
    Space :=
  (1 - 1 / (2 * α)) • U y + (1 / (2 * α)) • fderiv ℝ U y y
    + a • (fderiv ℝ U y (axialTurn y) - axialTurn (U y))
    + ν • fractionalPowerAt α U y + advectionAt U y + gradientAt P y

def RotatingFractionalProfileExists (α : ℝ) : Prop :=
  ∃ (U : Space → Space) (P : Space → ℝ) (a ν : ℝ), 0 < ν ∧
    ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ P ∧ ContDiff ℝ ∞ (fractionalPowerAt α U) ∧
    (∀ y, rotatingProfileResidual α a ν U P y = 0) ∧
    (∀ y, divergenceAt U y = 0) ∧
    (∃ y, U y ≠ 0) ∧
    ∀ j : ℕ, ∃ C : ℝ, ∀ y : Space,
      ‖iteratedFDeriv ℝ j U y‖ ≤ C * (1 + ‖y‖) ^ (-(2 * α - 1 + j)) ∧
      ‖iteratedFDeriv ℝ (j + 1) P y‖ ≤ C * (1 + ‖y‖) ^ (-(4 * α - 1 + j)) ∧
      ‖iteratedFDeriv ℝ j (fractionalPowerAt α U) y‖ ≤ C * (1 + ‖y‖) ^ (-(4 * α - 1 + j))

end Breakdown
