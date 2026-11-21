import Breakdown.Defs

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def cross (a b : Space) : Space := WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))

def partialAt (v : Space → Space) (i j : Fin 3) (x : Space) : ℝ := (fderiv ℝ v x (unitVector i)) j

def curlAt (v : Space → Space) (x : Space) : Space :=
  WithLp.toLp 2 ![partialAt v 1 2 x - partialAt v 2 1 x, partialAt v 2 0 x - partialAt v 0 2 x,
    partialAt v 0 1 x - partialAt v 1 0 x]

def homotopyPotential (x₀ : Space) (g : Space → Space) (x : Space) : Space :=
  ∫ s in (0 : ℝ)..1, s • cross (g (x₀ + s • (x - x₀))) (x - x₀)

def HomotopyCurl : Prop :=
  ∀ (x₀ : Space) (g : Space → Space), ContDiff ℝ ∞ g → (∀ x, divergenceAt g x = 0) →
    ContDiff ℝ ∞ (homotopyPotential x₀ g) ∧ ∀ x, curlAt (homotopyPotential x₀ g) x = g x

def cutoffField (χ : Space → ℝ) (x₀ : Space) (g : Space → Space) (x : Space) : Space :=
  χ x • g x + cross (gradientAt χ x) (homotopyPotential x₀ g x)

def CutoffDivergenceFree : Prop :=
  ∀ (χ : Space → ℝ) (x₀ : Space) (g : Space → Space), ContDiff ℝ ∞ χ → ContDiff ℝ ∞ g →
    (∀ x, divergenceAt g x = 0) →
      ContDiff ℝ ∞ (cutoffField χ x₀ g) ∧ ∀ x, divergenceAt (cutoffField χ x₀ g) x = 0

end Breakdown.Periodic
