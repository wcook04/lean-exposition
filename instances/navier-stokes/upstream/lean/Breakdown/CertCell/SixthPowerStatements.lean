import Breakdown.Cert.Statement

open MeasureTheory

noncomputable section

namespace Breakdown

def SixthPowerGradientBound (C : ℝ) : Prop :=
  ∀ (w : Space → Space) (G : Space → (Space →L[ℝ] Space)), IsWeakGradient w G →
    ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6) < ⊤ → ∫⁻ y, ENNReal.ofReal (matSq (G y)) < ⊤ →
      (∫ y, ‖w y‖ ^ 6) ^ ((1 : ℝ) / 3) ≤ C * ∫ y, matSq (G y)

def SmoothSixthPowerBound (C : ℝ) : Prop :=
  ∀ w : Space → Space, ContDiff ℝ 1 w → HasCompactSupport w →
    (∫ y, ‖w y‖ ^ 6) ^ ((1 : ℝ) / 3) ≤ C * ∫ y, matSq (fderiv ℝ w y)

def ThreeHalvesGradientBound (C : ℝ) : Prop :=
  ∀ u : Space → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
    (∫ y, |u y| ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) ≤ C * ∫ y, ‖fderiv ℝ u y‖

def TripleSliceBound : Prop :=
  ∀ f₁ f₂ f₃ : ℝ × ℝ → ENNReal, Measurable f₁ → Measurable f₂ → Measurable f₃ →
    ∫⁻ x, ∫⁻ y, ∫⁻ z, (f₁ (y, z) * f₂ (x, z) * f₃ (x, y)) ^ ((1 : ℝ) / 2) ≤
      ((∫⁻ p, f₁ p) * (∫⁻ p, f₂ p) * (∫⁻ p, f₃ p)) ^ ((1 : ℝ) / 2)

def LineGradientBound : Prop :=
  ∀ u : Space → ℝ, ContDiff ℝ 1 u → HasCompactSupport u → ∀ (i : Fin 3) (y : Space),
    |u y| ≤ (1 / 2 : ℝ) * ∫ t : ℝ, |fderiv ℝ u (y + t • unitVector i) (unitVector i)|

end Breakdown
