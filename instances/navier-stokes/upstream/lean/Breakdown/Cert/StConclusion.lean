import Breakdown.Defs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

def sigmaSimilarityIntegrand (P : ℝ) (W : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (φ : ℝ → Space → Space) (z : ℝ × Space) : ℝ :=
  -(1 / P) * inner ℝ (W z.1 z.2) (deriv (fun σ => φ σ z.2) z.1)
    - inner ℝ (W z.1 z.2) (φ z.1 z.2)
    - (1 / 2 : ℝ) * inner ℝ (W z.1 z.2) (fderiv ℝ (φ z.1) z.2 z.2)
    + ∑ i : Fin 3, inner ℝ (G z.1 z.2 (unitVector i)) (fderiv ℝ (φ z.1) z.2 (unitVector i))
    - ∑ i : Fin 3, (W z.1 z.2) i * inner ℝ (W z.1 z.2) (fderiv ℝ (φ z.1) z.2 (unitVector i))

structure IsSigmaProfile (P : ℝ) (W : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (C : ℝ) : Prop where
  period_pos : 0 < P
  measurable_velocity : AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume
  measurable_gradient : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume
  measurable_secondDeriv : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume
  periodic : ∀ σ y, W (σ + 1) y = W σ y
  weak_gradient : ∀ σ, IsWeakGradient (W σ) (G σ)
  weak_secondDeriv : ∀ᵐ σ, ∀ j : Fin 3,
    IsWeakGradient (fun y => G σ y (unitVector j)) (fun y => (H σ y).flip (unitVector j))
  divergence_free : ∀ σ, ∀ᵐ y, ∑ i : Fin 3, (G σ y (unitVector i)) i = 0
  sixth_power : ∀ σ, ∫⁻ y, ENNReal.ofReal (‖W σ y‖ ^ 6) ≤ ENNReal.ofReal C
  gradient_bound : ∀ σ, ∫⁻ y, ENNReal.ofReal (‖G σ y‖ ^ 2) ≤ ENNReal.ofReal C
  secondDeriv_finite : (∫⁻ σ in Set.Icc 0 1, ∫⁻ y, ENNReal.ofReal (‖H σ y‖ ^ 2)) < ⊤
  weak_equation : ∀ φ, IsSpaceTimeTestField φ →
    Integrable (sigmaSimilarityIntegrand P W G φ) ∧ ∫ z, sigmaSimilarityIntegrand P W G φ z = 0
  nonzero : ¬ (∀ᵐ z : ℝ × Space, W z.1 z.2 = 0)

end Breakdown
