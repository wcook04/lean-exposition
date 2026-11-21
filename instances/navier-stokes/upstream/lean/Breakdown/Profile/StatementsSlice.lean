import Breakdown.Profile.StatementsField

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

structure IsSimilarityProfile (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)
  smooth_pressure : ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)
  residual : ∀ s y, SimilarityResidual W q s y = 0
  div : ∀ s y, divergenceAt (W s) y = 0
  decay : ∀ s y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W s) y‖ ≤ C / (1 + ‖y‖) ^ (j + 1)
  decay_pressure : ∀ s y, ‖fderiv ℝ (q s) y‖ ≤ C / (1 + ‖y‖) ^ 3

def SliceDecay : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ), IsSimilarityProfile W q C →
    ∀ s, IsDecayField (W s)

def SimilarityDerivBound : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ), IsSimilarityProfile W q C →
    ∃ K : ℝ, ∀ s y, ‖deriv (fun σ => W σ y) s + (1 / 2 : ℝ) • W s y
      + (1 / 2 : ℝ) • fderiv ℝ (W s) y y‖ ≤ K / (1 + ‖y‖) ^ 3

def SliceGradientContinuous : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ), IsSimilarityProfile W q C →
    ∀ s₀, Filter.Tendsto
      (fun s => ∫ y, ∑ i : Fin 3, ‖fderiv ℝ (W s - W s₀) y (unitVector i)‖ ^ 2)
      (nhds s₀) (nhds 0)

end Breakdown
