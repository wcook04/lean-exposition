import Breakdown.Torus.StatementsSmooth

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def CoefDeriv : Prop :=
  ∀ f : Space → Space, ContDiff ℝ 1 f → IsPeriodic f → ∀ (i : Fin 3) (k : Lattice),
    freqTrCoef (fun x => fderiv ℝ f x (unitVector i)) k =
      (2 * π * Complex.I * (k i : ℂ)) • freqTrCoef f k

def CoefSumSecondPartials : Prop :=
  ∀ f : Space → Space, ContDiff ℝ 2 f → IsPeriodic f → ∀ k : Lattice,
    freqTrCoef (sumSecondPartialsAt f) k = (-(4 * π ^ 2 * ‖freq k‖ ^ 2) : ℝ) • freqTrCoef f k

def CoefGradient : Prop :=
  ∀ g : Space → ℝ, ContDiff ℝ 1 g → IsPeriodic g → ∀ k : Lattice,
    freqTrCoef (gradientAt g) k = (2 * π * Complex.I * scalarCoef g k) • latVec k

def FreqTrSeriesSpec : Prop :=
  ∀ f : Space → Space, ContDiff ℝ ∞ f → IsPeriodic f → (∀ x, divergenceAt f x = 0) →
    (∀ k, coeff (toV f) k = freqTrCoef f k) ∧ Summable (fun k => ‖freqTrCoef f k‖) ∧
      ∀ x, HasSum (fun k => character (-k) x • freqTrCoef f k) (complexify (f x))

def CoefAdvection : Prop :=
  ∀ f : Space → Space, ContDiff ℝ ∞ f → IsPeriodic f → (∀ x, divergenceAt f x = 0) →
    ∀ k, freqTrCoef (advectionAt f) k = advCoef (toV f) (toV f) k

def CoefTimeDeriv : Prop :=
  ∀ u : ℝ → Space → Space, ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Ici 0 ×ˢ univ) →
    (∀ t ≥ 0, IsPeriodic (u t)) → ∀ k : Lattice,
      ContinuousOn (fun τ => freqTrCoef (u τ) k) (Ici 0) ∧
        ∀ t > 0, HasDerivAt (fun τ => freqTrCoef (u τ) k)
          (freqTrCoef (fun x => deriv (fun τ => u τ x) t) k) t

def ToVContinuous : Prop :=
  ∀ u : ℝ → Space → Space, ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Ici 0 ×ˢ univ) →
    (∀ t ≥ 0, IsPeriodic (u t)) → (∀ t ≥ 0, ∀ x, divergenceAt (u t) x = 0) →
      ContinuousOn (fun t => toV (u t)) (Ici 0)

def TrigHs : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset Lattice) (c : Lattice → Coef),
    (∫ x in cell, ‖∑ k ∈ s, character (-k) x • c k‖ ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤
      C * (∑ k ∈ s, weight k * ‖c k‖ ^ 2) ^ (1 / 2 : ℝ)

end Breakdown.Periodic
