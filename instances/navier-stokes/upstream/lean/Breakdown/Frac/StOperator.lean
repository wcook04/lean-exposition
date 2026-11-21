import Breakdown.Frac.Defs
import Breakdown.FreqTr.Basic

open scoped ContDiff
open MeasureTheory Real

noncomputable section

namespace Breakdown

def RemainderBoundStatement : Prop :=
  ∀ f : Space → Space, ContDiff ℝ 3 f → ∀ x z : Space, ∀ C : ℝ,
    (∀ y ∈ Metric.closedBall x ‖z‖, ‖iteratedFDeriv ℝ 3 f y‖ ≤ C) →
    ‖secondOrderRemainder f x z‖ ≤ C * ‖z‖ ^ 3

def NormalizerStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 2 →
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (z 0) - 1 + (z 0) ^ 2 / 2)) ∧
      0 < fractionalNormalizer α

def RemainderIntegrableStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ v : Space → Space, ContDiff ℝ ∞ v →
    (MemLp v 2 volume ∨ ∃ C : ℝ, ∀ y, ‖v y‖ ≤ C) →
    ∀ x, Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v x z)

def SymbolScalarStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ ξ : Space,
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) *
      (Real.cos (inner ℝ z ξ) - 1 + (inner ℝ z ξ) ^ 2 / 2)) ∧
    ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) * (Real.cos (inner ℝ z ξ) - 1 + (inner ℝ z ξ) ^ 2 / 2) =
      ‖ξ‖ ^ (2 * α) * fractionalNormalizer α ∧
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * (Real.sin (inner ℝ z ξ) - inner ℝ z ξ)) ∧
    ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) * (Real.sin (inner ℝ z ξ) - inner ℝ z ξ) = 0

def symbolIntegrand (α : ℝ) (ξ z : Space) : ℂ :=
  ((‖z‖ ^ (-(3 + 2 * α)) : ℝ) : ℂ) *
    (Complex.exp (((2 * π * inner ℝ z ξ : ℝ) : ℂ) * Complex.I) - 1
      - ((2 * π * inner ℝ z ξ : ℝ) : ℂ) * Complex.I + ((2 * π ^ 2 * (inner ℝ z ξ) ^ 2 : ℝ) : ℂ))

def SymbolExchangeStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ φ : SchwartzMap Space Space, ∀ ξ : Space,
    FourierTransform.fourier (fun x => Freq.complexifyVec (fractionalPowerAt α φ x)) ξ =
      (((fractionalNormalizer α)⁻¹ : ℝ) : ℂ) • (∫ z : Space, symbolIntegrand α ξ z) •
        FourierTransform.fourier (fun x => Freq.complexifyVec (φ x)) ξ

def SymbolStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ φ : SchwartzMap Space Space, ∀ ξ : Space,
    FourierTransform.fourier (fun x => Freq.complexifyVec (fractionalPowerAt α φ x)) ξ =
      (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) •
        FourierTransform.fourier (fun x => Freq.complexifyVec (φ x)) ξ

def SymmetryCompactStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ v φ : Space → Space, ContDiff ℝ ∞ v →
    (MemLp v 2 volume ∨ ∃ C : ℝ, ∀ y, ‖v y‖ ≤ C) → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    Integrable (fun x => inner ℝ (fractionalPowerAt α v x) (φ x)) ∧
      Integrable (fun x => inner ℝ (v x) (fractionalPowerAt α φ x)) ∧
      ∫ x, inner ℝ (fractionalPowerAt α v x) (φ x) = ∫ x, inner ℝ (v x) (fractionalPowerAt α φ x)

def SymmetryRapidStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ v : Space → Space, ContDiff ℝ ∞ v →
    (∀ j ≤ 3, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j v y‖ ≤ C) → ∀ φ : SchwartzMap Space Space,
    Integrable (fun x => inner ℝ (fractionalPowerAt α v x) (φ x)) ∧
      Integrable (fun x => inner ℝ (v x) (fractionalPowerAt α φ x)) ∧
      ∫ x, inner ℝ (fractionalPowerAt α v x) (φ x) = ∫ x, inner ℝ (v x) (fractionalPowerAt α φ x)

def CovarianceStatement : Prop :=
  ∀ α : ℝ, ∀ v : Space → Space, ContDiff ℝ 2 v →
    (∀ (l : ℝ), 0 < l → ∀ y, fractionalPowerAt α (fun x => v (l • x)) y =
      l ^ (2 * α) • fractionalPowerAt α v (l • y)) ∧
    (∀ c : ℝ, ∀ y, fractionalPowerAt α (fun x => c • v x) y = c • fractionalPowerAt α v y) ∧
    (∀ R : Space ≃ₗᵢ[ℝ] Space, ∀ y, fractionalPowerAt α (fun x => R (v (R.symm x))) y =
      R (fractionalPowerAt α v (R.symm y))) ∧
    (∀ c y : Space, fractionalPowerAt α (fun x => v (x + c)) y = fractionalPowerAt α v (y + c))

def AdditivityStatement : Prop :=
  ∀ α : ℝ, ∀ v w : Space → Space, ∀ x : Space,
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v x z) →
    Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder w x z) →
    DifferentiableAt ℝ v x → DifferentiableAt ℝ w x → ContDiffAt ℝ 2 v x → ContDiffAt ℝ 2 w x →
    fractionalPowerAt α (v + w) x = fractionalPowerAt α v x + fractionalPowerAt α w x

end Breakdown
