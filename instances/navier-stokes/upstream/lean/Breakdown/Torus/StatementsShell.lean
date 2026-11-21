import Breakdown.Torus.ShellDefs

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def TorusSeriesSmooth : Prop :=
  ∀ f : Space → Space, ContDiff ℝ ∞ f → IsPeriodic f → (∀ x, divergenceAt f x = 0) →
    (torusSeries 2 (coeff (toV f)) : Space → Coef) =ᵐ[volume.restrict cell] (fun x => complexify (f x)) ∧
    (torusSeries 6 (coeff (toV f)) : Space → Coef) =ᵐ[volume.restrict cell] (fun x => complexify (f x)) ∧
    ∀ j, (torusSeries 2 (gradCoef j (toV f)) : Space → Coef) =ᵐ[volume.restrict cell]
      (fun x => complexify (fderiv ℝ f x (unitVector j)))

def RestrictR3Bound : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, ‖restrictR3 b‖ ≤ C

def R3Factor : Prop :=
  ∀ (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ), tsupport φ ⊆ Metric.closedBall 0 b →
    ∀ τ : ℝ, 0 < τ → ∀ v : Freq.X,
      (2 : ℝ) • Freq.bilinX τ (Freq.embedX φ) v = lambdaR3 φ hφ b τ (restrictR3 b v)

def R3LambdaBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ), 0 < τ → ∀ ζ : ShellData,
    ‖lambdaR3 φ hφ b τ ζ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX φ‖ * ‖ζ‖

def TorusFactor : Prop :=
  ∀ (φ : Space → Space) (hφ : IsTestField φ) (b μ : ℝ), IsShellScale μ b →
    tsupport φ ⊆ Metric.closedBall 0 b → ∀ τ : ℝ, 0 < τ → ∀ z : V,
      (2 * μ ^ (3 / 4 : ℝ)) • kernel (μ * τ) ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ φ)) z =
        lambdaTorus φ hφ b μ τ (restrictTorus μ b z)

def TorusLambdaBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space → Space) (hφ : IsTestField φ) (b μ τ : ℝ), IsShellScale μ b →
    0 < τ → μ * τ ≤ 1 → ∀ ζ : ShellData,
      ‖lambdaTorus φ hφ b μ τ ζ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX φ‖ * ‖ζ‖

def TransplantNorm : Prop :=
  ∀ (g : Space → Space) (μ b : ℝ), ContDiff ℝ ∞ g → (∀ x, divergenceAt g x = 0) → IsShellScale μ b →
    tsupport g ⊆ Metric.closedBall 0 b →
      ‖(μ ^ (1 / 4 : ℝ)) • toV (transplantField μ g)‖ ^ 2 =
        (∫ y, ∑ i : Fin 3, ‖fderiv ℝ g y (unitVector i)‖ ^ 2) + μ * ∫ y, ‖g y‖ ^ 2

def TransplantSmooth : Prop :=
  ∀ (g : Space → Space) (μ b : ℝ), ContDiff ℝ ∞ g → (∀ x, divergenceAt g x = 0) → IsShellScale μ b →
    tsupport g ⊆ Metric.closedBall 0 b →
      ContDiff ℝ ∞ (transplantField μ g) ∧ IsPeriodic (transplantField μ g) ∧
        (∀ x, divergenceAt (transplantField μ g) x = 0) ∧
        ∀ x, dist x center ≤ 1 / 4 → transplantField μ g x = (Real.sqrt μ)⁻¹ • g ((Real.sqrt μ)⁻¹ • (x - center))

def HeatDivFreeComparison : Prop :=
  ∀ b b' ε δ : ℝ, 0 < b → 0 < b' → 0 < ε → 0 < δ → ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
    ∀ τ ∈ Icc ε ε⁻¹, ∀ A : Freq.L2R, (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
      ‖restrictTorus μ b ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A) - restrictR3 b (Freq.heatDivFree τ A)‖ ≤
        δ * (eLpNorm (A : Space → Space) (3 / 2) volume).toReal

def FreeHeatComparison : Prop :=
  ∀ (φ : Space → Space), IsTestField φ → ∀ b ε δ : ℝ, 0 < b → 0 < ε → 0 < δ →
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∀ τ ∈ Icc 0 ε⁻¹,
      ‖restrictTorus μ b ((μ ^ (1 / 4 : ℝ)) • heat (μ * τ) (toV (transplantField μ φ))) -
        restrictR3 b (Freq.heatX τ (Freq.embedX φ))‖ ≤ δ

end Breakdown.Periodic
