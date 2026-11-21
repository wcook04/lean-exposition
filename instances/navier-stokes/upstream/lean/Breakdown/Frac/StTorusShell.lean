import Breakdown.Frac.StTorusStep
import Breakdown.Frac.StTorusForce
import Breakdown.Torus.HeatComparisonStatements
import Breakdown.Torus.StatementsShell

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def simScale (α μ : ℝ) : ℝ := μ ^ (1 / α)

def fracSourceFun (α μ τ : ℝ) (A : Freq.L2R) : V :=
  if 0 < μ then fracTorusForce α (μ * τ) (fun x => (A : Space → Space) (simCoord (simScale α μ) x)) else 0

def FracSourceOpSpec (α μ τ : ℝ) (S : Freq.L2R →L[ℝ] V) : Prop := ∀ A, S A = fracSourceFun α μ τ A

open Classical in
def fracSourceOp (α μ τ : ℝ) : Freq.L2R →L[ℝ] V :=
  if h : ∃ S, FracSourceOpSpec α μ τ S then h.choose else 0

def FracSourceOpExists (α : ℝ) : Prop := ∀ μ τ : ℝ, ∃ S, FracSourceOpSpec α μ τ S

def FracSourceOpContinuous (α : ℝ) : Prop :=
  ∀ (μ : ℝ) (A : Freq.L2R), 0 < μ → ContinuousOn (fun τ => fracSourceOp α μ τ A) (Ioi 0)

def FracHeatSolenoidalContinuous (α : ℝ) : Prop :=
  ∀ A : Freq.L2R, ContinuousOn (fun τ => Freq.fracHeatSolenoidal α τ A) (Ioi 0)

def fracLambdaR3 (α : ℝ) (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ) : ShellData →L[ℝ] Freq.X :=
  -((Freq.fracHeatSolenoidal α τ).comp (advectShell φ hφ b))

def fracLambdaTorus (α : ℝ) (φ : Space → Space) (hφ : IsTestField φ) (b μ τ : ℝ) : ShellData →L[ℝ] V :=
  -((μ ^ (-(1 / (4 * α)))) • (fracSourceOp α μ τ).comp (advectShell φ hφ b))

def FracR3Factor (α : ℝ) : Prop :=
  ∀ (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ), tsupport φ ⊆ Metric.closedBall 0 b →
    ∀ τ : ℝ, 0 < τ → ∀ v : Freq.X,
      (2 : ℝ) • Freq.fracBilinX α τ (Freq.embedX φ) v = fracLambdaR3 α φ hφ b τ (restrictR3 b v)

def FracR3LambdaBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ), 0 < τ → ∀ ζ : ShellData,
    ‖fracLambdaR3 α φ hφ b τ ζ‖ ≤ C * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖ζ‖

def FracTorusFactor (α : ℝ) : Prop :=
  ∀ (φ : Space → Space) (hφ : IsTestField φ) (b μ : ℝ), 0 < μ → μ ≤ 1 → IsShellScale (simScale α μ) b →
    tsupport φ ⊆ Metric.closedBall 0 b → ∀ τ : ℝ, 0 < τ → ∀ z : V,
      (2 * μ ^ (3 / (4 * α))) • fracTorusKernel α (μ * τ)
          ((simScale α μ ^ (1 / 4 : ℝ)) • toV (transplantField (simScale α μ) φ)) z =
        fracLambdaTorus α φ hφ b μ τ (restrictTorus (simScale α μ) b z)

def FracTorusLambdaBound (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space → Space) (hφ : IsTestField φ) (b μ τ : ℝ), 0 < μ → μ ≤ 1 →
    IsShellScale (simScale α μ) b → 0 < τ → μ * τ ≤ 1 → ∀ ζ : ShellData,
      ‖fracLambdaTorus α φ hφ b μ τ ζ‖ ≤ C * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖ζ‖

def FracHeatSolenoidalComparison (α : ℝ) : Prop :=
  ∀ b b' ε δ : ℝ, 0 < b → 0 < b' → 0 < ε → 0 < δ → ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
    ∀ τ ∈ Icc ε ε⁻¹, ∀ A : Freq.L2R, (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
      ‖restrictTorus (simScale α μ) b ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A) -
          restrictR3 b (Freq.fracHeatSolenoidal α τ A)‖ ≤
        δ * (eLpNorm (A : Space → Space) (3 / 2) volume).toReal

def FracFreeHeatComparison (α : ℝ) : Prop :=
  ∀ (φ : Space → Space), IsTestField φ → ∀ b ε δ : ℝ, 0 < b → 0 < ε → 0 < δ →
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ → ∀ τ ∈ Icc 0 ε⁻¹,
      ‖restrictTorus (simScale α μ) b ((simScale α μ ^ (1 / 4 : ℝ)) •
          fracTorusHeat α (μ * τ) (toV (transplantField (simScale α μ) φ))) -
        restrictR3 b (Freq.fracHeatX α τ (Freq.embedX φ))‖ ≤ δ

def fracValueDensity (α τ : ℝ) (A : Space → Space) (y ξ : Space) : Coef :=
  expChar y ξ • (Freq.fracHeatFactor α τ ξ • divFreeVec ξ (freqTrVec A ξ))

def fracGradDensity (α : ℝ) (j : Fin 3) (τ : ℝ) (A : Space → Space) (y ξ : Space) : Coef :=
  (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • fracValueDensity α τ A y ξ

def fracFreeDensity (α τ : ℝ) (φ : Space → Space) (y ξ : Space) : Coef :=
  expChar y ξ • (Freq.fracHeatFactor α τ ξ • freqTrVec φ ξ)

def fracFreeGradDensity (α : ℝ) (j : Fin 3) (τ : ℝ) (φ : Space → Space) (y ξ : Space) : Coef :=
  (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • fracFreeDensity α τ φ y ξ

def FracTorusSourceSeries (α : ℝ) : Prop :=
  ∀ (b b' μ τ : ℝ), 0 < μ → μ ≤ 1 → IsShellScale (simScale α μ) b →
    Real.sqrt (simScale α μ) * b' ≤ 1 / 4 → 0 < τ → ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
    (∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) b)),
      (simScale α μ ^ (1 / 4 : ℝ)) •
          (torusSeries 6 (coeff ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A)) : Space → Coef)
        (center + Real.sqrt (simScale α μ) • y) =
        latticeSum (Real.sqrt (simScale α μ)) (fracValueDensity α τ (⇑A) y)) ∧
    ∀ j : Fin 3, ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) b)),
      (simScale α μ ^ (3 / 4 : ℝ)) •
          (torusSeries 2 (gradCoef j ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ A)) : Space → Coef)
        (center + Real.sqrt (simScale α μ) • y) =
        latticeSum (Real.sqrt (simScale α μ)) (fracGradDensity α j τ (⇑A) y)

def FracTorusFreeSeries (α : ℝ) : Prop :=
  ∀ (φ : Space → Space), IsTestField φ → ∀ (b b' μ τ : ℝ), 0 < μ → μ ≤ 1 →
    IsShellScale (simScale α μ) b → IsShellScale (simScale α μ) b' →
    0 ≤ τ → tsupport φ ⊆ Metric.closedBall 0 b' →
    (∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) b)),
      (simScale α μ ^ (1 / 4 : ℝ)) •
          (torusSeries 6 (coeff ((simScale α μ ^ (1 / 4 : ℝ)) •
            fracTorusHeat α (μ * τ) (toV (transplantField (simScale α μ) φ)))) : Space → Coef)
          (center + Real.sqrt (simScale α μ) • y) =
        latticeSum (Real.sqrt (simScale α μ)) (fracFreeDensity α τ φ y)) ∧
    ∀ j : Fin 3, ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) b)),
      (simScale α μ ^ (3 / 4 : ℝ)) •
          (torusSeries 2 (gradCoef j ((simScale α μ ^ (1 / 4 : ℝ)) •
            fracTorusHeat α (μ * τ) (toV (transplantField (simScale α μ) φ)))) : Space → Coef)
          (center + Real.sqrt (simScale α μ) • y) =
        latticeSum (Real.sqrt (simScale α μ)) (fracFreeGradDensity α j τ φ y)

def FracHeatSolenoidalFactor (α : ℝ) : Prop :=
  ∀ (b' τ : ℝ), 0 < τ → ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
    ∃ g : Freq.X, ((g : Freq.L2C) : Space → Freq.CSpace) =ᵐ[volume]
        (fun ξ => Freq.fracHeatFactor α τ ξ • divFreeVec ξ (freqTrVec (⇑A) ξ)) ∧
      Freq.IsHalfSspOf g (Freq.fracHeatSolenoidal α τ A)

def FracR3ValueFormula (α : ℝ) : Prop :=
  ∀ (b' τ : ℝ), 0 < τ → ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
    (Freq.velocity (Freq.fracHeatSolenoidal α τ A) : Space → Space) =ᵐ[volume]
        (fun y => Freq.realVec (∫ ξ, fracValueDensity α τ (⇑A) y ξ)) ∧
      ∀ j : Fin 3, (Freq.partialX j (Freq.fracHeatSolenoidal α τ A) : Space → Space) =ᵐ[volume]
        (fun y => Freq.realVec (∫ ξ, fracGradDensity α j τ (⇑A) y ξ))

def FracR3FreeFormula (α : ℝ) : Prop :=
  ∀ (φ : Space → Space), IsTestField φ → ∀ τ : ℝ, 0 ≤ τ →
    (Freq.velocity (Freq.fracHeatX α τ (Freq.embedX φ)) : Space → Space) =ᵐ[volume]
        (fun y => Freq.realVec (∫ ξ, fracFreeDensity α τ φ y ξ)) ∧
      ∀ j : Fin 3, (Freq.partialX j (Freq.fracHeatX α τ (Freq.embedX φ)) : Space → Space) =ᵐ[volume]
        (fun y => Freq.realVec (∫ ξ, fracFreeGradDensity α j τ φ y ξ))

def FracSourceDensityBounds (α : ℝ) : Prop :=
  ∀ b b' ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
    (eLpNorm (A : Space → Space) (3 / 2) volume).toReal ≤ 1 →
    ∀ y : Space, ‖y‖ ≤ b → ∀ τ ∈ Icc ε ε⁻¹, ∀ ξ : Space,
      ‖fracValueDensity α τ (⇑A) y ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ) ∧
      ∀ j : Fin 3, ‖fracGradDensity α j τ (⇑A) y ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ)

def FracSourceDensityIncrement (α : ℝ) : Prop :=
  ∀ b b' ε r R : ℝ, 0 < ε → 0 < r → ∃ L : ℝ, ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
    (eLpNorm (A : Space → Space) (3 / 2) volume).toReal ≤ 1 →
    ∀ y : Space, ‖y‖ ≤ b → ∀ τ ∈ Icc ε ε⁻¹, ∀ ξ ξ' : Space,
      r ≤ ‖ξ‖ → ‖ξ‖ ≤ R → r ≤ ‖ξ'‖ → ‖ξ'‖ ≤ R →
      ‖fracValueDensity α τ (⇑A) y ξ - fracValueDensity α τ (⇑A) y ξ'‖ ≤ L * ‖ξ - ξ'‖ ∧
      ∀ j : Fin 3, ‖fracGradDensity α j τ (⇑A) y ξ - fracGradDensity α j τ (⇑A) y ξ'‖ ≤ L * ‖ξ - ξ'‖

def FracFreeDensityBounds (α : ℝ) : Prop :=
  ∀ φ : Space → Space, IsTestField φ → ∀ b ε : ℝ, 0 < ε → ∃ K : ℝ,
    ∀ y : Space, ‖y‖ ≤ b → ∀ τ ∈ Icc 0 ε⁻¹, ∀ ξ : Space,
      ‖fracFreeDensity α τ φ y ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ) ∧
      ∀ j : Fin 3, ‖fracFreeGradDensity α j τ φ y ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ)

def FracFreeDensityIncrement (α : ℝ) : Prop :=
  ∀ φ : Space → Space, IsTestField φ → ∀ b ε r R : ℝ, 0 < ε → 0 < r → ∃ L : ℝ,
    ∀ y : Space, ‖y‖ ≤ b → ∀ τ ∈ Icc 0 ε⁻¹, ∀ ξ ξ' : Space,
      r ≤ ‖ξ‖ → ‖ξ‖ ≤ R → r ≤ ‖ξ'‖ → ‖ξ'‖ ≤ R →
      ‖fracFreeDensity α τ φ y ξ - fracFreeDensity α τ φ y ξ'‖ ≤ L * ‖ξ - ξ'‖ ∧
      ∀ j : Fin 3, ‖fracFreeGradDensity α j τ φ y ξ - fracFreeGradDensity α j τ φ y ξ'‖ ≤ L * ‖ξ - ξ'‖

end Breakdown.Periodic
