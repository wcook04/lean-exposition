import Breakdown.Torus.StatementsShell

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

def divFreeVec (ξ : Space) (c : Coef) : Coef :=
  if ξ = 0 then c else c - ((∑ i, ((ξ i : ℝ) : ℂ) * c i) / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • Freq.complexifyVec ξ

def freqTrVec (A : Space → Space) (ξ : Space) : Coef :=
  FourierTransform.fourier (fun x => Freq.complexifyVec (A x)) ξ

def expChar (y ξ : Space) : ℂ := Complex.exp (2 * π * Complex.I * ((inner ℝ ξ y : ℝ) : ℂ))

def valueDensity (τ : ℝ) (A : Space → Space) (y ξ : Space) : Coef :=
  expChar y ξ • (Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec A ξ))

def gradDensity (j : Fin 3) (τ : ℝ) (A : Space → Space) (y ξ : Space) : Coef :=
  (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • valueDensity τ A y ξ

def freeDensity (τ : ℝ) (φ : Space → Space) (y ξ : Space) : Coef :=
  expChar y ξ • (Freq.heatFactor τ ξ • freqTrVec φ ξ)

def freeGradDensity (j : Fin 3) (τ : ℝ) (φ : Space → Space) (y ξ : Space) : Coef :=
  (2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) • freeDensity τ φ y ξ

def latticeSum (h : ℝ) (G : Space → Coef) : Coef := (h ^ 3) • ∑' k : Lattice, G (h • freq k)

def latticeIndex (h : ℝ) (ξ : Space) : Lattice := fun i => ⌊ξ i / h⌋

def StepIntegral : Prop :=
  ∀ h : ℝ, 0 < h →
    (∀ c : Lattice → ℝ≥0∞, ∫⁻ ξ, c (latticeIndex h ξ) = ENNReal.ofReal (h ^ 3) * ∑' k, c k) ∧
    (∀ c : Lattice → Coef, Summable (fun k => ‖c k‖) →
      Integrable (fun ξ => c (latticeIndex h ξ)) ∧ ∫ ξ, c (latticeIndex h ξ) = (h ^ 3) • ∑' k, c k) ∧
    Summable (fun k : Lattice => (1 + ‖h • freq k‖) ^ (-4 : ℝ))

def PartitionSumBound : Prop :=
  ∀ (ι : Type) (G : ι → Space → Coef) (K : ℝ),
    (∀ i ξ, ‖G i ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ)) →
    (∀ r R : ℝ, 0 < r → ∃ L : ℝ, ∀ i ξ ξ', r ≤ ‖ξ‖ → ‖ξ‖ ≤ R → r ≤ ‖ξ'‖ → ‖ξ'‖ ≤ R →
      ‖G i ξ - G i ξ'‖ ≤ L * ‖ξ - ξ'‖) →
    ∀ δ : ℝ, 0 < δ → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ → ∀ i,
      ‖latticeSum h (G i) - ∫ ξ, G i ξ‖ ≤ δ

def TorusSeriesPointwise : Prop :=
  ∀ c : Lattice → Coef, Summable (fun k => ‖c k‖) →
    (torusSeries 2 c : Space → Coef) =ᵐ[volume.restrict cell] (fun x => ∑' k, character (-k) x • c k) ∧
    (torusSeries 6 c : Space → Coef) =ᵐ[volume.restrict cell] (fun x => ∑' k, character (-k) x • c k)

def SourceCoefFormula : Prop :=
  ∀ (b' μ : ℝ), 0 < μ → Real.sqrt μ * b' ≤ 1 / 4 → ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) → ∀ k : Lattice,
      freqTrCoef (fun x => (A : Space → Space) (simCoord μ x)) k =
        (μ ^ (3 / 2 : ℝ)) • (character k center • freqTrVec (⇑A) (Real.sqrt μ • freq k))

def TransplantCoefFormula : Prop :=
  ∀ (φ : Space → Space), IsTestField φ → ∀ (b' μ : ℝ), 0 < μ → Real.sqrt μ * b' ≤ 1 / 4 →
    tsupport φ ⊆ Metric.closedBall 0 b' → ∀ k : Lattice,
      freqTrCoef (transplantField μ φ) k = μ • (character k center • freqTrVec φ (Real.sqrt μ • freq k))

def TorusSourceSeries : Prop :=
  ∀ (b b' μ τ : ℝ), IsShellScale μ b → Real.sqrt μ * b' ≤ 1 / 4 → 0 < τ → ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
    (∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) b)),
      (μ ^ (1 / 4 : ℝ)) • (torusSeries 6 (coeff ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A)) : Space → Coef)
        (center + Real.sqrt μ • y) = latticeSum (Real.sqrt μ) (valueDensity τ (⇑A) y)) ∧
    ∀ j : Fin 3, ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) b)),
      (μ ^ (3 / 4 : ℝ)) •
          (torusSeries 2 (gradCoef j ((μ ^ (-(1 / 4 : ℝ))) • sourceOp μ τ A)) : Space → Coef)
        (center + Real.sqrt μ • y) = latticeSum (Real.sqrt μ) (gradDensity j τ (⇑A) y)

def TorusFreeSeries : Prop :=
  ∀ (φ : Space → Space), IsTestField φ → ∀ (b b' μ τ : ℝ), IsShellScale μ b → IsShellScale μ b' →
    0 ≤ τ → tsupport φ ⊆ Metric.closedBall 0 b' →
    (∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) b)),
      (μ ^ (1 / 4 : ℝ)) •
          (torusSeries 6 (coeff ((μ ^ (1 / 4 : ℝ)) • heat (μ * τ) (toV (transplantField μ φ)))) :
            Space → Coef) (center + Real.sqrt μ • y) = latticeSum (Real.sqrt μ) (freeDensity τ φ y)) ∧
    ∀ j : Fin 3, ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) b)),
      (μ ^ (3 / 4 : ℝ)) •
          (torusSeries 2 (gradCoef j ((μ ^ (1 / 4 : ℝ)) • heat (μ * τ) (toV (transplantField μ φ)))) :
            Space → Coef) (center + Real.sqrt μ • y) = latticeSum (Real.sqrt μ) (freeGradDensity j τ φ y)

def HeatDivFreeFactor : Prop :=
  ∀ (b' τ : ℝ), 0 < τ → ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
    ∃ g : Freq.X, ((g : Freq.L2C) : Space → Freq.CSpace) =ᵐ[volume]
        (fun ξ => Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec (⇑A) ξ)) ∧
      Freq.IsHalfSspOf g (Freq.heatDivFree τ A)

def R3ValueFormula : Prop :=
  ∀ (b' τ : ℝ), 0 < τ → ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) →
    (Freq.velocity (Freq.heatDivFree τ A) : Space → Space) =ᵐ[volume]
        (fun y => Freq.realVec (∫ ξ, valueDensity τ (⇑A) y ξ)) ∧
      ∀ j : Fin 3, (Freq.partialX j (Freq.heatDivFree τ A) : Space → Space) =ᵐ[volume]
        (fun y => Freq.realVec (∫ ξ, gradDensity j τ (⇑A) y ξ))

def R3FreeFormula : Prop :=
  ∀ (φ : Space → Space), IsTestField φ → ∀ τ : ℝ, 0 ≤ τ →
    (Freq.velocity (Freq.heatX τ (Freq.embedX φ)) : Space → Space) =ᵐ[volume]
        (fun y => Freq.realVec (∫ ξ, freeDensity τ φ y ξ)) ∧
      ∀ j : Fin 3, (Freq.partialX j (Freq.heatX τ (Freq.embedX φ)) : Space → Space) =ᵐ[volume]
        (fun y => Freq.realVec (∫ ξ, freeGradDensity j τ φ y ξ))

def SourceDensityBounds : Prop :=
  ∀ b b' ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) → (eLpNorm (A : Space → Space) (3 / 2) volume).toReal ≤ 1 →
    ∀ y : Space, ‖y‖ ≤ b → ∀ τ ∈ Icc ε ε⁻¹, ∀ ξ : Space,
      ‖valueDensity τ (⇑A) y ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ) ∧
      ∀ j : Fin 3, ‖gradDensity j τ (⇑A) y ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ)

def SourceDensitySlope : Prop :=
  ∀ b b' ε r R : ℝ, 0 < ε → 0 < r → ∃ L : ℝ, ∀ A : Freq.L2R,
    (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) → (eLpNorm (A : Space → Space) (3 / 2) volume).toReal ≤ 1 →
    ∀ y : Space, ‖y‖ ≤ b → ∀ τ ∈ Icc ε ε⁻¹, ∀ ξ ξ' : Space,
      r ≤ ‖ξ‖ → ‖ξ‖ ≤ R → r ≤ ‖ξ'‖ → ‖ξ'‖ ≤ R →
      ‖valueDensity τ (⇑A) y ξ - valueDensity τ (⇑A) y ξ'‖ ≤ L * ‖ξ - ξ'‖ ∧
      ∀ j : Fin 3, ‖gradDensity j τ (⇑A) y ξ - gradDensity j τ (⇑A) y ξ'‖ ≤ L * ‖ξ - ξ'‖

def FreeDensityBounds : Prop :=
  ∀ φ : Space → Space, IsTestField φ → ∀ b ε : ℝ, 0 < ε → ∃ K : ℝ,
    ∀ y : Space, ‖y‖ ≤ b → ∀ τ ∈ Icc 0 ε⁻¹, ∀ ξ : Space,
      ‖freeDensity τ φ y ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ) ∧
      ∀ j : Fin 3, ‖freeGradDensity j τ φ y ξ‖ ≤ K * (1 + ‖ξ‖) ^ (-4 : ℝ)

def FreeDensitySlope : Prop :=
  ∀ φ : Space → Space, IsTestField φ → ∀ b ε r R : ℝ, 0 < ε → 0 < r → ∃ L : ℝ,
    ∀ y : Space, ‖y‖ ≤ b → ∀ τ ∈ Icc 0 ε⁻¹, ∀ ξ ξ' : Space,
      r ≤ ‖ξ‖ → ‖ξ‖ ≤ R → r ≤ ‖ξ'‖ → ‖ξ'‖ ≤ R →
      ‖freeDensity τ φ y ξ - freeDensity τ φ y ξ'‖ ≤ L * ‖ξ - ξ'‖ ∧
      ∀ j : Fin 3, ‖freeGradDensity j τ φ y ξ - freeGradDensity j τ φ y ξ'‖ ≤ L * ‖ξ - ξ'‖

end Breakdown.Periodic
