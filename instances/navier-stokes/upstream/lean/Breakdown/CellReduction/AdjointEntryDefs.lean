import Breakdown.Cert.ExtendedStatement
import Breakdown.CertCell.StatementDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

def IsWeakMatrixDivergence (K : Space → (Space →L[ℝ] Space)) (d : Space → Space) : Prop :=
  LocallyIntegrable K ∧ LocallyIntegrable d ∧
    ∀ φ, IsTestFunction φ → ∀ c : Fin 3,
      ∫ y, φ y * d y c = -∫ y, ∑ i : Fin 3, fderiv ℝ φ y (unitVector i) * K y (unitVector i) c

def IsWeakScalarGradient (p : Space → ℝ) (g : Space → Space) : Prop :=
  LocallyIntegrable p ∧ LocallyIntegrable g ∧
    ∀ φ, IsTestFunction φ → ∀ i : Fin 3,
      ∫ y, φ y * g y i = -∫ y, fderiv ℝ φ y (unitVector i) * p y

def curlAt (A : Space → Space) (y : Space) : Space :=
  (fderiv ℝ A y (unitVector 1) 2 - fderiv ℝ A y (unitVector 2) 1) • unitVector 0
    + (fderiv ℝ A y (unitVector 2) 0 - fderiv ℝ A y (unitVector 0) 2) • unitVector 1
    + (fderiv ℝ A y (unitVector 0) 1 - fderiv ℝ A y (unitVector 1) 0) • unitVector 2

def periodInnerIntegral (v T : ℝ → Space → Space) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (v σ y) (T σ y)

def periodMatrixIntegral (G K : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (G σ y) (K σ y)

def gradientNorm (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  Real.sqrt (periodLIntegral (fun σ y => matSq (G σ y))).toReal

structure IsAdjointField (ζ : ℝ → Space → Space) (C γ : ℝ) : Prop where
  rate_gt : 5 / 2 < γ
  smooth : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)
  periodic : IsTimePeriodic ζ
  divergence_free : ∀ σ y, divergenceAt (ζ σ) y = 0
  second_weak : ∀ σ, ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ (ζ σ) y (unitVector j))
    (fun y => (secondDeriv (ζ σ) y).flip (unitVector j))
  decay : ∀ σ y, ‖ζ σ y‖ ≤ C / (1 + ‖y‖) ^ γ ∧ ‖timeDerivative ζ σ y‖ ≤ C / (1 + ‖y‖) ^ γ ∧
    ‖fderiv ℝ (ζ σ) y‖ ≤ C / (1 + ‖y‖) ^ (γ + 1)
  second_decay : ∀ σ, ∀ᵐ y, ‖secondDeriv (ζ σ) y‖ ≤ C / (1 + ‖y‖) ^ γ
  second_differentiable : ∀ σ, ∀ᵐ y, DifferentiableAt ℝ (fun x => fderiv ℝ (ζ σ) x) y

structure IsCurlPotential (ζ A : ℝ → Space → Space) (C β : ℝ) : Prop where
  rate_gt : 3 / 2 < β
  smooth : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)
  periodic : IsTimePeriodic A
  curl_eq : ∀ σ y, curlAt (A σ) y = ζ σ y
  decay : ∀ σ y, ‖A σ y‖ ≤ C / (1 + ‖y‖) ^ β ∧ ‖timeDerivative A σ y‖ ≤ C / (1 + ‖y‖) ^ β ∧
    ‖fderiv ℝ (A σ) y‖ ≤ C / (1 + ‖y‖) ^ (β + 1)

structure IsFlowPiece (W : ℝ → Space → Space) (D : ℝ) : Prop where
  smooth : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)
  periodic : IsTimePeriodic W
  divergence_free : ∀ σ y, divergenceAt (W σ) y = 0
  decay : ∀ σ y, ‖W σ y‖ ≤ D ∧ ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖)

structure IsResidualField (T : ℝ → Space → Space) (K : ℝ → Space → (Space →L[ℝ] Space)) (C γ : ℝ) :
    Prop where
  rate_gt : 5 / 2 < γ
  residual_measurable : AEStronglyMeasurable (fun z : ℝ × Space => T z.1 z.2) volume
  flux_measurable : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) volume
  flux_weak : ∀ σ, IsWeakMatrixDivergence (K σ) (matrixDivergence (K σ))
  decay : ∀ σ y, ‖T σ y‖ ≤ C / (1 + ‖y‖) ^ γ ∧ ‖K σ y‖ ≤ C / (1 + ‖y‖) ^ (γ + 1)
  flux_div_decay : ∀ σ, ∀ᵐ y, ‖matrixDivergence (K σ) y‖ ≤ C / (1 + ‖y‖) ^ γ

structure IsPotentialData (p : PotentialData) (C : ℝ) : Prop where
  theta_smooth : ContDiff ℝ 1 (fun z : ℝ × Space => p.theta z.1 z.2)
  phi_smooth : ContDiff ℝ 1 (fun z : ℝ × Space => p.phi z.1 z.2)
  flux_measurable : AEStronglyMeasurable (fun z : ℝ × Space => p.flux z.1 z.2) volume
  pressure_measurable : AEStronglyMeasurable (fun z : ℝ × Space => p.pressure z.1 z.2) volume
  theta_weak : ∀ σ, ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ (p.theta σ) y (unitVector j))
    (fun y => (secondDeriv (p.theta σ) y).flip (unitVector j))
  phi_weak : ∀ σ, ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ (p.phi σ) y (unitVector j))
    (fun y => (secondDeriv (p.phi σ) y).flip (unitVector j))
  flux_weak : ∀ σ, IsWeakMatrixDivergence (p.flux σ) (matrixDivergence (p.flux σ))
  pressure_weak : ∀ σ, IsWeakScalarGradient (p.pressure σ) (gradientAt (p.pressure σ))
  value_decay : ∀ σ y, ‖p.theta σ y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧ ‖fderiv ℝ (p.theta σ) y‖ ≤ C / (1 + ‖y‖) ^ 3 ∧
    ‖p.phi σ y‖ ≤ C / (1 + ‖y‖) ∧ ‖fderiv ℝ (p.phi σ) y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
    ‖p.flux σ y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧ |p.pressure σ y| ≤ C / (1 + ‖y‖) ^ 2
  second_decay : ∀ σ, ∀ᵐ y, ‖secondDerivTrace (secondDeriv (p.theta σ) y)‖ ≤ C / (1 + ‖y‖) ^ 4 ∧
    ‖secondDerivTrace (secondDeriv (p.phi σ) y)‖ ≤ C / (1 + ‖y‖) ^ 3 ∧
    ‖y‖ * ‖matrixDivergence (p.flux σ) y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
    ‖y‖ * ‖gradientAt (p.pressure σ) y‖ ≤ C ∧ ‖y‖ ^ 3 * ‖gradientAt (p.pressure σ) y‖ ≤ C

def RemainderDualBound (R : ℝ → Space → Space) (ρ : ℝ) : Prop :=
  ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume →
    AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume →
    (∀ᵐ σ, IsWeakGradient (v σ) (G σ)) →
    (∀ᵐ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) < ⊤) →
    periodLIntegral (fun σ y => matSq (G σ y)) < ⊤ →
    (∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), Integrable (fun y => inner ℝ (v σ y) (R σ y))) ∧
      IntegrableOn (fun σ => ∫ y, inner ℝ (v σ y) (R σ y)) (Set.Icc (0 : ℝ) 1) ∧
      |periodInnerIntegral v R| ≤ ρ * gradientNorm G

structure IsPinData {k : ℕ} (χ : Fin k → ℝ → Space → (Space →L[ℝ] Space)) (p : PinData k)
    (C R₀ : ℝ) : Prop where
  pin_measurable : ∀ l, AEStronglyMeasurable (fun z : ℝ × Space => χ l z.1 z.2) volume
  potential_measurable : ∀ l, AEStronglyMeasurable (fun z : ℝ × Space => p.potential l z.1 z.2) volume
  potentialGrad_measurable : ∀ l,
    AEStronglyMeasurable (fun z : ℝ × Space => fderiv ℝ (p.potential l z.1) z.2) volume
  potential_weak : ∀ l σ, IsWeakGradient (p.potential l σ) (fun y => fderiv ℝ (p.potential l σ) y)
  potentialGrad_finite : ∀ l, periodLIntegral (fun σ y => matSq (fderiv ℝ (p.potential l σ) y)) < ⊤
  potential_support : ∀ l σ y, R₀ ≤ ‖y‖ → p.potential l σ y = 0
  generator_smooth : ∀ l, ContDiff ℝ 1 (fun z : ℝ × Space => p.generator l z.1 z.2)
  generator_periodic : ∀ l, IsTimePeriodic (p.generator l)
  generator_weak : ∀ l σ, ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ (p.generator l σ) y (unitVector j))
    (fun y => (secondDeriv (p.generator l σ) y).flip (unitVector j))
  generator_support : ∀ l σ y, R₀ ≤ ‖y‖ → p.generator l σ y = 0
  generatorSecond_bound : ∀ l σ, ∀ᵐ y, ‖secondDeriv (p.generator l σ) y‖ ≤ C
  generator_differentiable : ∀ l σ, ∀ᵐ y, DifferentiableAt ℝ (fun x => fderiv ℝ (p.generator l σ) x) y

namespace AdjointDefectEntry

variable {k : ℕ} (r : AdjointDefectEntry k)

end AdjointDefectEntry

end AdjointDefect

end Breakdown
