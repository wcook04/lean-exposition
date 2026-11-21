import Breakdown.Defs
import Breakdown.FreqTr.Realization
import Breakdown.Profile.StatementsPhysical

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

open Freq

def heatKernel (τ : ℝ) (x : Space) : ℝ :=
  (4 * π * τ) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖x‖ ^ 2) / (4 * τ))

def heatKernelThird (i j k : Fin 3) (ρ : ℝ) (x : Space) : ℝ :=
  ((if j = k then x i else 0) + (if i = k then x j else 0) + (if i = j then x k else 0)) /
      (4 * ρ ^ 2) * heatKernel ρ x
    - x i * x j * x k / (8 * ρ ^ 3) * heatKernel ρ x

def lerayKernel (i j k : Fin 3) (τ : ℝ) (x : Space) : ℝ :=
  (if i = j then -(x k / (2 * τ)) * heatKernel τ x else 0) + ∫ ρ in Ioi τ, heatKernelThird i j k ρ x

def kernelConv (τ : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (y : Space) : Space :=
  ∑ i : Fin 3, (∫ z, ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k) • unitVector i

def tensorField (a b : Space → Space) : Space → Fin 3 → Fin 3 → ℝ := fun z j k => a z j * b z k

def similarityShift (a : ℝ → Space → Space) (s τ : ℝ) : Space → Space := fun z =>
  a (s - Real.log (1 + τ)) ((Real.sqrt (1 + τ))⁻¹ • z)

def profileBilin (a b : ℝ → Space → Space) (s : ℝ) (y : Space) : Space :=
  -∫ τ in Ioi (0 : ℝ), (1 + τ)⁻¹ • kernelConv τ (tensorField (similarityShift a s τ) (similarityShift b s τ)) y

def WeightedBound {E : Type*} [Norm E] (a : ℝ → Space → E) (γ C : ℝ) : Prop :=
  ∀ s y, (1 + ‖y‖) ^ γ * ‖a s y‖ ≤ C

def UniformDerivBound (W : ℝ → Space → Space) (n : ℕ) (C : ℝ) : Prop :=
  ∀ j ≤ n, ∀ s y, ‖iteratedFDeriv ℝ j (W s) y‖ ≤ C

def TailVanishes (W : ℝ → Space → Space) : Prop :=
  ∀ ε > 0, ∃ R₀ : ℝ, ∀ s y, R₀ ≤ ‖y‖ → ‖W s y‖ ≤ ε

structure IsSmoothOrbitField (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) : Prop where
  period_pos : 0 < P
  smooth_field : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)
  smooth_pressure : ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)
  residual : ∀ s y, SimilarityResidual W q s y = 0
  divergence : ∀ s y, divergenceAt (W s) y = 0
  periodic : ∀ s y, W (s + P) y = R (W s (R.symm y))
  nonzero : ∃ s y, W s y ≠ 0
  deriv_bound : ∃ C, UniformDerivBound W 3 C
  tail : TailVanishes W
  pressure_sq : ∀ s, MemLp (fun y => fderiv ℝ (q s) y) 2 volume

structure IsRegularOrbitField (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) : Prop extends IsSmoothOrbitField W q P R where
  integral_eq : ∀ s y, W s y = profileBilin W W s y

def IsVelocityOf (w : ℝ → X) (W : ℝ → Space → Space) : Prop :=
  ∀ s, (velocity (w s) : Space → Space) =ᵐ[volume] W s

def SmoothFieldOfOrbit : Prop :=
  ∀ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space), realization.F.IsOrbit (realization.rot R) w P →
    ∃ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ), IsSmoothOrbitField W q P R ∧ IsVelocityOf w W

def IntegralEquationOfOrbit : Prop :=
  ∀ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (W : ℝ → Space → Space) (q : ℝ → Space → ℝ),
    realization.F.IsOrbit (realization.rot R) w P → IsSmoothOrbitField W q P R → IsVelocityOf w W →
      ∀ s y, W s y = profileBilin W W s y

def DecayBounds (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (C : ℝ) : Prop :=
  (∀ s y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W s) y‖ ≤ C / (1 + ‖y‖) ^ (j + 1)) ∧
    ∀ s y, ‖fderiv ℝ (q s) y‖ ≤ C / (1 + ‖y‖) ^ 3

def FarFieldDecay : Prop :=
  ∀ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space),
    IsRegularOrbitField W q P R → ∃ C, DecayBounds W q C

end Breakdown.FarField
