import Breakdown.CertTorus.KernelStatements

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

open Freq

def heatConv (τ : ℝ) (f : Space → Space) (y : Space) : Space := ∫ z, heatKernel τ (y - z) • f z

def HeatConvTest : Prop :=
  ∀ ψ : Space → Space, IsTestField ψ → ∀ τ : ℝ, 0 < τ →
    IsDecayField (heatConv τ ψ) ∧ heatX τ (embedX ψ) = embedX (heatConv τ ψ)

def HeatVelocity : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ x : X,
    (velocity (heatX τ x) : Space → Space) =ᵐ[volume] heatConv τ (velocity x : Space → Space)

def KernelContraction : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ χ : Space → Space, IsTestField χ → ∀ j k : Fin 3, ∀ x : Space,
    ∫ z, ∑ i : Fin 3, lerayKernel i j k τ (x - z) * χ z i = fderiv ℝ (heatConv τ χ) x (unitVector k) j

def KernelConvTestDecay : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ φ : Space → Space, IsTestField φ →
    IsDecayField (fun y => -kernelConv τ (tensorField φ φ) y)

def BilinTestKernel : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ φ : Space → Space, IsTestField φ →
    bilinX τ (embedX φ) (embedX φ) = embedX (fun y => -kernelConv τ (tensorField φ φ) y)

def KernelConvL3Pointwise : Prop :=
  ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ∀ F : Space → Fin 3 → Fin 3 → ℝ, MemLp F 3 volume → ∀ y : Space,
    (∀ i : Fin 3, Integrable (fun z => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k)) ∧
      ‖kernelConv τ F y‖ ≤ C * τ ^ (-(1 : ℝ)) * (eLpNorm F 3 volume).toReal

def BilinKernel : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ u : X,
    (velocity (bilinX τ u u) : Space → Space) =ᵐ[volume]
      fun y => -kernelConv τ (tensorField (velocity u : Space → Space) (velocity u : Space → Space)) y

end Breakdown.FarField
