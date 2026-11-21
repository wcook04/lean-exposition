import Breakdown.Weak.Basic

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

def PairingVelocity : Prop :=
  ∀ (x : X) (φ : Space → Space), IsTestField φ →
    inner ℝ x (embedX φ) = ∫ y, inner ℝ ((velocity x : Space → Space) y) (negSsp φ y)

def VelocityWeakGradient : Prop :=
  ∀ (x : X) (φ : Space → ℝ), IsTestFunction φ → ∀ j : Fin 3,
    ∫ y, φ y • (partialX j x : Space → Space) y =
      -∫ y, fderiv ℝ φ y (unitVector j) • (velocity x : Space → Space) y

def ZeroGradientSix : Prop :=
  ∀ f : Space → Space, MemLp f 6 volume →
    (∀ φ : Space → ℝ, IsTestFunction φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • f y = 0) →
    f =ᵐ[volume] 0

def GradientFreqTr : Prop :=
  ∀ (f : Space → Space) (g : Space → (Space →L[ℝ] Space)) (C : ℝ), IsSlice f g C →
    ∃ x : X, ∀ j, (partialX j x : Space → Space) =ᵐ[volume] gradComponent g j

def SliceEmbedding : Prop :=
  PairingVelocity → VelocityWeakGradient → ZeroGradientSix → GradientFreqTr →
  ∀ (f : Space → Space) (g : Space → (Space →L[ℝ] Space)) (C : ℝ), IsSlice f g C →
    ∃ x : X, (velocity x : Space → Space) =ᵐ[volume] f ∧
      (∀ j, (partialX j x : Space → Space) =ᵐ[volume] gradComponent g j) ∧
      ‖x‖ ^ 2 ≤ 3 * max C 0

def AdvectionByParts : Prop :=
  ∀ (x : X) (ψ : Space → Space), IsTestField ψ →
    ∫ y, ∑ i : Fin 3, (velocity x : Space → Space) y i *
      inner ℝ ((velocity x : Space → Space) y) (fderiv ℝ ψ y (unitVector i)) = -trilinear x x ψ

def PairingDilate : Prop :=
  PairingVelocity → ∀ μ : ℝ, 0 < μ → ∀ (x : X) (φ : Space → Space), IsTestField φ →
    inner ℝ (dilX μ x) (embedX φ) = inner ℝ x (embedX (spaceScale (Real.sqrt μ)⁻¹ φ))

def TrilinearDilate : Prop :=
  VelocityWeakGradient → ∀ μ : ℝ, 0 < μ → ∀ (x : X) (ψ : Space → Space), IsTestField ψ →
    trilinear (dilX μ x) (dilX μ x) ψ = trilinear x x (spaceScale (Real.sqrt μ)⁻¹ ψ)

end Breakdown.WeakProfile
