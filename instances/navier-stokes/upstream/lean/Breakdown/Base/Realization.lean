import Breakdown.Base.Framework

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

def pushForward (R : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) : Space → Space :=
  fun y => R (f (R.symm y))

def dilateField (μ : ℝ) (f : Space → Space) : Space → Space :=
  fun y => Real.sqrt μ • f (Real.sqrt μ • y)

def IsDecayField (f : Space → Space) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ y, divergenceAt f y = 0) ∧
    ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C / (1 + ‖y‖) ∧ ‖fderiv ℝ f y‖ ≤ C / (1 + ‖y‖) ^ 2

def IsTestField (φ : Space → Space) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ ∀ y, divergenceAt φ y = 0

def gradientPairing (u φ : Space → Space) : ℝ :=
  ∫ x, ∑ i : Fin 3, inner ℝ (fderiv ℝ u x (unitVector i)) (fderiv ℝ φ x (unitVector i))

def advectionPairing (u φ : Space → Space) : ℝ :=
  ∫ x, inner ℝ (advectionAt u x) (φ x)

def fieldPairing (u φ : Space → Space) : ℝ :=
  ∫ x, inner ℝ (u x) (φ x)

structure Realization (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] where
  F : MildFramework X
  rot : (Space ≃ₗᵢ[ℝ] Space) → X ≃ₗᵢ[ℝ] X
  rot_commutes : ∀ R, F.Commutes (rot R)
  embed : (Space → Space) → X
  embed_sub : ∀ f g, IsDecayField f → IsDecayField g → embed (f - g) = embed f - embed g
  embed_norm : ∀ f, IsDecayField f →
    ‖embed f‖ ^ 2 = ∫ y, ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2
  embed_ne_zero : ∀ f, IsDecayField f → (∃ y, f y ≠ 0) → embed f ≠ 0
  embed_rot : ∀ R f, IsDecayField f → rot R (embed f) = embed (pushForward R f)
  embed_dilate : ∀ μ f, 0 < μ → IsDecayField f → F.D μ (embed f) = embed (dilateField μ f)
  mild_of_weak : ∀ (v : ℝ → Space → Space) (a b : ℝ), a < b →
    (∀ t ∈ Icc a b, IsDecayField (v t)) →
    ContinuousOn (fun t => embed (v t)) (Icc a b) →
    (∀ t ∈ Icc a b, ∀ t' ∈ Icc a b, Integrable (fun x => ‖v t x - v t' x‖ ^ 2)) →
    (∀ t₀ ∈ Icc a b, Filter.Tendsto (fun t => ∫ x, ‖v t x - v t₀ x‖ ^ 2)
      (nhdsWithin t₀ (Icc a b)) (nhds 0)) →
    (∀ φ, IsTestField φ → ∀ t ∈ Ioo a b,
      HasDerivAt (fun τ => fieldPairing (v τ) φ)
        (-gradientPairing (v t) φ - advectionPairing (v t) φ) t) →
    (∀ φ, IsTestField φ → ContinuousOn (fun τ => fieldPairing (v τ) φ) (Icc a b)) →
    F.IsMildOnIcc (fun t => embed (v t)) a b
  test : Submodule ℝ X
  test_dense : Dense (test : Set X)
  test_spec : ∀ x ∈ test, ∃ φ, IsTestField φ ∧ embed φ = x

def ProfileOrbitHolds : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Realization X), PeriodicSimilarityProfileExists →
    ∃ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space), Rlz.F.IsOrbit (Rlz.rot R) w P

end Breakdown
