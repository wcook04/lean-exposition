import Breakdown.Defs
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

def spaceScale (b : ℝ) (φ : Space → Space) : Space → Space := fun y => φ (b • y)

def gradComponent (g : Space → (Space →L[ℝ] Space)) (j : Fin 3) : Space → Space :=
  fun y => g y (unitVector j)

def similarityScale (s₀ σ : ℝ) : ℝ := Real.exp (-(σ - s₀) / 2)

def physicalCurve (x : ℝ → X) (s₀ t : ℝ) : X := dilX (1 - t)⁻¹ (x (s₀ - Real.log (1 - t)))

def scaledTest (α : ℝ → ℝ) (s₀ : ℝ) (φ : Space → Space) : ℝ → Space → Space :=
  fun σ y => (α σ * similarityScale s₀ σ ^ 2) • negSsp φ (similarityScale s₀ σ • y)

def weakRate (u : X) (φ : Space → Space) : ℝ :=
  inner ℝ u (embedX (negSsp φ)) + trilinear u u (negSsp φ)

def sspRate (u h : X) : ℝ := inner ℝ u h + trilinear u u (velocity h)

def similarityRate (x : ℝ → X) (α : ℝ → ℝ) (s₀ : ℝ) (φ : Space → Space) (σ : ℝ) : ℝ :=
  -deriv α σ * inner ℝ (x σ) (embedX (spaceScale (similarityScale s₀ σ) φ)) +
    α σ * weakRate (x σ) (spaceScale (similarityScale s₀ σ) φ)

def varConst (y : ℝ → X) (t₀ t : ℝ) : X :=
  heatX (t - t₀) (y t₀) + ∫ τ in t₀..t, bilinX (t - τ) (y τ) (y τ)

structure IsSlice (f : Space → Space) (g : Space → (Space →L[ℝ] Space)) (C : ℝ) : Prop where
  grad : IsWeakGradient f g
  div : ∀ᵐ y, ∑ i : Fin 3, (g y (unitVector i)) i = 0
  six : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) ≤ ENNReal.ofReal C
  two : ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ 2) ≤ ENNReal.ofReal C

structure IsSliceCurve (x : ℝ → X) (W : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (M : ℝ) : Prop where
  vel : ∀ s, (velocity (x s) : Space → Space) =ᵐ[volume] W s
  part : ∀ s j, (partialX j (x s) : Space → Space) =ᵐ[volume] gradComponent (G s) j
  bound : ∀ s, ‖x s‖ ≤ M

def IsTensorWeak (y : ℝ → X) (l r : ℝ) : Prop :=
  ∀ (θ : ℝ → ℝ) (φ : Space → Space), ContDiff ℝ ∞ θ → HasCompactSupport θ →
    tsupport θ ⊆ Ioo l r → IsTestField φ →
      ∫ t, deriv θ t * inner ℝ (y t) (embedX φ) = ∫ t, θ t * weakRate (y t) φ

structure IsGoodSet (y : ℝ → X) (l r : ℝ) (E : Set ℝ) : Prop where
  sub : E ⊆ Ioo l r
  null : volume (Ioo l r \ E) = 0
  weak : ∀ s ∈ E, ∀ t ∈ E, s ≤ t → ∀ χ h : X, IsSspOf χ h →
    IntervalIntegrable (fun τ => sspRate (y τ) h) volume s t ∧
      inner ℝ (y t) χ - inner ℝ (y s) χ = -∫ τ in s..t, sspRate (y τ) h

end Breakdown.WeakProfile
