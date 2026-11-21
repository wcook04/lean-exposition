import Breakdown.FreqTr.Basic
import Breakdown.Uniqueness.Basic

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def hsWeight (m : ℕ) (ξ : Space) : ℝ := (1 + ‖ξ‖ ^ 2) ^ m

def hsNormSq (m : ℕ) (f : Space → CSpace) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2

def homNormSq (k : ℕ) (f : Space → CSpace) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖f ξ‖ₑ ^ 2

def freqL1Norm (f : Space → CSpace) : ℝ≥0∞ := ∫⁻ ξ, ‖f ξ‖ₑ

def gradFreqL1Norm (f : Space → CSpace) : ℝ≥0∞ := ∫⁻ ξ, ENNReal.ofReal ‖ξ‖ * ‖f ξ‖ₑ

def heatSymbol (t : ℝ) (ξ : Space) : ℝ := Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2))

def divFreeC (ξ : Space) (z : CSpace) : CSpace :=
  z - ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ((ξ i : ℝ) : ℂ) * z i) • freqVec ξ

def convC (f g : Space → ℂ) (ξ : Space) : ℂ := ∫ η, f η * g (ξ - η)

def advectionBilin (f g : Space → CSpace) (ξ : Space) : CSpace :=
  WithLp.toLp 2 (fun i => ∑ j, convC (fun η => f η j)
    (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * g η i) ξ)

def advectionSymbol (f : Space → CSpace) : Space → CSpace := advectionBilin f f

def nonlinSymbol (f : Space → CSpace) (ξ : Space) : CSpace := -divFreeC ξ (advectionSymbol f ξ)

def pressureSymbol (f : Space → CSpace) (ξ : Space) : ℂ :=
  -(∑ i, ((ξ i : ℝ) : ℂ) * advectionSymbol f ξ i) / (2 * (π : ℂ) * Complex.I * (((‖ξ‖ ^ 2 : ℝ)) : ℂ))

def IsSolenoidalSymbol (f : Space → CSpace) : Prop :=
  ∀ ξ, (∑ i, ((ξ i : ℝ) : ℂ) * f ξ i = 0) ∧ f (-ξ) = conjVec (f ξ)

def IsVarConstSymbol (F : ℝ → Space → CSpace) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ ξ, F t ξ = ((heatSymbol (t - a) ξ : ℝ) : ℂ) • F a ξ +
    ∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ

def IsHsCurve (m : ℕ) (F : ℝ → Space → CSpace) (a b : ℝ) : Prop :=
  (∀ t ∈ Icc a b, AEStronglyMeasurable (F t) volume ∧ hsNormSq m (F t) < ⊤) ∧
    ∀ t₀ ∈ Icc a b, Tendsto (fun t => hsNormSq m (F t - F t₀)) (𝓝[Icc a b] t₀) (𝓝 0)

def symbolOf (φ : Space → Space) : Space → CSpace := 𝓕 (fun x => complexifyVec (φ x))

def physField (f : Space → CSpace) (x : Space) : Space := realVec (𝓕⁻ f x)

def physScalar (g : Space → ℂ) (x : Space) : ℝ := (𝓕⁻ g x).re

end Breakdown.SmoothFlow
