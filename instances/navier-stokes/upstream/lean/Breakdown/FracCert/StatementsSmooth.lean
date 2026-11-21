import Breakdown.Frac.StRealize
import Breakdown.Uniqueness.RegDefs

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

def symbolX (x : X) (ξ : Space) : CSpace := ((2 * π * ‖ξ‖)⁻¹ : ℝ) • (x : L2C) ξ

def HasAllMoments (x : X) : Prop := ∀ k : ℕ, 1 ≤ k → homNormSq k (symbolX x) < ⊤

def fracHomSq (s : ℝ) (x : X) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * s)) * ‖symbolX x ξ‖ₑ ^ 2

def IsConcreteFrame (α : ℝ) (F : ScaledMildFramework X (dilExponent α)) : Prop :=
  F.G = fracHeatX α ∧ F.K = fracBilinX α

def MildFirstGainStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ F : ScaledMildFramework X (dilExponent α), IsConcreteFrame α F →
    ∀ (u : ℝ → X) (t : ℝ), 0 < t → F.IsMildOnIcc u 0 t → ∀ σ ∈ Ioc 0 t, ∃ C : ℝ,
      ∀ s ∈ Icc σ t, fracHomSq (α + 1 / 2) (u s) ≤ ENNReal.ofReal C

def SupFromGainStatement : Prop :=
  ∀ s : ℝ, 3 / 2 < s → ∃ C : ℝ, ∀ x : X, fracHomSq s x < ⊤ →
    freqL1Norm (symbolX x) ≤ ENNReal.ofReal C * (homNormSq 1 (symbolX x) ^ (1 / 2 : ℝ) + fracHomSq s x ^ (1 / 2 : ℝ))

def MildMomentStepStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ F : ScaledMildFramework X (dilExponent α), IsConcreteFrame α F →
    ∀ (u : ℝ → X) (t : ℝ), 0 < t → F.IsMildOnIcc u 0 t → ∀ k : ℕ, 1 ≤ k →
    (∀ σ ∈ Ioc 0 t, ∃ C : ℝ, ∀ s ∈ Icc σ t,
      freqL1Norm (symbolX (u s)) + homNormSq k (symbolX (u s)) ≤ ENNReal.ofReal C) →
    ∀ σ ∈ Ioc 0 t, ∃ C : ℝ, ∀ s ∈ Icc σ t, homNormSq (k + 1) (symbolX (u s)) ≤ ENNReal.ofReal C

def MildSmoothingStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ F : ScaledMildFramework X (dilExponent α), IsConcreteFrame α F →
    ∀ (u : ℝ → X) (t : ℝ), 0 < t → F.IsMildOnIcc u 0 t → ∀ σ ∈ Ioc 0 t, HasAllMoments (u σ)

end Breakdown.FracCert
