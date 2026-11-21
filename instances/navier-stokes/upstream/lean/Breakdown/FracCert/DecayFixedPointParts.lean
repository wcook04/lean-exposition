import Breakdown.FracCert.StDecay

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

def FarFieldWeightedStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), HasAllMoments U →
    MemLp (fun y => (1 + ‖y‖)⁻¹ • farFieldOp α a (tensorSq (profileField U)) y) 2 volume

def FixedPointAnnulusStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ∀ m : Space → CSpace, (∀ ξ, m (-ξ) = conjVec (m ξ)) → ContDiff ℝ ∞ m →
      HasCompactSupport m → (∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → m ξ = 0) →
      ∫ y, inner ℝ (profileField U y - farFieldOp α a (tensorSq (profileField U)) y) (physField m y) = 0

def ProfileMildFormStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ∀ φ, IsNiceField φ → ∫ y, inner ℝ (profileField U y) (φ y) =
      -∫ τ in Ioi (0 : ℝ), trilinear U U (heatField α (1 - Real.exp (-τ)) (simAdj α a (Real.exp τ) φ))

def FarFieldPairingStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), HasAllMoments U →
    ∀ φ, IsNiceField φ → ∫ y, inner ℝ (farFieldOp α a (tensorSq (profileField U)) y) (φ y) =
      -∫ τ in Ioi (0 : ℝ), trilinear U U (heatField α (1 - Real.exp (-τ)) (simAdj α a (Real.exp τ) φ))

def ProfileGradientFreeStatement : Prop :=
  ∀ U : X, HasAllMoments U →
    ∀ q : Space → CSpace, (∀ ξ, q (-ξ) = conjVec (q ξ)) → ContDiff ℝ ∞ q →
      HasCompactSupport q → (∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → q ξ = 0) →
      (∃ c : Space → ℂ, ∀ ξ, q ξ = c ξ • freqVec ξ) →
      ∫ y, inner ℝ (profileField U y) (physField q y) = 0

def FarFieldGradientFreeStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), HasAllMoments U →
    ∀ q : Space → CSpace, (∀ ξ, q (-ξ) = conjVec (q ξ)) → ContDiff ℝ ∞ q →
      HasCompactSupport q → (∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → q ξ = 0) →
      (∃ c : Space → ℂ, ∀ ξ, q ξ = c ξ • freqVec ξ) →
      ∫ y, inner ℝ (farFieldOp α a (tensorSq (profileField U)) y) (physField q y) = 0

end Breakdown.FracCert
