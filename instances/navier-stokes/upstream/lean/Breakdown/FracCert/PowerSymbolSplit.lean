import Breakdown.FracCert.StFree
import Breakdown.Frac.StRealize

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

def IsBandSymbol (m : Space → Freq.CSpace) : Prop :=
  ContDiff ℝ ∞ m ∧ HasCompactSupport m ∧ (∃ r > 0, ∀ ξ : Space, ‖ξ‖ < r → m ξ = 0) ∧
    ∀ ξ, m (-ξ) = Freq.conjVec (m ξ)

def RapidWeakPowerStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ v P : Space → Space, AEStronglyMeasurable v volume →
    MemLp v 6 volume → IsWeakFractionalPower α v P → ∀ φ : SchwartzMap Space Space,
    ∫ y, inner ℝ (P y) (φ y) = ∫ y, inner ℝ (v y) (fractionalPowerAt α φ y)

def RapidSecondPairStatement : Prop :=
  ∀ (k : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField k v G H →
    ∀ φ : SchwartzMap Space Space,
    ∫ y, inner ℝ (v y) (Freq.negSsp φ y) = ∫ y, inner ℝ (negSecondTrace H y) (φ y)

def BandWeakPowerStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ v P : Space → Space, AEStronglyMeasurable v volume →
    MemLp v 6 volume → IsWeakFractionalPower α v P → ∀ m, IsBandSymbol m →
    ∫ y, inner ℝ (P y) (Freq.niceField m y) = ∫ y, inner ℝ (v y) (fractionalPowerAt α (Freq.niceField m) y)

def BandSecondPairStatement : Prop :=
  ∀ (k : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField k v G H →
    ∀ m, IsBandSymbol m →
    ∫ y, inner ℝ (v y) (Freq.negSsp (Freq.niceField m) y) =
      ∫ ξ, inner ℝ ((secondSymbol H : Space → Freq.CSpace) ξ) (m ξ)

def BandPairStatement : Prop :=
  ∀ F : Space → Space, MemLp F 2 volume → ∀ m, IsBandSymbol m →
    ∫ y, inner ℝ (F y) (Freq.niceField m y) = ∫ ξ, inner ℝ ((fieldSymbol F : Space → Freq.CSpace) ξ) (m ξ)

def BandScaleStatement : Prop :=
  ∀ s : ℝ, 0 < s → ∀ m, IsBandSymbol m → IsBandSymbol (fun ξ => freqPow s ξ • m ξ)

def BandPowerTraceStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ m, IsBandSymbol m →
    fractionalPowerAt α (Freq.niceField m) = Freq.negSsp (Freq.niceField (fun ξ => freqPow (2 * α - 2) ξ • m ξ))

def SymbolConjSymStatement : Prop :=
  ∀ F : Space → Space, ∀ᵐ ξ ∂volume,
    (fieldSymbol F : Space → Freq.CSpace) (-ξ) = Freq.conjVec ((fieldSymbol F : Space → Freq.CSpace) ξ)

def BandUniqueStatement : Prop :=
  ∀ g₁ g₂ : Space → Freq.CSpace, LocallyIntegrable g₁ volume → LocallyIntegrable g₂ volume →
    (∀ᵐ ξ ∂volume, g₁ (-ξ) = Freq.conjVec (g₁ ξ)) → (∀ᵐ ξ ∂volume, g₂ (-ξ) = Freq.conjVec (g₂ ξ)) →
    (∀ m, IsBandSymbol m → ∫ ξ, inner ℝ (g₁ ξ) (m ξ) = ∫ ξ, inner ℝ (g₂ ξ) (m ξ)) →
    g₁ =ᵐ[volume] g₂

end SteadyCert

end Breakdown
