import Breakdown.FracCert.Defs
import Breakdown.FreqTr.Basic

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

def secondSymbol (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Freq.L2C :=
  Freq.freqTrR (Freq.complexify (Freq.toLpOrZero 2 (negSecondTrace H)))

def fieldSymbol (P : Space → Space) : Freq.L2C := Freq.freqTrR (Freq.complexify (Freq.toLpOrZero 2 P))

def freqPow (s : ℝ) (ξ : Space) : ℝ := (2 * π * ‖ξ‖) ^ s

def fullSecondSq (H : Space →L[ℝ] Space →L[ℝ] Space) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ‖H (unitVector i) (unitVector j)‖ ^ 2

def SecondSymbolEnergyStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    Integrable (fun ξ => ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ) ∧
    ∫ y, entrySq (G y) = ∫ ξ, ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ ∧
    ∫ y, fullSecondSq (H y) = ∫ ξ, ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 ∧
    ∫ y, ‖secondTrace (H y)‖ ^ 2 = ∫ ξ, ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2

def WeakPowerSymbolStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 3 / 2 → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space), IsSecondOrderField m v G H →
    IsWeakFractionalPower α v P →
    (fieldSymbol P : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => freqPow (2 * α - 2) ξ • (secondSymbol H : Space → Freq.CSpace) ξ

def DriftEnergyStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    MemLp (driftField α a v G) 2 volume →
    l2Pair (driftField α a v G) (negSecondTrace H) = (1 - 3 / (4 * α)) * ∫ y, entrySq (G y)

def DriftPowerStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space), IsSecondOrderField m v G H →
    IsWeakFractionalPower α v P → MemLp (driftField α a v G) 2 volume →
    Integrable (fun ξ => freqPow (2 * α - 4) ξ * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2) ∧
    l2Pair (driftField α a v G) P =
      (3 / 2 - 5 / (4 * α)) * ∫ ξ, freqPow (2 * α - 4) ξ * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2

def SecondOrderCompleteStatement : Prop :=
  ∀ (m : ℕ) (w : Space → ℝ) (wmin : ℝ), 0 < wmin → Measurable w → (∀ y, wmin ≤ w y) →
    (∃ wmax : ℝ, ∀ y, w y ≤ wmax) →
    ∀ (v : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
      (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)), (∀ n, IsSecondOrderField m (v n) (G n) (H n)) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N,
        weightedEnergy w (fun y => G n y - G n' y) (fun y => H n y - H n' y) < ε) →
      ∃ (v₀ : Space → Space) (G₀ : Space → (Space →L[ℝ] Space))
        (H₀ : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v₀ G₀ H₀ ∧
        Filter.Tendsto (fun n => weightedEnergy w (fun y => G n y - G₀ y) (fun y => H n y - H₀ y))
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun n => ∫ y, ‖v n y - v₀ y‖ ^ 6) Filter.atTop (nhds 0)

def SecondOrderLinearStatement : Prop :=
  ∀ (m : ℕ) (v u : Space → Space) (G K : Space → (Space →L[ℝ] Space))
    (H L : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (c : ℝ),
    IsSecondOrderField m v G H → IsSecondOrderField m u K L →
    IsSecondOrderField m (fun y => v y + c • u y) (fun y => G y + c • K y) (fun y => H y + c • L y)

def FreeUniqueStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space), IsSecondOrderField m v G H →
    IsWeakFractionalPower α v P → MemLp (driftField α a v G) 2 volume →
    (∀ᵐ y ∂volume, driftField α a v G y + P y = 0) →
    (∀ᵐ y ∂volume, v y = 0) ∧ (∀ᵐ y ∂volume, G y = 0) ∧ (∀ᵐ y ∂volume, H y = 0) ∧ ∀ᵐ y ∂volume, P y = 0

def FreeBoundsStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∃ C₀ : ℝ, ∀ (a : ℝ) (m : ℕ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P F : Space → Space),
    IsSecondOrderField m v G H → IsWeakFractionalPower α v P → MemLp (driftField α a v G) 2 volume →
    MemLp F 2 volume → (∀ᵐ y ∂volume, driftField α a v G y + P y = F y) →
    l2Norm P ≤ l2Norm F ∧ l2Norm (driftField α a v G) ≤ l2Norm F ∧
    (1 - 3 / (4 * α)) * (∫ y, entrySq (G y)) + l2Pair P (negSecondTrace H) = l2Pair F (negSecondTrace H) ∧
    Real.sqrt (∫ y, ‖secondTrace (H y)‖ ^ 2) + Real.sqrt (∫ y, entrySq (G y)) ≤ C₀ * l2Norm F

def FreeExistsStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (F : Space → Space), IsSolenoidalL2 F → IsClassField m F →
    ∃ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
      (P : Space → Space), IsSecondOrderField m v G H ∧ IsWeakFractionalPower α v P ∧
      MemLp (driftField α a v G) 2 volume ∧ ∀ᵐ y ∂volume, driftField α a v G y + P y = F y

def InverseSquareBoundStatement : Prop :=
  ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable v volume →
    MemLp v 6 volume → Integrable (fun y => entrySq (G y)) → IsWeakGradientOf v G →
    Integrable (fun y => ‖v y‖ ^ 2 / ‖y‖ ^ 2) ∧ ∫ y, ‖v y‖ ^ 2 / ‖y‖ ^ 2 ≤ 4 * ∫ y, entrySq (G y)

def ProfileProductCompactStatement : Prop :=
  ∀ (m : ℕ) (W : Space → Space) (C : ℝ), ContDiff ℝ 1 W →
    (∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖fderiv ℝ W y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) →
    ∀ (v : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
      (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (B : ℝ), (∀ n, IsSecondOrderField m (v n) (G n) (H n)) →
      (∀ n, (∫ y, entrySq (G n y)) + (∫ y, ‖secondTrace (H n y)‖ ^ 2) ≤ B) →
      ∃ (φ : ℕ → ℕ) (L : Space → Space), StrictMono φ ∧ MemLp L 2 volume ∧
        Filter.Tendsto (fun n => ∫ y, ‖symProduct W (fun z => fderiv ℝ W z) (v (φ n)) (G (φ n)) y - L y‖ ^ 2)
          Filter.atTop (nhds 0)

end SteadyCert

end Breakdown
