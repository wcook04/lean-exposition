import Breakdown.FracCert.StFreeNice

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

def axialTurnC (z : Freq.CSpace) : Freq.CSpace :=
  EuclideanSpace.single 0 (-(z 1)) + EuclideanSpace.single 1 (z 0)

def IsProfileSymbol (α : ℝ) (w : Space → Freq.CSpace) : Prop :=
  ContDiffOn ℝ ∞ w {ξ | ξ ≠ 0} ∧ (∃ R : ℝ, ∀ ξ : Space, R < ‖ξ‖ → w ξ = 0) ∧
    (∀ j : ℕ, ∃ C : ℝ, ∀ ξ : Space, ξ ≠ 0 → ‖iteratedFDeriv ℝ j w ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 4 - (j : ℝ))) ∧
    (∀ ξ, w (-ξ) = Freq.conjVec (w ξ)) ∧ ∀ ξ, ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * w ξ i = 0

def profileSymbolLhs (α a : ℝ) (w : Space → Freq.CSpace) (ξ : Space) : Freq.CSpace :=
  (1 - 2 / α) • w ξ - (1 / (2 * α)) • fderiv ℝ w ξ ξ
    + a • (fderiv ℝ w ξ (axialTurn ξ) - axialTurnC (w ξ)) + freqPow (2 * α) ξ • w ξ

def FreeSymbolExistsStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (m : ℕ) (s : Space → Freq.CSpace), Freq.IsNiceSymbol s →
    IsClassField m (Freq.niceField s) →
    ∃ w : Space → Freq.CSpace, IsProfileSymbol α w ∧ IsClassField m (Freq.niceField w) ∧
      ∀ ξ : Space, ξ ≠ 0 → profileSymbolLhs α a w ξ = s ξ

def ProfileSymbolRealizeStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (m : ℕ) (w : Space → Freq.CSpace), IsProfileSymbol α w →
    IsClassField m (Freq.niceField w) →
    IsSecondOrderField m (Freq.niceField w) (fun y => fderiv ℝ (Freq.niceField w) y)
        (fun y => fderiv ℝ (fun z => fderiv ℝ (Freq.niceField w) z) y) ∧
      IsWeakFractionalPower α (Freq.niceField w) (Freq.niceField (fun ξ => freqPow (2 * α) ξ • w ξ))

def ProfileSymbolEquationStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (s w : Space → Freq.CSpace), Freq.IsNiceSymbol s →
    IsProfileSymbol α w → (∀ ξ : Space, ξ ≠ 0 → profileSymbolLhs α a w ξ = s ξ) →
    MemLp (driftField α a (Freq.niceField w) (fun y => fderiv ℝ (Freq.niceField w) y)) 2 volume ∧
      ∀ᵐ y ∂volume, driftField α a (Freq.niceField w) (fun y => fderiv ℝ (Freq.niceField w) y) y
        + Freq.niceField (fun ξ => freqPow (2 * α) ξ • w ξ) y = Freq.niceField s y

def ProfileSymbolSmoothStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ w : Space → Freq.CSpace, IsProfileSymbol α w →
    ContDiff ℝ 2 (Freq.niceField w) ∧
      ∀ y, ∑ i : Fin 3, inner ℝ (fderiv ℝ (Freq.niceField w) y (unitVector i)) (unitVector i) = 0

def ProfileSymbolSixStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ w : Space → Freq.CSpace, IsProfileSymbol α w →
    MemLp (Freq.niceField w) 6 volume

def ProfileSymbolEnergyStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ w : Space → Freq.CSpace, IsProfileSymbol α w →
    Integrable (fun y => entrySq (fderiv ℝ (Freq.niceField w) y)) ∧
      Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun z => fderiv ℝ (Freq.niceField w) z) y (unitVector i) (unitVector j)‖ ^ 2)

def ProfileSymbolPowerStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ w : Space → Freq.CSpace, IsProfileSymbol α w →
    IsWeakFractionalPower α (Freq.niceField w) (Freq.niceField (fun ξ => freqPow (2 * α) ξ • w ξ))

end SteadyCert

end Breakdown
