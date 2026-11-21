import Breakdown.FracCert.StDecay

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

def HeatDivPairingStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ U : X, HasAllMoments U → ∀ t : ℝ, 0 < t → t < 1 →
    ∀ χ, IsNiceField χ → ∫ y, inner ℝ (heatDivConv α t (tensorSq (profileField U)) y) (χ y) =
      trilinear U U (heatField α t χ)

def HeatDivTransposeStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ t : ℝ, 0 < t → t < 1 →
    ∀ F : Space → Fin 3 → Fin 3 → ℝ, Continuous F → (∃ B : ℝ, ∀ y, ‖F y‖ ≤ B) →
    ∀ χ, IsNiceField χ → ∫ y, inner ℝ (heatDivConv α t F y) (χ y) =
      -∑ j : Fin 3, ∑ k : Fin 3, ∫ z, F z j k * partialField (heatField α t χ) k z j

def TrilinearByPartsStatement : Prop :=
  ∀ U : X, HasAllMoments U → ∀ ψ, IsNiceField ψ →
    trilinear U U ψ = -∑ j : Fin 3, ∑ k : Fin 3, ∫ z, tensorSq (profileField U) z j k * partialField ψ k z j

def KernelTransposeStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ t : ℝ, 0 < t → t < 1 → ∀ χ, IsNiceField χ → ∀ (j k : Fin 3) (z : Space),
    ∑ i : Fin 3, ∫ y, (projDivKernel α t i j k (y - z)).re * χ y i = -partialField (heatField α t χ) k z j

end Breakdown.FracCert
