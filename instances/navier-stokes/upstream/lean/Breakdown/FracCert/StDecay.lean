import Breakdown.FracCert.StKernel
import Breakdown.FracCert.StWeakRegular
import Breakdown.FracCert.StMildProfile

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

def tensorSq (V : Space → Space) (y : Space) : Fin 3 → Fin 3 → ℝ := fun j k => V y j * V y k

def heatDivConv (α t : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (x : Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (fun i => ∑ j : Fin 3, ∑ k : Fin 3, ∫ z, (projDivKernel α t i j k (x - z)).re * F z j k)

def farFieldOp (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (y : Space) : Space :=
  -∫ τ in Ioi (0 : ℝ), pushForward (axialRotation (a * τ))
    (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) F)) y

def profileField (U : X) : Space → Space := physField (symbolX U)

def HeatDivBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (β b : ℝ) (j : ℕ), 0 ≤ β → β < 3 → 0 ≤ b → b ≤ β + 1 + j →
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ (F : Space → Fin 3 → Fin 3 → ℝ) (A B : ℝ), ContDiff ℝ j F →
      (∀ y, (1 + ‖y‖) ^ b * ‖iteratedFDeriv ℝ j F y‖ ≤ A) → (∀ y, (1 + ‖y‖) ^ β * ‖F y‖ ≤ B) →
      ∀ x, (1 + ‖x‖) ^ b * ‖iteratedFDeriv ℝ j (heatDivConv α t F) x‖ ≤ C * t ^ (-(1 / (2 * α))) * (A + B)

def FarFieldBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a β b : ℝ) (j : ℕ), 0 ≤ β → β < 3 → 0 ≤ b → b ≤ β + 1 + j →
    b ≠ 2 * α - 1 + j →
    ∃ C : ℝ, ∀ (F : Space → Fin 3 → Fin 3 → ℝ) (A B : ℝ), ContDiff ℝ j F →
      (∀ y, (1 + ‖y‖) ^ b * ‖iteratedFDeriv ℝ j F y‖ ≤ A) → (∀ y, (1 + ‖y‖) ^ β * ‖F y‖ ≤ B) →
      ContDiff ℝ j (farFieldOp α a F) ∧
      ∀ y, (1 + ‖y‖) ^ (min b (2 * α - 1 + j)) * ‖iteratedFDeriv ℝ j (farFieldOp α a F) y‖ ≤ C * (A + B)

def ProfileFixedPointStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ∀ y, profileField U y = farFieldOp α a (tensorSq (profileField U)) y

def ProfileDecayBaseStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ∃ C : ℝ, ∀ y, ‖profileField U y‖ ≤ C * (1 + ‖y‖) ^ (-(2 * α - 1))

def ProfileDecayStepStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ∀ j : ℕ, (∀ i < j, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ i (profileField U) y‖ ≤
        C * (1 + ‖y‖) ^ (-(2 * α - 1 + i))) →
      ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (profileField U) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 * α - 1 + j))

def ProfileDecay (α : ℝ) (U : X) : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (profileField U) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 * α - 1 + j))

def PowerDecayStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ProfileDecay α U → ContDiff ℝ ∞ (fractionalPowerAt α (profileField U)) ∧
      ∀ j : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (fractionalPowerAt α (profileField U)) y‖ ≤
        C * (1 + ‖y‖) ^ (-(4 * α - 1 + j))

def PressureDecayStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ProfileDecay α U → ∀ P : Space → ℝ, ContDiff ℝ ∞ P →
    (∀ y, rotatingProfileResidual α a 1 (profileField U) P y = 0) →
      ∀ j : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ (j + 1) P y‖ ≤ C * (1 + ‖y‖) ^ (-(4 * α - 1 + j))

def ProfileNonzeroStatement : Prop :=
  ∀ (U : X), U ≠ 0 → HasAllMoments U → ∃ y, profileField U y ≠ 0

end Breakdown.FracCert
