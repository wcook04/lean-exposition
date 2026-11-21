import Breakdown.FracCert.StDecay
import Breakdown.Uniqueness.FundSolDefs
import Breakdown.FracCert.WeakRegularParts
import Breakdown.FracCert.StKernel

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.FundSol

def PressureModelStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ProfileDecay α U → ∃ Q : Space → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ y, scalarSumSecondPartials Q y = -divergenceAt (advectionAt (profileField U)) y) ∧
      ∀ j : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ (j + 1) Q y‖ ≤ C * (1 + ‖y‖) ^ (-(4 * α - 1 + j))

def PressureTraceStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ProfileDecay α U →
      ∀ y, scalarSumSecondPartials (profilePressure U) y = -divergenceAt (advectionAt (profileField U)) y

def ModelPressureDecayStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ProfileDecay α U → ∀ j : ℕ, ∃ C : ℝ, ∀ y,
      ‖iteratedFDeriv ℝ (j + 1) (profilePressure U) y‖ ≤ C * (1 + ‖y‖) ^ (-(4 * α - 1 + j))

def pressureMultiplier (i j : Fin 3) (ξ : Space) : ℂ := ((-(ξ i * ξ j / ‖ξ‖ ^ 2) : ℝ) : ℂ)

def ProductWeightedSmoothStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ProfileDecay α U → ∀ i j : Fin 3,
      IsWeightedSmooth (fun y => ((profileField U y i * profileField U y j : ℝ) : ℂ)) (4 * α - 2)

def PressureRepresentationStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ProfileDecay α U → ∃ F : Fin 3 → Fin 3 → Space → ℂ,
      (∀ i j, IsTransformOf (F i j) (fun y => ((profileField U y i * profileField U y j : ℝ) : ℂ))) ∧
      (∀ i j, HasMomentsInL1 (fun ξ => pressureMultiplier i j ξ * F i j ξ)) ∧
      ∀ y, profilePressure U y =
        ∑ i, ∑ j, (FourierTransform.fourierInv (fun ξ => pressureMultiplier i j ξ * F i j ξ) y).re

def ResidualDivergenceStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ProfileDecay α U → ∀ P : Space → ℝ, ContDiff ℝ ∞ P →
    (∀ y, rotatingProfileResidual α a 1 (profileField U) P y = 0) →
      ∀ y, scalarSumSecondPartials P y = -divergenceAt (advectionAt (profileField U)) y

def PowerDivergenceFreeStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (a : ℝ) (U : X), IsWeakRotatingProfile α a U → HasAllMoments U →
    ProfileDecay α U → ∀ y, divergenceAt (fractionalPowerAt α (profileField U)) y = 0

def DecayingGradientVanishesStatement : Prop :=
  ∀ h : Space → ℝ, ContDiff ℝ ∞ h → (∀ y, scalarSumSecondPartials h y = 0) →
    ∀ K s : ℝ, 0 < s → (∀ y, ‖fderiv ℝ h y‖ ≤ K * (1 + ‖y‖) ^ (-s)) → ∀ y, fderiv ℝ h y = 0

end Breakdown.FracCert
