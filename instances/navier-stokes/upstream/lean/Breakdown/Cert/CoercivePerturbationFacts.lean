import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

def PerturbationLocalIntegrabilityHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g →
    LocallyIntegrable (fun z : ℝ × Space => v z.1 z.2) volume ∧
      LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume ∧
      LocallyIntegrable (fun z : ℝ × Space => H z.1 z.2) volume

def PerturbationSecondDerivBoundHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g →
    periodLIntegral (fun σ y => secondDerivSq (H σ y)) ≤ periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)

def PerturbationLocalSquareIntegrabilityHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g →
    ∀ R : ℝ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖v σ y‖ ^ 2) < ⊤

end Coercive

end Breakdown
