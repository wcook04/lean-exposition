import Breakdown.Frac.StTorusStepApprox
import Breakdown.Torus.ApproxSizes

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

def fracCutAt (α a : ℝ) (U : Space → Space) (T t ℓ : ℝ) (y : Space) : Space :=
  ℓ ^ (1 - 1 / (2 * α)) • fracApproxField α a U T t (center + ℓ ^ (1 / (2 * α)) • y)

def FracCutoffClose (α : ℝ) : Prop :=
  ∀ (a : ℝ) (U : Space → Space) (P : Space → ℝ), IsRotatingProfile α a 1 U P →
    (∀ η : ℝ, 0 < η → ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T → T - t < ℓ₀ →
      gradEnergy (rotatingSlice a U (similarityTime T t) - fracCutAt α a U T t (T - t)) ≤ η) ∧
    ∃ K : ℝ, ∀ T t : ℝ, 0 < T → T ≤ 1 → 0 ≤ t → t < T →
      ∫ y, ‖fracCutAt α a U T t (T - t) y‖ ^ 2 ≤ K * (T - t) ^ (-((5 - 4 * α) / (2 * α)))

end Breakdown.Periodic
