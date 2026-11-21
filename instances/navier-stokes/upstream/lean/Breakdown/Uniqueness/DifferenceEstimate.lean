import Breakdown.Uniqueness.CutoffHs
import Breakdown.Uniqueness.SimpleTerms
import Breakdown.Uniqueness.CubicTerm
import Breakdown.Uniqueness.MixedStress
import Breakdown.Uniqueness.SelfStress
import Breakdown.Uniqueness.DifferenceEstimateAux

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem differenceRHS_le : ∃ K : ℝ, ∀ (A U₀ U₁ : ℝ) (u w : Space → Space),
    IsDifferenceData A U₀ U₁ u w → ∀ r : ℝ, 1 ≤ r →
      differenceRHS r u w ≤ 2 * U₁ * cutoffEnergy r w + K * (1 + U₀) * (A ^ 2 + A ^ 6) / r :=
  differenceRHS_le_of_bounds cutoffSixthNorm_le sumSecondPartials_term_le transport_term_le
    stretching_term_le cubic_term_le mixed_stress_le self_stress_le

end Breakdown
