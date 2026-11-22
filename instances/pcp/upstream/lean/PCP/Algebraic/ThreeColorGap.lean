/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorBinaryVerifier

/-!
# The fixed three-color gap lies strictly between zero and one

These elementary bounds put the actual verifier's soundness base in `[0,1)`
for independent repetition. They use the declared gap, not a replacement
constant or an assumed acceptance estimate.
-/

namespace PCP.Algebraic.ThreeColorGap

/-- The difference-consistency term alone bounds every degree's rejection budget. -/
theorem budget_gap_le_sixteenth (c : ℕ) :
    ThreeColorSoundnessBudget.gap c ≤ (1 : ℚ) / 16 := by
  have hS := EncodedLineLowDegreeTest.soundnessConstant_nonneg c
  have hD : 1 ≤ ThreeColorSoundnessBudget.differenceCoefficient c := by
    unfold ThreeColorSoundnessBudget.differenceCoefficient
    linarith
  have hgap : ThreeColorSoundnessBudget.gap c ≤
      1 / (16 * ThreeColorSoundnessBudget.differenceCoefficient c) :=
    (min_le_right _ _).trans (min_le_left _ _)
  exact hgap.trans (one_div_le_one_div_of_le (by norm_num) (by linarith))

/-- Whole-field sampling has already divided the base rejection gap by sixteen. -/
theorem gap_le_one_over_256 : ThreeColorBinaryVerifier.gap ≤ (1 : ℚ) / 256 := by
  have h := div_le_div_of_nonneg_right (budget_gap_le_sixteenth 4)
    (by norm_num : (0 : ℚ) ≤ 16)
  norm_num [ThreeColorBinaryVerifier.gap] at h ⊢
  exact h

theorem gap_lt_one : ThreeColorBinaryVerifier.gap < 1 :=
  gap_le_one_over_256.trans_lt (by norm_num)

theorem gap_le_one : ThreeColorBinaryVerifier.gap ≤ 1 := gap_lt_one.le

/-- The actual acceptance upper bound is a legitimate nonnegative probability base. -/
theorem acceptance_nonneg : 0 ≤ 1 - ThreeColorBinaryVerifier.gap := by
  have h := gap_le_one
  linarith

/-- Strictly positive rejection makes the acceptance base strictly below one. -/
theorem acceptance_lt_one : 1 - ThreeColorBinaryVerifier.gap < 1 := by
  have h := ThreeColorBinaryVerifier.gap_pos
  linarith

theorem acceptance_mem_unitInterval :
    0 ≤ 1 - ThreeColorBinaryVerifier.gap ∧ 1 - ThreeColorBinaryVerifier.gap < 1 :=
  ⟨acceptance_nonneg, acceptance_lt_one⟩

end PCP.Algebraic.ThreeColorGap
