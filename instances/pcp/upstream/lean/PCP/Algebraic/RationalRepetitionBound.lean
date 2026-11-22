/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# An explicit repetition count for a rational rejection gap

For a gap `δ` in `(0, 1]`, `ceil (1 / δ)` repetitions reduce acceptance to at
most one half. The count is computed directly by rational arithmetic and natural
ceiling; it uses no search or chosen witness. This supplies a fixed numerical
constant, not a running-time certificate for a verifier.
-/

namespace PCP.Algebraic.RationalRepetitionBound

/-- A directly computable repetition count. Its positivity requires a positive gap. -/
def repetitions (δ : ℚ) : ℕ := ⌈δ⁻¹⌉₊

theorem repetitions_pos {δ : ℚ} (hδ : 0 < δ) : 0 < repetitions δ :=
  Nat.ceil_pos.mpr (inv_pos.mpr hδ)

/-- An elementary form of the geometric-decay estimate, without division. -/
theorem linear_mul_pow_le_one {δ : ℚ} (hδ1 : δ ≤ 1) (k : ℕ) :
    (1 + (k : ℚ) * δ) * (1 - δ) ^ k ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    have hstep : (1 + ((k : ℚ) + 1) * δ) * (1 - δ) ≤ 1 + (k : ℚ) * δ := by
      nlinarith [mul_nonneg hk (sq_nonneg δ)]
    calc
      (1 + ((k + 1 : ℕ) : ℚ) * δ) * (1 - δ) ^ (k + 1) =
          ((1 + ((k : ℚ) + 1) * δ) * (1 - δ)) * (1 - δ) ^ k := by
            rw [Nat.cast_add, Nat.cast_one, pow_succ]
            ring
      _ ≤ (1 + (k : ℚ) * δ) * (1 - δ) ^ k :=
        mul_le_mul_of_nonneg_right hstep (pow_nonneg (sub_nonneg.mpr hδ1) k)
      _ ≤ 1 := ih

/-- A rational decay bound valid for every repetition count, including zero. -/
theorem acceptance_pow_le_reciprocal {δ : ℚ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (k : ℕ) : (1 - δ) ^ k ≤ 1 / (1 + (k : ℚ) * δ) := by
  have hden : 0 < 1 + (k : ℚ) * δ := by positivity
  apply (le_div_iff₀ hden).mpr
  simpa only [mul_comm] using linear_mul_pow_le_one hδ1 k

/-- The chosen count accumulates at least one unit of rejection gap. -/
theorem one_le_repetitions_mul {δ : ℚ} (hδ : 0 < δ) :
    1 ≤ (repetitions δ : ℚ) * δ := by
  have h := mul_le_mul_of_nonneg_right (Nat.le_ceil δ⁻¹) hδ.le
  simpa only [inv_mul_cancel₀ hδ.ne', repetitions] using h

/-- The explicit positive count attains the standard soundness target. -/
theorem acceptance_pow_le_half {δ : ℚ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) ^ repetitions δ ≤ 1 / 2 := by
  apply (acceptance_pow_le_reciprocal hδ.le hδ1 (repetitions δ)).trans
  have hden : 0 < 1 + (repetitions δ : ℚ) * δ := by positivity
  apply (div_le_iff₀ hden).mpr
  have h := one_le_repetitions_mul hδ
  linarith

end PCP.Algebraic.RationalRepetitionBound
