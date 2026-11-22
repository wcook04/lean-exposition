module

public import QuarticQuery.Paper.ClassicalPlanted

/-!
# Proposed whole-display wrapper for equation (19)

This assembles the maintained equality and expected-count bound. Native
validation belongs to `research/adjudication/round3_formal.json`; the unchanged
original proposal is preserved with return 07.

This wrapper preserves both clauses of the display. Its inequality is proved
by the alternative finite-world zero-search route; it does not formalize the
paper's early/late decomposition and makes no optimality assertion.
-/

@[expose] public section

namespace QuarticQuery.Paper

open Finset

theorem eq_19_complete
    {κ : Type} [Fintype κ] [DecidableEq κ] {ℓ r S : ℕ}
    {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) {G : ℕ}
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    (coupledAvg μ (fun A J I => foundZero T A J I) =
      expectedZeros μ T / ((2 ^ ℓ : ℕ) : ℝ)) ∧
    expectedZeros μ T / ((2 ^ ℓ : ℕ) : ℝ) ≤
      4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 := by
  refine ⟨erasedZero_eq_expectedZeros_div μ T, ?_⟩
  calc
    expectedZeros μ T / ((2 ^ ℓ : ℕ) : ℝ) ≤
        (4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ)) / ((2 ^ ℓ : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (expectedZeros_le_four hμ hμ1 T hT)
        (colCard_pos ℓ).le
    _ = 4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 := by
      rw [div_div, pow_two]

end QuarticQuery.Paper
