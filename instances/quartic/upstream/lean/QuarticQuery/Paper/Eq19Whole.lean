module

public import QuarticQuery.Paper.ClassicalPlanted

/-!
# The complete equation (19), with both clauses in one theorem

This wrapper assembles the maintained equality and hit-probability bound.
Native validation belongs to `research/adjudication/round3_formal.json`; the
unchanged original proposal is preserved with return 09.

The law draws every address string independently with mass `μ`, all zero
positions independently uniformly, and a further uniform column independently.
The depth cap counts every bit query, including repetitions. `ℓ = 2*t` gives
the preprint's `m = 4^t`; no promise-support or hardness premise is needed here.
-/

@[expose] public section

open scoped BigOperators

open Finset

namespace QuarticQuery.Paper

theorem eq19_whole {κ : Type} [Fintype κ] [DecidableEq κ]
    {ℓ r S : ℕ} {μ : BitInput κ → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) {G : ℕ}
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    (coupledAvg μ (fun A J I => foundZero T A J I) =
      expectedZeros μ T / ((2 ^ ℓ : ℕ) : ℝ)) ∧
    (coupledAvg μ (fun A J I => foundZero T A J I) ≤
      4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2) := by
  exact ⟨erasedZero_eq_expectedZeros_div μ T, eq_19 hμ hμ1 T hT⟩

end QuarticQuery.Paper
