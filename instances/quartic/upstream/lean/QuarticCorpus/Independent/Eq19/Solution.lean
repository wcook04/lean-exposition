module

public import QuarticCorpus.Independent.Eq19.Spec
import QuarticCorpus.Independent.Eq19.Bridge

/-! Proof-bearing independent target wrapper; see `research/adjudication/round3_formal.json` for native validation. -/

@[expose] public section

open scoped BigOperators

open Finset

namespace QuarticQuery.Independent.Eq19

theorem checked_eq19 {κ : Type} [Fintype κ] [DecidableEq κ]
    {ℓ r S : ℕ} {μ : BitInput κ → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) {G : ℕ}
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    (hitProbability μ T = expectedCount μ T / ((2 ^ ℓ : ℕ) : ℝ)) ∧
    (hitProbability μ T ≤ 4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2) := by
  exact specification_eq19 hμ hμ1 T hT

end QuarticQuery.Independent.Eq19
