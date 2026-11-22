module

public import QuarticCorpus.Independent.Eq19.Spec

/-!
Authored target, not output of tools/build_challenges.py.
`sorry` is intentional in this specification-only challenge. The solution must
prove the same complete conjunction without sorryAx. Native validation: `research/adjudication/round3_formal.json`.
-/

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
  sorry

end QuarticQuery.Independent.Eq19
