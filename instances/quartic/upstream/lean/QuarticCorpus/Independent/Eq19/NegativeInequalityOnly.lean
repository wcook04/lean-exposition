module

public import QuarticCorpus.Independent.Eq19.Spec
import QuarticCorpus.Independent.Eq19.Bridge

/-!
Deliberately wrong comparison target: the proof is valid but the equality clause
was omitted. Expected Comparator stage: theorem statement mismatch. Native outcomes belong to
`research/adjudication/round3_formal.json`.
-/

@[expose] public section

open scoped BigOperators

open Finset

namespace QuarticQuery.Independent.Eq19

theorem checked_eq19 {κ : Type} [Fintype κ] [DecidableEq κ]
    {ℓ r S : ℕ} {μ : BitInput κ → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) {G : ℕ}
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    hitProbability μ T ≤ 4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 := by
  exact (specification_eq19 hμ hμ1 T hT).2

end QuarticQuery.Independent.Eq19
