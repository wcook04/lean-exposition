module

public import QuarticQuery.Paper.ClassicalPlanted

/-!
Direct agreement target for the actual-vocabulary wrapper itself. This challenge
shares the project's definitions; the separate Spec/Bridge/Challenge checks are
the independent mathematical expectation. Never call this agreement alone a
semantic review. `sorry` is an intentional challenge hole. Native validation: `research/adjudication/round3_formal.json`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace QuarticQuery.Paper

theorem eq19_whole {κ : Type} [Fintype κ] [DecidableEq κ]
    {ℓ r S : ℕ} {μ : BitInput κ → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) {G : ℕ}
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    (coupledAvg μ (fun A J I => foundZero T A J I) =
      expectedZeros μ T / ((2 ^ ℓ : ℕ) : ℝ)) ∧
    (coupledAvg μ (fun A J I => foundZero T A J I) ≤
      4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2) := by
  sorry

end QuarticQuery.Paper
