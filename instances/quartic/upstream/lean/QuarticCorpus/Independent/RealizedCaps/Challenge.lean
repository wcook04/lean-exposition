module

public import QuarticQuery.LowerBound.RealizedCaps

/-! Authored direct agreement target for the finite external-seed endpoint of
round-four return 05. It imports the maintained cap, tree and success
definitions but not the proof module. The intentional `sorry` is not a proof.
This shares the maintained vocabulary and is not an independent semantic review. -/

@[expose] public section

open Finset

namespace QuarticQuery

variable {κ : Type} [Fintype κ] [DecidableEq κ] {r : ℕ}

theorem direct_product_external_finite_realized_caps
    {Ω : Type} [Fintype Ω]
    {f : PartialBool κ} {μ : BitInput κ → ℝ} {L : ℕ} {β : ℝ}
    (hμ : ∀ x, 0 ≤ μ x)
    (hard : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (T : Ω → OutTree (Fin r × κ) (Fin r → Bool)) :
    ∑ ω, w ω * compliantSuccess f μ (T ω) (fun _ => L) ≤ β ^ r := by
  sorry

end QuarticQuery
