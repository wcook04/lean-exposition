module

public import QuarticQuery.Paper.ClassicalDirectProduct
public import QuarticQuery.LowerBound.RealizedCaps

/-!
# Paper-route consumer of realized-cap truncation

Compiled as part of the `QuarticQuery` library target.
This states the joint event with a mass-one hard input distribution, and routes
the clipped tree into the separately maintained paper-style proof.
-/

@[expose] public section

namespace QuarticQuery.Paper

variable {κ : Type} [Fintype κ] [DecidableEq κ] {r : ℕ}

/-- Same conclusion as the weighted route, now using the paper's normalized
conditional-value proof at the clipped-tree stage. -/
theorem classical_realized_caps
    {f : PartialBool κ} {μ : BitInput κ → ℝ} {L : ℕ} {β : ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : classicalMass μ = 1)
    (hard : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    (T : OutTree (Fin r × κ) (Fin r → Bool)) :
    compliantSuccess f μ T (fun _ => L) ≤ β ^ r := by
  let fallback : Fin r → Bool := fun _ => false
  calc
    _ ≤ guessSuccess f (fun _ => μ) (T.clip fallback (fun _ => L)) :=
      compliantSuccess_le_clipped f μ hμ T _ fallback
    _ ≤ β ^ r :=
      classical_direct_product hμ hμ1 hard _ (OutTree.clip_capped fallback T _)

end QuarticQuery.Paper
