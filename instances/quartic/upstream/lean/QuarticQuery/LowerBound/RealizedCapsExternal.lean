module

public import QuarticQuery.ExternalRandomness
public import QuarticQuery.LowerBound.RealizedCaps

/-!
# Finite-seed bridge to initially uncapped adaptive trees

Compiled as part of the `QuarticQuery` library target.
Every ω selects an *initially uncapped* finite tree. This theorem pushes its
weights exactly to a finite set of behaviors and uses the joint-event result.
The measurable Ω extension is a further formalization obligation, not hidden
in the statement of this finite theorem.
-/

@[expose] public section

open Finset

namespace QuarticQuery

variable {κ : Type} [Fintype κ] [DecidableEq κ] {r : ℕ}

/-- External side information and coins may be correlated with each other;
only the entire seed is required to be independent of the tuple under the
original product experiment. This is the finite-seed algebraic endpoint. -/
theorem direct_product_external_finite_realized_caps
    {Ω : Type} [Fintype Ω]
    {f : PartialBool κ} {μ : BitInput κ → ℝ} {L : ℕ} {β : ℝ}
    (hμ : ∀ x, 0 ≤ μ x)
    (hard : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (T : Ω → OutTree (Fin r × κ) (Fin r → Bool)) :
    ∑ ω, w ω * compliantSuccess f μ (T ω) (fun _ => L) ≤ β ^ r :=
  direct_product_realized_caps_average hμ hard hw hw1 T

end QuarticQuery
