module

public import QuarticQuery.LowerBound.RealizedCaps

/-! Meaningful negative target: a valid theorem that adds the all-branch cap
premise `(T ω).capped` which the round-four endpoint removes. The duplicate
theorem name is deliberate; this module is compiled separately from the
positive solution. It must be rejected for target-type mismatch. -/

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
    (T : Ω → OutTree (Fin r × κ) (Fin r → Bool))
    (_hcap : ∀ ω, (T ω).capped fun _ => L) :
    ∑ ω, w ω * compliantSuccess f μ (T ω) (fun _ => L) ≤ β ^ r :=
  direct_product_realized_caps_average hμ hard hw hw1 T

end QuarticQuery
