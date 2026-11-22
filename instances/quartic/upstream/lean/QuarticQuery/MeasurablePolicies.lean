module

public import QuarticQuery.LowerBound.RealizedCaps

/-!
# Explicit action-table compilation with finite query allowances

Compiled as part of the `QuarticQuery` library target.
Measurability of every action coordinate and its exact pushforward mass is
proved in ordinary mathematics in `classical_completion.md`. This finite
compiler is a separate syntactic component, not a claim that Lean has already
verified an arbitrary-measure policy transfer.
-/

@[expose] public section

namespace QuarticQuery

variable {κ : Type} [Fintype κ] [DecidableEq κ] {r : ℕ}

/-- What an action-at-history policy can return. -/
inductive PolicyAction (ι β : Type) where
  | stop : β → PolicyAction ι β
  | ask : ι → PolicyAction ι β

/-- A query/answer history keeps repeated queries; it is not an information
set of distinct coordinates. -/
abbrev PolicyHistory (ι : Type) := List (ι × Bool)

/-- A finite table may be viewed as a function from histories to actions.
Only finitely many histories of length at most `fuel` are ever evaluated. -/
def compilePolicy {β : Type}
    (a : PolicyHistory (Fin r × κ) → PolicyAction (Fin r × κ) β)
    (fallback : β) :
    ℕ → (Fin r → ℕ) → PolicyHistory (Fin r × κ) →
      OutTree (Fin r × κ) β
  | 0, _, hist =>
      match a hist with
      | .stop out => .leaf out
      | .ask _ => .leaf fallback
  | fuel + 1, c, hist =>
      match a hist with
      | .stop out => .leaf out
      | .ask p =>
          if 0 < c p.1 then
            .query p
              (compilePolicy a fallback fuel
                (Function.update c p.1 (c p.1 - 1)) (hist ++ [(p, false)]))
              (compilePolicy a fallback fuel
                (Function.update c p.1 (c p.1 - 1)) (hist ++ [(p, true)]))
          else .leaf fallback

/-- The compiler enforces individual caps on every syntactic branch.
The zero-fuel case still preserves a terminal response. -/
theorem compilePolicy_capped {β : Type}
    (a : PolicyHistory (Fin r × κ) → PolicyAction (Fin r × κ) β)
    (fallback : β) (fuel : ℕ) (c : Fin r → ℕ)
    (hist : PolicyHistory (Fin r × κ)) :
    (compilePolicy a fallback fuel c hist).capped c := by
  induction fuel generalizing c hist with
  | zero =>
    cases ha : a hist <;> simp [compilePolicy, ha, OutTree.capped]
  | succ n ih =>
    cases ha : a hist with
    | stop out => simp [compilePolicy, ha, OutTree.capped]
    | ask p =>
      by_cases hp : 0 < c p.1
      · simp only [compilePolicy, ha, if_pos hp, OutTree.capped]
        exact ⟨hp, ih _ _, ih _ _⟩
      · simp [compilePolicy, ha, hp, OutTree.capped]

/-- The fuel is an additional upper bound on the depth of any compiled tree. -/
theorem compilePolicy_depth_le {β : Type}
    (a : PolicyHistory (Fin r × κ) → PolicyAction (Fin r × κ) β)
    (fallback : β) (fuel : ℕ) (c : Fin r → ℕ)
    (hist : PolicyHistory (Fin r × κ)) :
    (compilePolicy a fallback fuel c hist).depth ≤ fuel := by
  induction fuel generalizing c hist with
  | zero => cases ha : a hist <;> simp [compilePolicy, ha, OutTree.depth]
  | succ n ih =>
    cases ha : a hist with
    | stop out => simp [compilePolicy, ha, OutTree.depth]
    | ask p =>
      by_cases hp : 0 < c p.1
      · simp only [compilePolicy, ha, if_pos hp, OutTree.depth]
        have hl := ih (Function.update c p.1 (c p.1 - 1)) (hist ++ [(p, false)])
        have hu := ih (Function.update c p.1 (c p.1 - 1)) (hist ++ [(p, true)])
        omega
      · simp [compilePolicy, ha, hp, OutTree.depth]

end QuarticQuery
