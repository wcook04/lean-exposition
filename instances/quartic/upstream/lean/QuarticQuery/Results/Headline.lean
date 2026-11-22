module

public import QuarticQuery.Appendix.TheoremA1
public import QuarticQuery.Model.Quantum
public import QuarticQuery.Results.Exponent

/-!
# Headline theorems, with cost transport discharged

The theorems of `Results.Exponent` take reindex invariance of `R` and `Q` as
binders. Those are proved in `Model`, so the only remaining hypotheses here are
the family bounds of equation (2). The universal quartic bound is discharged by
`universalPower_four`.
-/

public section

namespace QuarticQuery

/-- Ledger: thm-1.1. The optimal power is four, given the family bounds. -/
theorem alphaTot_eq_four (hfam : FamilyBounds) : alphaTot = 4 :=
  alphaTot_eq_four_of (fun _ _ _ _ e f => R_reindex e f) (fun _ _ _ _ e f => Q_reindex e f)
    hfam universalPower_four

/-- Ledger: claim-no-smaller-exponent. A family at one fixed `k` rules out every
power below `4 - 2/k`. -/
theorem no_universal_power {k : ℕ} {α : ℝ} (hfam : FamilyBoundsAt k)
    (hs : α / 2 < 2 - 1 / (k : ℝ)) : ¬ UniversalPower α :=
  not_universalPower_of_familyBoundsAt (fun _ _ _ _ e f => R_reindex e f)
    (fun _ _ _ _ e f => Q_reindex e f) hfam hs

/-- Ledger: cor-cubic-refuted. The family at `k = 3` alone refutes the cubic bound. -/
theorem cubic_bound_fails (hfam : FamilyBoundsAt 3) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
      (R (totalise f) : ℝ) ≤ C * (Q (totalise f) : ℝ) ^ 3 :=
  cubic_refuted_bare (fun _ _ _ _ e f => R_reindex e f) (fun _ _ _ _ e f => Q_reindex e f) hfam

end QuarticQuery
