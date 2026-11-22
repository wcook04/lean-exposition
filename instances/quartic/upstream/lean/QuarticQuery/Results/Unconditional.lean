module

public import QuarticQuery.Results.Conditional
public import QuarticQuery.ForrelationLower.Main

/-!
# The separation, unconditionally

`bansalSinhaLower` discharges the one hypothesis of `Results.Conditional`, so
Theorem 1.1 holds with no mathematical hypothesis.
-/

public section

namespace QuarticQuery

/-- Ledger: thm-1.1. The optimal power is four. -/
theorem alphaTot_eq_four_unconditional : alphaTot = 4 :=
  alphaTot_eq_four_of_bansalSinha ForrelationLower.bansalSinhaLower

/-- Ledger: thm-1.1. The whole of Theorem 1.1: the optimal power, the universal
quartic bound, and for each fixed `k ≥ 2` a family with equation (2). -/
theorem theorem_1_1_unconditional :
    alphaTot = 4 ∧ UniversalPower 4 ∧
      ∀ k : ℕ, 2 ≤ k → ∃ (S A : ℕ) (b : ℕ) (t₀ : ℕ), 0 < A ∧ ∀ t, max 1 t₀ ≤ t →
        ∃ C : Circuit (ForrelationCoord k t), CircuitRealises C (P k t) ∧
          C.size ≤ S * mValue t * (2 * t) ^ 2 ∧
          (Q (totalise (Fkm k t C)) : ℝ) ≤ (A : ℝ) * 2 ^ t * (2 * (t : ℝ)) ^ b ∧
          Gvalue (mValue t) (Lvalue k t) < R (totalise (Fkm k t C)) := by
  refine ⟨alphaTot_eq_four_unconditional, universalPower_four, fun k hk => ?_⟩
  obtain ⟨S, A, b, hA, hfam⟩ := family_bounds k hk
  obtain ⟨t₀, ht₀⟩ := ForrelationLower.bansalSinhaLower k hk
  refine ⟨S, A, b, max t₀ 8, hA, fun t ht => ?_⟩
  have h1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have h2 : max t₀ 8 ≤ t := le_trans (le_max_right _ _) ht
  obtain ⟨C, hC, hS, hQ, hR⟩ := hfam t h1
  exact ⟨C, hC, hS, hQ, hR (le_trans (le_max_right _ _) h2)
    (ht₀ t (le_trans (le_max_left _ _) h2))⟩

/-- Ledger: cor-cubic-refuted. No constant makes `R ≤ C Q³` hold for all total
functions. -/
theorem cubic_bound_fails_unconditional :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
      (R (totalise f) : ℝ) ≤ C * (Q (totalise f) : ℝ) ^ 3 :=
  cubic_bound_fails_of_bansalSinha ForrelationLower.bansalSinhaLower

end QuarticQuery
