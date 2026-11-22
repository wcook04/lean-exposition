module

public import QuarticQuery.Results.Headline
public import QuarticQuery.LowerBound.Planted.Main
public import QuarticQuery.Upper.Bound

/-!
# The separation, conditional on the Forrelation lower bound

Everything in the preprint's argument is proved here except one input, the
Bansal–Sinha randomized lower bound, which appears as the named hypothesis
`BansalSinhaLower`. The universal quartic bound is proved through complexitylib's
route, not along Appendix A.
-/

public section

namespace QuarticQuery

open Forrelation Upper

/-- Ledger: eq-2. For each fixed `k ≥ 2`, one circuit family of size
`O_k(m log² m)` gives both bounds of equation (2). The lower bound holds wherever
`L < R(P)` does. -/
theorem family_bounds (k : ℕ) (hk : 2 ≤ k) :
    ∃ (S A : ℕ) (b : ℕ), 0 < A ∧ ∀ t, 1 ≤ t →
      ∃ C : Circuit (ForrelationCoord k t), CircuitRealises C (P k t) ∧
        C.size ≤ S * mValue t * (2 * t) ^ 2 ∧
        (Q (totalise (Fkm k t C)) : ℝ) ≤ (A : ℝ) * 2 ^ t * (2 * (t : ℝ)) ^ b ∧
        (8 ≤ t → Lvalue k t < R (P k t) →
          Gvalue (mValue t) (Lvalue k t) < R (totalise (Fkm k t C))) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  refine ⟨forrConstant (l + 1), budgetConst (l + 1), 6, budgetConst_pos _, fun t ht => ?_⟩
  exact ⟨forrCircuit l t, forrCircuit_realises l t, forrCircuit_size_le l t ht, Q_Fkm_le l t ht,
    fun h8 hLR => Gvalue_lt_R_Fkm hk h8 _ (forrCircuit_realises l t) hLR⟩

/-- Ledger: eq-2. The family bounds follow from the Forrelation lower bound. -/
theorem familyBounds_of_bansalSinha (h : BansalSinhaLower) : FamilyBounds := by
  intro k hk
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t₀, ht₀⟩ := h (l + 1) hk
  refine familyBoundsAt_of_lower l hk (t₀ := max t₀ 8) fun t ht => ?_
  exact Gvalue_lt_R_Fkm hk (le_trans (le_max_right _ _) ht) _ (forrCircuit_realises l t)
    (ht₀ t (le_trans (le_max_left _ _) ht))

/-- Ledger: thm-1.1. The optimal power is four, given the Forrelation lower bound. -/
theorem alphaTot_eq_four_of_bansalSinha (h : BansalSinhaLower) : alphaTot = 4 :=
  alphaTot_eq_four (familyBounds_of_bansalSinha h)

/-- Ledger: thm-1.1. The whole of Theorem 1.1, given the Forrelation lower bound: the
optimal power, the universal quartic bound, and for each fixed `k ≥ 2` the family of
equation (2). -/
theorem theorem_1_1 (h : BansalSinhaLower) :
    alphaTot = 4 ∧ UniversalPower 4 ∧
      ∀ k : ℕ, 2 ≤ k → ∃ (S A : ℕ) (b : ℕ), 0 < A ∧ ∀ t, 1 ≤ t →
        ∃ C : Circuit (ForrelationCoord k t), CircuitRealises C (P k t) ∧
          C.size ≤ S * mValue t * (2 * t) ^ 2 ∧
          (Q (totalise (Fkm k t C)) : ℝ) ≤ (A : ℝ) * 2 ^ t * (2 * (t : ℝ)) ^ b ∧
          (8 ≤ t → Lvalue k t < R (P k t) →
            Gvalue (mValue t) (Lvalue k t) < R (totalise (Fkm k t C))) :=
  ⟨alphaTot_eq_four_of_bansalSinha h, universalPower_four, family_bounds⟩

/-- Ledger: cor-cubic-refuted. No constant makes `R ≤ C Q³` hold for all total
functions, given the Forrelation lower bound. -/
theorem cubic_bound_fails_of_bansalSinha (h : BansalSinhaLower) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
      (R (totalise f) : ℝ) ≤ C * (Q (totalise f) : ℝ) ^ 3 :=
  cubic_bound_fails (familyBounds_of_bansalSinha h 3 (by norm_num))

end QuarticQuery
