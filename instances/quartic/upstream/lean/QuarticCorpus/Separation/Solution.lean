module

public import QuarticQuery.Statement
import QuarticQuery.Results.Conditional

/-!
# Separation bundle

The headline. `BansalSinhaLower` is the one mathematical hypothesis left: an
ordinary theorem binder, never an axiom, so the axiom report cannot show it. Read
each theorem's type for its hypotheses.
-/

public section

namespace QuarticQuery.Checked

-- CHALLENGE-BEGIN
theorem alphaTot_eq_four_of_bansalSinha (h : BansalSinhaLower) : alphaTot = 4 := by
  -- proof
  exact QuarticQuery.alphaTot_eq_four_of_bansalSinha h

theorem theorem_1_1 (h : BansalSinhaLower) :
    alphaTot = 4 ∧ UniversalPower 4 ∧
      ∀ k : ℕ, 2 ≤ k → ∃ (S A : ℕ) (b : ℕ), 0 < A ∧ ∀ t, 1 ≤ t →
        ∃ C : Circuit (ForrelationCoord k t), CircuitRealises C (P k t) ∧
          C.size ≤ S * mValue t * (2 * t) ^ 2 ∧
          (Q (totalise (Fkm k t C)) : ℝ) ≤ (A : ℝ) * 2 ^ t * (2 * (t : ℝ)) ^ b ∧
          (8 ≤ t → Lvalue k t < R (P k t) →
            Gvalue (mValue t) (Lvalue k t) < R (totalise (Fkm k t C))) := by
  -- proof
  exact QuarticQuery.theorem_1_1 h

theorem universal_quartic_bound : UniversalPower 4 := by
  -- proof
  exact QuarticQuery.universalPower_four

theorem cubic_bound_fails_of_bansalSinha (h : BansalSinhaLower) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
      (R (totalise f) : ℝ) ≤ C * (Q (totalise f) : ℝ) ^ 3 := by
  -- proof
  exact QuarticQuery.cubic_bound_fails_of_bansalSinha h

theorem family_bounds (k : ℕ) (hk : 2 ≤ k) :
    ∃ (S A : ℕ) (b : ℕ), 0 < A ∧ ∀ t, 1 ≤ t →
      ∃ C : Circuit (ForrelationCoord k t), CircuitRealises C (P k t) ∧
        C.size ≤ S * mValue t * (2 * t) ^ 2 ∧
        (Q (totalise (Fkm k t C)) : ℝ) ≤ (A : ℝ) * 2 ^ t * (2 * (t : ℝ)) ^ b ∧
        (8 ≤ t → Lvalue k t < R (P k t) →
          Gvalue (mValue t) (Lvalue k t) < R (totalise (Fkm k t C))) := by
  -- proof
  exact QuarticQuery.family_bounds k hk

theorem addressed_lower_bound {κ : Type} [Fintype κ] [DecidableEq κ] (f : PartialBool κ)
    (C : Circuit κ) (hC : CircuitRealises C f) {t L : ℕ} (hL1 : 1 ≤ L) (hLm : L ≤ mValue t)
    (hLR : L < R f) :
    Gvalue (mValue t) L < R (totalise (addressedF f C (2 * t) (40 * t))) := by
  -- proof
  exact QuarticQuery.Gvalue_lt_R_addressedF f C hC hL1 hLm hLR
-- CHALLENGE-END

end QuarticQuery.Checked
