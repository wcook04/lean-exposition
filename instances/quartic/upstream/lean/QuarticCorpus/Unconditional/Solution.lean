module

public import QuarticQuery.Statement
import QuarticQuery.Results.Unconditional

/-!
# Unconditional bundle

Theorem 1.1 of the preprint with no hypothesis, and the Forrelation lower bound in
the form it uses. The statements use only the public vocabulary.
-/

public section

namespace QuarticQuery.Checked

-- CHALLENGE-BEGIN
theorem alpha_tot_eq_four : alphaTot = 4 := by
  -- proof
  exact QuarticQuery.alphaTot_eq_four_unconditional

theorem theorem_one_one :
    alphaTot = 4 ∧ UniversalPower 4 ∧
      ∀ k : ℕ, 2 ≤ k → ∃ (S A : ℕ) (b : ℕ) (t₀ : ℕ), 0 < A ∧ ∀ t, max 1 t₀ ≤ t →
        ∃ C : Circuit (ForrelationCoord k t), CircuitRealises C (P k t) ∧
          C.size ≤ S * mValue t * (2 * t) ^ 2 ∧
          (Q (totalise (Fkm k t C)) : ℝ) ≤ (A : ℝ) * 2 ^ t * (2 * (t : ℝ)) ^ b ∧
          Gvalue (mValue t) (Lvalue k t) < R (totalise (Fkm k t C)) := by
  -- proof
  exact QuarticQuery.theorem_1_1_unconditional

theorem cubic_bound_fails :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
      (R (totalise f) : ℝ) ≤ C * (Q (totalise f) : ℝ) ^ 3 := by
  -- proof
  exact QuarticQuery.cubic_bound_fails_unconditional

theorem forrelation_lower_bound : BansalSinhaLower := by
  -- proof
  exact QuarticQuery.ForrelationLower.bansalSinhaLower
-- CHALLENGE-END

end QuarticQuery.Checked
