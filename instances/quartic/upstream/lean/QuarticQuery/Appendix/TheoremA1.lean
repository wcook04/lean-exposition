module

public import QuarticQuery.Model.Quantum
import QuarticQuery.Bridge.DecisionTree
import QuarticQuery.Bridge.Deferred
import Complexity.Computability.QueryComplexity.Quantum.Adversary

/-!
# Theorem A.1: `D(f) = O((1 + Q(f))^4)` for total `f`

This proves Theorem A.1 by the imported route: complexitylib's
`Cslib.Quantum.complexity_le_mul_pow_four`, reached through the bridges in
`QuarticQuery/Bridge/`. It is not a line-by-line check of Appendix A; Lemmas A.2 to
A.5 are not formalised here in the paper's form.
-/

public section

namespace QuarticQuery

variable {n : ℕ}

/-- Ledger: thm-A.1. A `t`-query adaptive program for a total function gives a decision
tree of depth `20736 t⁴`. Constant functions need no program. -/
theorem D_le_of_QLe {f : TotalBool (Fin n)} {t : ℕ} (h : QLe (totalise f) t) :
    D (totalise f) ≤ 20736 * t ^ 4 := by
  rcases h with ⟨b, hb⟩ | ⟨w, ψ, A, hψ, hA, hc⟩
  · have : DLe (totalise f) 0 :=
      ⟨.leaf b, le_rfl, fun x c hx => (hb x c hx).symm⟩
    exact (D_le_of_DLe this).trans (Nat.zero_le _)
  · obtain ⟨W', _, entry, U, S, hspec⟩ := exists_fixedSequence A hA
    rw [D_totalise_eq_complexity]
    refine Cslib.Quantum.complexity_le_mul_pow_four U (ψ₀ := entry ψ)
      (by rw [entry.norm_map, hψ]) t S fun x => ?_
    rw [hspec]
    have hsum := A.outputMass_true_add_false x ψ
    have hx := hc x (f x) rfl
    rw [hψ] at hsum
    have ht := A.outputMass_nonneg x ψ true
    have hf := A.outputMass_nonneg x ψ false
    cases hfx : f x
    · rw [hfx] at hx
      simp only [Cslib.BitString.bitVal_false, sub_zero]
      rw [abs_of_nonneg ht]
      linarith
    · rw [hfx] at hx
      simp only [Cslib.BitString.bitVal_true]
      rw [abs_le]
      constructor <;> linarith

/-- Ledger: thm-A.1. `D(f) ≤ 20736 Q(f)⁴` for every total `f`. -/
theorem D_le_Q_pow_four (f : TotalBool (Fin n)) :
    D (totalise f) ≤ 20736 * Q (totalise f) ^ 4 :=
  D_le_of_QLe (QLe_Q _)

/-- Ledger: thm-A.1. `R(f) ≤ D(f) ≤ 20736 (1 + Q(f))⁴`. -/
theorem R_le_D_le_one_add_Q_pow_four (f : TotalBool (Fin n)) :
    (R (totalise f) : ℝ) ≤ D (totalise f) ∧
      (D (totalise f) : ℝ) ≤ 20736 * (1 + (Q (totalise f) : ℝ)) ^ 4 := by
  refine ⟨by exact_mod_cast R_le_D _, ?_⟩
  have h : (D (totalise f) : ℝ) ≤ 20736 * (Q (totalise f) : ℝ) ^ 4 := by
    exact_mod_cast D_le_Q_pow_four f
  have hq : (0 : ℝ) ≤ Q (totalise f) := Nat.cast_nonneg _
  refine h.trans ?_
  gcongr
  linarith

/-- Ledger: thm-A.1. The exponent `4` is admissible in equation (1), with constant
`20736 = 12⁴`. -/
theorem universalPower_four : UniversalPower 4 := by
  refine ⟨by norm_num, 20736, by norm_num, fun n _ f => ?_⟩
  obtain ⟨h₁, h₂⟩ := R_le_D_le_one_add_Q_pow_four f
  have h : Real.rpow (1 + (Q (totalise f) : ℝ)) 4 = (1 + (Q (totalise f) : ℝ)) ^ 4 := by
    rw [Real.rpow_eq_pow]
    exact_mod_cast Real.rpow_natCast (1 + (Q (totalise f) : ℝ)) 4
  rw [h]
  exact h₁.trans h₂

end QuarticQuery
