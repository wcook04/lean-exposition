module

public import QuarticQuery.Results.Conditional
public import QuarticQuery.ForrelationLower.Main

/-!
# Equation (2) for the specified circuit family

Compiled as part of the `QuarticQuery` library target.
No `Paper.Section2` or `ForrelationLower.Uniform` result
is used here.

Both complexities below refer to the same explicit `forrCircuit`. The
randomized estimate is written in the paper's real-power form. Its Forrelation
input is supplied by the existing alternative fixed-parameter proof.
-/

public section

namespace QuarticQuery.Paper

/-- Ledger: eq-2. Exact parameter identity used to translate the dyadic quantum
bound into the paper's square-root notation. -/
theorem construction_sqrt_mValue (t : ℕ) :
    Real.sqrt (mValue t : ℝ) = (2 : ℝ) ^ t := by
  rw [Forrelation.mValue_cast, ← pow_two, Real.sqrt_sq (by positivity)]

/-- Ledger: eq-2. Stronger explicit version: the same named circuit satisfies
both inequalities with `c = 1/400`, `b = 6` and the existing `budgetConst`. -/
theorem construction_family_named (l : ℕ) (hk : 2 ≤ l + 1) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      CircuitRealises (Forrelation.forrCircuit l t) (P (l + 1) t) ∧
      (Forrelation.forrCircuit l t).size ≤
        Forrelation.forrConstant (l + 1) * mValue t * (2 * t) ^ 2 ∧
      (Q (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) : ℝ) ≤
        (Upper.budgetConst (l + 1) : ℝ) * Real.sqrt (mValue t : ℝ) *
          (Real.logb 2 (mValue t : ℝ)) ^ 6 ∧
      (1 / 400 : ℝ) * Real.rpow (mValue t : ℝ) (2 - 1 / ((l + 1 : ℕ) : ℝ)) /
          (Real.logb 2 (mValue t : ℝ)) ^ 2 ≤
        (R (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) : ℝ) := by
  obtain ⟨t₀, ht₀⟩ := ForrelationLower.bansalSinhaLower (l + 1) hk
  refine ⟨max t₀ 8, fun t ht => ?_⟩
  have h8 : 8 ≤ t := le_trans (le_max_right _ _) ht
  have h1 : 1 ≤ t := by omega
  have hLR : Lvalue (l + 1) t < R (P (l + 1) t) :=
    ht₀ t (le_trans (le_max_left _ _) ht)
  have hG := Gvalue_lt_R_Fkm hk h8 (Forrelation.forrCircuit l t)
    (Forrelation.forrCircuit_realises l t) hLR
  refine ⟨Forrelation.forrCircuit_realises l t,
    Forrelation.forrCircuit_size_le l t h1, ?_, ?_⟩
  · rw [QuarticQuery.logb_mValue, construction_sqrt_mValue]
    exact Upper.Q_Fkm_le l t h1
  · rw [QuarticQuery.logb_mValue, QuarticQuery.mValue_cast]
    exact rpow_le_of_Gvalue_lt hk h8 hG

/-- Ledger: eq-2. Verbatim existential family bounds, with a positive natural
logarithmic exponent and a circuit-size witness retained in the same package. -/
theorem construction_equation_two (k : ℕ) (hk : 2 ≤ k) :
    ∃ (S : ℕ) (c C : ℝ), 0 < c ∧ 0 < C ∧
      ∃ (b : ℕ), 0 < b ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        ∃ Cir : Circuit (ForrelationCoord k t), CircuitRealises Cir (P k t) ∧
          Cir.size ≤ S * mValue t * (2 * t) ^ 2 ∧
          (Q (totalise (Fkm k t Cir)) : ℝ) ≤
            C * Real.sqrt (mValue t : ℝ) * (Real.logb 2 (mValue t : ℝ)) ^ b ∧
          c * Real.rpow (mValue t : ℝ) (2 - 1 / (k : ℝ)) /
              (Real.logb 2 (mValue t : ℝ)) ^ 2 ≤
            (R (totalise (Fkm k t Cir)) : ℝ) := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t₀, ht₀⟩ := construction_family_named l hk
  refine ⟨Forrelation.forrConstant (l + 1), 1 / 400,
    (Upper.budgetConst (l + 1) : ℝ), by norm_num,
    by exact_mod_cast Upper.budgetConst_pos (l + 1), 6, by norm_num,
    t₀, fun t ht => ?_⟩
  exact ⟨Forrelation.forrCircuit l t, ht₀ t ht⟩

end QuarticQuery.Paper
