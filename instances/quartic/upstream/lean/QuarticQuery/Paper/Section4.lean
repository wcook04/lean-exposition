module

public import QuarticQuery.Results.Unconditional

/-!
# Section 4 of the preprint, statement by statement

Proposition 4.2 and its Omega corollary with the paper's quantifiers, derived from
`Gvalue_lt_R_Fkm` and the unconditional Forrelation lower bound `bansalSinhaLower`.
-/

public section

namespace QuarticQuery.Paper

/-- Ledger: prop-4.2. The paper's statement: for each fixed integer `k ≥ 2` and every
sufficiently large power of four `m = 4 ^ t`, `R(F_{k,m}) > G = ⌊m L / 100⌋` with
`L = ⌊m^(1-1/k) / (log₂ m)²⌋`. It is stated for every circuit realising `P_{k,m}`, which
includes the paper's `C_{k,m}`; the threshold `t₀` does not depend on the circuit. -/
theorem prop_4_2 (k : ℕ) (hk : 2 ≤ k) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ C : Circuit (ForrelationCoord k t),
      CircuitRealises C (P k t) → Gvalue (mValue t) (Lvalue k t) < R (totalise (Fkm k t C)) := by
  obtain ⟨t₀, ht₀⟩ := ForrelationLower.bansalSinhaLower k hk
  exact ⟨max t₀ 8, fun t ht C hC => Gvalue_lt_R_Fkm hk (le_trans (le_max_right _ _) ht) C hC
    (ht₀ t (le_trans (le_max_left _ _) ht))⟩

/-- Ledger: prop-4.2. Proposition 4.2 for the paper's own circuit scheme `forrCircuit`,
with `k = l + 1`. -/
theorem prop_4_2_forrCircuit (l : ℕ) (hk : 2 ≤ l + 1) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      Gvalue (mValue t) (Lvalue (l + 1) t) <
        R (totalise (Fkm (l + 1) t (Forrelation.forrCircuit l t))) := by
  obtain ⟨t₀, ht₀⟩ := prop_4_2 (l + 1) hk
  exact ⟨t₀, fun t ht => ht₀ t ht _ (Forrelation.forrCircuit_realises l t)⟩

/-- Ledger: cor-R-omega. The paper's statement: for fixed `k ≥ 2`,
`R(F_{k,m}) = Ω_k(m^(2-1/k) / (log m)²)`, written with explicit quantifiers: a constant
`c > 0` and a threshold beyond which `c m^(2-1/k) / (log m)² ≤ R(F_{k,m})`. `log` is the
natural logarithm; the base only changes `c`, and `cor_R_omega_log2` gives base two
with `c = 1/400`. Stated for every circuit realising `P_{k,m}`. -/
theorem cor_R_omega (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ C : Circuit (ForrelationCoord k t),
      CircuitRealises C (P k t) →
        c * (mValue t : ℝ) ^ (2 - 1 / (k : ℝ)) / Real.log (mValue t : ℝ) ^ 2 ≤
          (R (totalise (Fkm k t C)) : ℝ) := by
  obtain ⟨t₀, ht₀⟩ := prop_4_2 k hk
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨Real.log 2 ^ 2 / 400, by positivity, max t₀ 8, fun t ht C hC => ?_⟩
  have ht8 : 8 ≤ t := le_trans (le_max_right _ _) ht
  have h := rpow_le_of_Gvalue_lt hk ht8 (ht₀ t (le_trans (le_max_left _ _) ht) C hC)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog : Real.log (mValue t : ℝ) = 2 * (t : ℝ) * Real.log 2 := by
    have : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
    rw [this, Real.log_pow]
    push_cast
    ring
  have e : Real.log 2 ^ 2 / 400 * (mValue t : ℝ) ^ (2 - 1 / (k : ℝ)) /
      Real.log (mValue t : ℝ) ^ 2 =
      (1 / 400 : ℝ) * ((4 : ℝ) ^ t) ^ (2 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 := by
    rw [hlog, mValue_cast]
    have := hl2.ne'
    have := ht0.ne'
    field_simp <;> ring_nf
  rw [e]
  exact h

/-- Ledger: cor-R-omega. The same bound with base-two logarithms and the explicit
constant `1/400`, from `t = 8` beyond the Forrelation threshold. -/
theorem cor_R_omega_log2 (k : ℕ) (hk : 2 ≤ k) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ C : Circuit (ForrelationCoord k t),
      CircuitRealises C (P k t) →
        (1 / 400 : ℝ) * (mValue t : ℝ) ^ (2 - 1 / (k : ℝ)) / Real.logb 2 (mValue t : ℝ) ^ 2 ≤
          (R (totalise (Fkm k t C)) : ℝ) := by
  obtain ⟨t₀, ht₀⟩ := prop_4_2 k hk
  refine ⟨max t₀ 8, fun t ht C hC => ?_⟩
  have h := rpow_le_of_Gvalue_lt hk (le_trans (le_max_right _ _) ht)
    (ht₀ t (le_trans (le_max_left _ _) ht) C hC)
  rw [logb_mValue, mValue_cast]
  exact h

end QuarticQuery.Paper
