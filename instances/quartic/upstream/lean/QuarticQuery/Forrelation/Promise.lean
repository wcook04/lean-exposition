module

public import QuarticQuery.Forrelation.Product

/-!
# `P` is the partial function of equation (4)

`P` is defined in `Statement` by integer tests. Here the tests are shown to be the
real thresholds `Φ ≥ δ` and `|Φ| ≤ δ/2`, so `P` is exactly the partial function of
(4), and the smallest interesting instance is checked to have inputs on each side.
-/

@[expose] public section

namespace QuarticQuery.Forrelation

/-- Ledger: eq-3. `δ = 2^(-5k)`. -/
noncomputable def delta (k : ℕ) : ℝ := (2 : ℝ) ^ (-(5 * (k : ℤ)))

theorem delta_eq (k : ℕ) : delta k = ((2 : ℝ) ^ (5 * k))⁻¹ := by
  rw [delta, zpow_neg]
  norm_cast

theorem delta_pos (k : ℕ) : 0 < delta k := by
  rw [delta_eq]
  positivity

theorem forrelationDenominator_pos (k t : ℕ) : 0 < forrelationDenominator k t := by
  unfold forrelationDenominator
  positivity

/-- Ledger: claim-integer-tests. The first test of (4). -/
theorem delta_le_Phi_iff (k t : ℕ) (z : BitInput (ForrelationCoord k t)) :
    delta k ≤ Phi k t z ↔
      (2 : ℤ) ^ (5 * k) * forrelationNumerator k t z ≥ forrelationDenominator k t := by
  have hM : (0 : ℝ) < forrelationDenominator k t := by
    exact_mod_cast forrelationDenominator_pos k t
  have hA : (0 : ℝ) < (2 : ℝ) ^ (5 * k) := by positivity
  rw [Phi, delta_eq, inv_eq_one_div, div_le_div_iff₀ hA hM, one_mul, ge_iff_le, mul_comm]
  exact_mod_cast Iff.rfl

/-- Ledger: claim-integer-tests. The second test of (4). -/
theorem abs_Phi_le_iff (k t : ℕ) (z : BitInput (ForrelationCoord k t)) :
    |Phi k t z| ≤ delta k / 2 ↔
      (2 : ℤ) ^ (5 * k + 1) * |forrelationNumerator k t z| ≤ forrelationDenominator k t := by
  have hM : (0 : ℝ) < forrelationDenominator k t := by
    exact_mod_cast forrelationDenominator_pos k t
  have hA : (0 : ℝ) < (2 : ℝ) ^ (5 * k + 1) := by positivity
  have hδ : delta k / 2 = 1 / (2 : ℝ) ^ (5 * k + 1) := by
    rw [delta_eq, pow_succ, inv_eq_one_div, div_div]
  rw [Phi, abs_div, abs_of_pos hM, hδ, div_le_div_iff₀ hM hA, one_mul, mul_comm]
  exact_mod_cast Iff.rfl

/-- Ledger: eq-4. The two cases cannot both hold, for any `k`. -/
theorem cases_disjoint (k t : ℕ) (z : BitInput (ForrelationCoord k t)) :
    ¬ (delta k ≤ Phi k t z ∧ |Phi k t z| ≤ delta k / 2) := by
  rintro ⟨h1, h2⟩
  have := delta_pos k
  have := le_abs_self (Phi k t z)
  linarith

/-- Ledger: eq-4, def-P. The 1-inputs. -/
theorem P_eq_some_true_iff (k t : ℕ) (z : BitInput (ForrelationCoord k t)) :
    P k t z = some true ↔ delta k ≤ Phi k t z := by
  rw [delta_le_Phi_iff]
  simp only [P]
  split_ifs <;> simp_all

/-- Ledger: eq-4, def-P. The 0-inputs. -/
theorem P_eq_some_false_iff (k t : ℕ) (z : BitInput (ForrelationCoord k t)) :
    P k t z = some false ↔ |Phi k t z| ≤ delta k / 2 := by
  have hd := cases_disjoint k t z
  constructor
  · intro h
    rw [abs_Phi_le_iff]
    simp only [P] at h
    split_ifs at h <;> first | assumption | simp at h
  · intro h
    have h1 : ¬ delta k ≤ Phi k t z := fun e => hd ⟨e, h⟩
    rw [delta_le_Phi_iff] at h1
    rw [abs_Phi_le_iff] at h
    simp only [P]
    split_ifs <;> first | rfl | contradiction

/-- Ledger: eq-4, def-P. Everything else is outside the promise, including large
negative `Φ`. -/
theorem P_eq_none_iff (k t : ℕ) (z : BitInput (ForrelationCoord k t)) :
    P k t z = none ↔ ¬ delta k ≤ Phi k t z ∧ ¬ |Phi k t z| ≤ delta k / 2 := by
  rw [← P_eq_some_true_iff, ← P_eq_some_false_iff]
  cases P k t z with
  | none => simp
  | some b => cases b <;> simp

/-- Ledger: eq-4. `P` as a single statement: the value of `P` at every input. -/
theorem P_eq_cases (k t : ℕ) (z : BitInput (ForrelationCoord k t)) :
    P k t z =
      open Classical in
      if delta k ≤ Phi k t z then some true
      else if |Phi k t z| ≤ delta k / 2 then some false
      else none := by
  split_ifs with h1 h2
  · exact (P_eq_some_true_iff k t z).2 h1
  · exact (P_eq_some_false_iff k t z).2 h2
  · exact (P_eq_none_iff k t z).2 ⟨h1, h2⟩

theorem promised_P_iff (k t : ℕ) (z : BitInput (ForrelationCoord k t)) :
    promised (P k t) z ↔ delta k ≤ Phi k t z ∨ |Phi k t z| ≤ delta k / 2 := by
  rw [promised, ← P_eq_some_true_iff, ← P_eq_some_false_iff]
  constructor
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inr hb
    · exact Or.inl hb
  · rintro (h | h)
    exacts [⟨_, h⟩, ⟨_, h⟩]

end QuarticQuery.Forrelation
