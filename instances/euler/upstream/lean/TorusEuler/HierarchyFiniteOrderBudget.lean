import TorusEuler.HierarchyDepthAssembly
import TorusEuler.ThresholdSelection

/-! Uniform derivative-order and parent-loss budgets for the solved depth. -/

namespace TorusEuler

/-- A single finite order budget controls every requested order through the
retained depth. The internal derivative reserve is included in the order
argument of the analytic cost table. -/
theorem hierarchy_level_bounds_through_depth {s : HierarchyMeasuredLevels} {freq L K : ℝ}
    {P m : ℕ} (rec : HierarchyNormRecurrence s freq L K P (m + 3 * P))
    (hf : 1 ≤ freq) (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hsmall : L ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1) :
    ∀ n ≤ m, ∀ p ∈ Finset.Icc 1 P,
      HierarchyLevelBound s freq L (hierarchyLevelConstant P K P) n p := by
  intro n hn p hp
  obtain ⟨hp₁,hpP⟩ := Finset.mem_Icc.mp hp
  exact (hierarchy_level_bounds rec hf hL hK hsmall p hp₁ hpP n (by omega)).mono hf hL
    (hierarchyLevelConstant_monotone (zero_le_one.trans hK) hpP)

/-- The loss budget of the level induction is part of the one absolute
parent exponent used by the wave step. -/
theorem hierarchy_level_budget_of_step_budget {D freq Γ : ℝ} {b p : ℕ}
    (hD : 1 ≤ D) (hf : 1 ≤ freq) (hΓ : 1 ≤ Γ) (hb : 6 * p ≤ b)
    (hstep : Γ * D ^ b ≤ freq ^ (1 / 32 : ℝ)) :
    (D ^ p) ^ 6 * freq ^ (-1 / 12 : ℝ) ≤ 1 := by
  have hfreq := zero_lt_one.trans_le hf
  have hpow : (D ^ p) ^ 6 ≤ Γ * D ^ b := by
    rw [← pow_mul, Nat.mul_comm p]
    exact (pow_le_pow_right₀ hD hb).trans (le_mul_of_one_le_left (by positivity) hΓ)
  calc
    _ ≤ freq ^ (1 / 32 : ℝ) * freq ^ (-1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_right (hpow.trans hstep) (by positivity)
    _ = freq ^ (1 / 32 - 1 / 12 : ℝ) := by
      have hneg : (-1 / 12 : ℝ) = -(1 / 12) := by ring
      rw [hneg, sub_eq_add_neg, Real.rpow_add hfreq]
    _ ≤ 1 := by
      rw [← Real.rpow_zero freq]
      exact Real.rpow_le_rpow_of_exponent_le hf (by norm_num)

/-- Raising the expense table at the requested order accounts for the
finite reserve used internally by the hierarchy induction. -/
theorem hierarchy_level_analysis_cost_is_finite {ι : Type*} [Fintype ι]
    (b : ℕ) (cost : ι → ℕ → ℕ → ℝ) (s m P : ℕ)
    (hm : m ≤ 7 * frequencyExponent b s) (hP : P ≤ 7 * frequencyExponent b s) (j : ι) :
    |cost j (m + 3 * P) P| ≤
      fixedOrderThreshold b (fun j n p => cost j (n + 3 * p) p) s :=
  abs_fixedOrderCost_le_threshold b (fun j n p => cost j (n + 3 * p) p) j hm hP

end TorusEuler
