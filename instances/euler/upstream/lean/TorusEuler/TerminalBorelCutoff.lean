import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

/-! Shrinking scalar cutoffs for the Taylor data at the terminal slice. -/

open Filter Topology
open scoped ContDiff

namespace TorusEuler

noncomputable section

private def terminalBorelBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private def terminalBorelBase (n : ℕ) (t : ℝ) : ℝ :=
  (t ^ n / (n.factorial : ℝ)) * terminalBorelBump t

private theorem contDiff_terminalBorelBase (n : ℕ) :
    ContDiff ℝ ∞ (terminalBorelBase n) :=
  ((contDiff_id.pow n).div_const _).mul terminalBorelBump.contDiff

/-- A cutoff time monomial of degree `n` at radius `ε`. -/
def terminalBorelAtom (n : ℕ) (ε t : ℝ) : ℝ :=
  ε ^ n • terminalBorelBase n (ε⁻¹ • t)

theorem contDiff_terminalBorelAtom (n : ℕ) (ε : ℝ) :
    ContDiff ℝ ∞ (terminalBorelAtom n ε) :=
  ((contDiff_terminalBorelBase n).comp (contDiff_id.const_smul _)).const_smul _

/-- At a positive scale the cutoff monomial agrees with its normalized
polynomial in a neighborhood of the endpoint. -/
theorem terminalBorelAtom_eventuallyEq_polynomial (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    terminalBorelAtom n ε =ᶠ[𝓝 0] fun t => t ^ n / (n.factorial : ℝ) := by
  have hmap : Tendsto (fun t : ℝ => ε⁻¹ • t) (𝓝 0) (𝓝 0) := by
    have h : ContinuousAt (fun t : ℝ => ε⁻¹ • t) (0 : ℝ) := by fun_prop
    simpa only [smul_zero] using h.tendsto
  filter_upwards [hmap terminalBorelBump.eventuallyEq_one] with t ht
  change terminalBorelBump (ε⁻¹ • t) = 1 at ht
  rw [terminalBorelAtom, terminalBorelBase, ht, mul_one, smul_eq_mul, smul_eq_mul, mul_pow, ← mul_div_assoc,
    ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow, one_mul]

/-- The atom has exactly one nonzero Taylor coefficient at the endpoint. -/
theorem iteratedDeriv_terminalBorelAtom_zero (n k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    iteratedDeriv k (terminalBorelAtom n ε) 0 = if k = n then 1 else 0 := by
  rw [(terminalBorelAtom_eventuallyEq_polynomial n hε).iteratedDeriv_eq k,
    iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
  split_ifs
  · exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  · simp

theorem iteratedFDeriv_terminalBorelAtom_zero_apply (n k : ℕ) {ε : ℝ} (hε : 0 < ε)
    (v : Fin k → ℝ) :
    iteratedFDeriv ℝ k (terminalBorelAtom n ε) 0 v = (∏ i, v i) * (if k = n then 1 else 0) := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_terminalBorelAtom_zero n k hε,
    smul_eq_mul]

/-- The derivative of order `k` has one inverse-radius factor for each time
derivative. The estimate also applies above the order of the monomial. -/
theorem exists_terminalBorelAtom_fderiv_bound (n k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ε : ℝ}, 0 < ε → ∀ t,
      ‖iteratedFDeriv ℝ k (terminalBorelAtom n ε) t‖ ≤ A * ε ^ n * (ε⁻¹) ^ k := by
  have hBase : HasCompactSupport (terminalBorelBase n) :=
    terminalBorelBump.hasCompactSupport.mul_left
  have hSmooth := contDiff_terminalBorelBase n
  obtain ⟨A, hA⟩ := (hBase.iteratedFDeriv (𝕜 := ℝ) k).exists_bound_of_continuous
    (hSmooth.continuous_iteratedFDeriv (mod_cast le_top))
  refine ⟨A, (norm_nonneg _).trans (hA 0), ?_⟩
  intro ε hε t
  have hSmooth' : ContDiff ℝ k (fun u => terminalBorelBase n (ε⁻¹ • u)) :=
    (hSmooth.of_le (mod_cast le_top)).comp (contDiff_id.const_smul _)
  change ‖iteratedFDeriv ℝ k (fun u => ε ^ n • terminalBorelBase n (ε⁻¹ • u)) t‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' hSmooth'.contDiffAt,
    iteratedFDeriv_comp_const_smul ε⁻¹ (hSmooth.of_le (mod_cast le_top)),
    norm_smul, norm_smul, norm_pow, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hε, abs_of_pos (inv_pos.mpr hε)]
  calc
    _ ≤ ε ^ n * ((ε⁻¹) ^ k * A) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hA _) (by positivity)) (by positivity)
    _ = _ := by ring

/-- At orders below the degree the atom gains a positive power of its radius. -/
theorem exists_terminalBorelAtom_fderiv_bound_of_le (n k : ℕ) (hk : k ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ε : ℝ}, 0 < ε → ∀ t,
      ‖iteratedFDeriv ℝ k (terminalBorelAtom n ε) t‖ ≤ A * ε ^ (n - k) := by
  obtain ⟨A, hA, h⟩ := exists_terminalBorelAtom_fderiv_bound n k
  refine ⟨A, hA, ?_⟩
  intro ε hε t
  refine (h hε t).trans_eq ?_
  rw [pow_sub₀ ε hε.ne' hk, inv_pow, mul_assoc]

/-- A single positive radius makes every weighted derivative of order
strictly below `n` as small as prescribed. -/
theorem exists_terminalBorelAtom_fderiv_small (n : ℕ) (W : ℕ → ℝ) (hW : ∀ k, 0 ≤ W k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ k < n, ∀ t,
      W k * ‖iteratedFDeriv ℝ k (terminalBorelAtom n ε) t‖ ≤ δ := by
  choose A hA hBound using exists_terminalBorelAtom_fderiv_bound n
  let B := 1 + ∑ k ∈ Finset.range n, W k * A k
  have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun k _ => mul_nonneg (hW k) (hA k))
  let ε := min 1 (δ / B)
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hδ hB)
  have hε₁ : ε ≤ 1 := min_le_left _ _
  have hεB : ε * B ≤ δ := (le_div_iff₀ hB).mp (min_le_right _ _)
  refine ⟨ε, hε, hε₁, ?_⟩
  intro k hk t
  have hp : ε ^ (n - k) ≤ ε := by
    simpa only [pow_one] using pow_le_pow_of_le_one hε.le hε₁ (by omega : 1 ≤ n - k)
  have hAB : W k * A k ≤ B :=
    (Finset.single_le_sum (fun j _ => mul_nonneg (hW j) (hA j)) (Finset.mem_range.mpr hk)).trans
      (le_add_of_nonneg_left zero_le_one)
  calc
    _ ≤ W k * (A k * ε ^ n * ε⁻¹ ^ k) := mul_le_mul_of_nonneg_left (hBound k hε t) (hW k)
    _ = W k * (A k * ε ^ (n - k)) := by rw [pow_sub₀ ε hε.ne' (le_of_lt hk), inv_pow, mul_assoc]
    _ ≤ W k * (A k * ε) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (hA k)) (hW k)
    _ = W k * A k * ε := by ring
    _ ≤ B * ε := mul_le_mul_of_nonneg_right hAB hε.le
    _ ≤ δ := mul_comm B ε ▸ hεB

end

end TorusEuler
