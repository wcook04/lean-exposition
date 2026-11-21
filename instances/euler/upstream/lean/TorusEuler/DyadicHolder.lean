import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic

/-!
The low/high dyadic summation in Appendix A,
`cc:holder:eq:frozen-bound`, from supplied block bounds.
-/

open Filter
open scoped NNReal

namespace TorusEuler

private theorem four_thirds_le_sqrt_two : (4 / 3 : ℝ) ≤ Real.sqrt 2 :=
  (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)

private theorem inv_sqrt_two_le_three_quarters : (Real.sqrt 2)⁻¹ ≤ (3 / 4 : ℝ) := by
  have h := inv_anti₀ (by norm_num : (0 : ℝ) < 4 / 3) four_thirds_le_sqrt_two
  norm_num at h ⊢
  exact h

private theorem sqrt_two_pow_sq (j : ℕ) : ((Real.sqrt 2) ^ j) ^ 2 = (2 : ℝ) ^ j := by
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul, Real.sq_sqrt (by norm_num)]

private theorem dyadic_half_pow (j : ℕ) : ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ) = (Real.sqrt 2) ^ j := by
  rw [← Real.sqrt_eq_rpow, ← sqrt_two_pow_sq, Real.sqrt_sq (by positivity)]

private theorem dyadic_neg_half_pow (j : ℕ) :
    ((2 : ℝ) ^ j) ^ (-1 / 2 : ℝ) = ((Real.sqrt 2)⁻¹) ^ j := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by positivity),
    dyadic_half_pow, inv_pow]

private theorem sqrt_two_inv_geom : Summable (fun j : ℕ => ((Real.sqrt 2)⁻¹) ^ j) :=
  summable_geometric_of_lt_one (by positivity)
    (inv_sqrt_two_le_three_quarters.trans_lt (by norm_num))

private theorem sqrt_two_inv_geom_sum :
    (∑' j : ℕ, ((Real.sqrt 2)⁻¹) ^ j) ≤ 4 := by
  rw [tsum_geometric_of_lt_one (by positivity)
    (inv_sqrt_two_le_three_quarters.trans_lt (by norm_num))]
  apply (inv_le_iff_one_le_mul₀ (by linarith [inv_sqrt_two_le_three_quarters])).2
  linarith [inv_sqrt_two_le_three_quarters]

private theorem sqrt_two_geom_prefix (n : ℕ) :
    (∑ j ∈ Finset.range n, (Real.sqrt 2) ^ j) ≤ 3 * (Real.sqrt 2) ^ n := by
  have hfactor : (1 / 3 : ℝ) ≤ Real.sqrt 2 - 1 := by linarith [four_thirds_le_sqrt_two]
  have hs : 0 ≤ ∑ j ∈ Finset.range n, (Real.sqrt 2) ^ j := by positivity
  have h := mul_le_mul_of_nonneg_left hfactor hs
  rw [geom_sum_mul] at h
  linarith

/-- For a positive distance below one, choose the first dyadic power
crossing its reciprocal. The two estimates control the low and high
blocks at this same index. -/
private theorem exists_dyadic_split {d : ℝ} (hd : 0 < d) (hd₁ : d < 1) :
    ∃ n : ℕ, d * (Real.sqrt 2) ^ n ≤ 2 * Real.sqrt d ∧
      ((Real.sqrt 2)⁻¹) ^ n ≤ Real.sqrt d := by
  have hex : ∃ n : ℕ, 1 ≤ d * (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := eventually_atTop.1
      ((tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).eventually_ge_atTop d⁻¹)
    exact ⟨n, (inv_le_iff_one_le_mul₀ hd).1 (hn n le_rfl) |>.trans_eq (mul_comm _ _)⟩
  let n := Nat.find hex
  have hcut : 1 ≤ d * (2 : ℝ) ^ n := Nat.find_spec hex
  have hn : n ≠ 0 := by
    intro h
    rw [h, pow_zero, mul_one] at hcut
    exact (not_le.mpr hd₁) hcut
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hprev : d * (2 : ℝ) ^ k < 1 := by
    apply lt_of_not_ge
    exact Nat.find_min hex (show k < n by rw [hk]; omega)
  have hup : d * (2 : ℝ) ^ n ≤ 2 := by
    rw [hk, pow_succ, ← mul_assoc]
    linarith
  refine ⟨n, ?_, ?_⟩
  · apply (sq_le_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, sqrt_two_pow_sq, mul_pow, Real.sq_sqrt hd.le]
    calc
      d ^ 2 * (2 : ℝ) ^ n = d * (d * (2 : ℝ) ^ n) := by ring
      _ ≤ d * 2 := mul_le_mul_of_nonneg_left hup hd.le
      _ ≤ 2 ^ 2 * d := by linarith
  · apply (Real.le_sqrt (by positivity) hd.le).2
    rw [inv_pow, inv_pow, sqrt_two_pow_sq]
    exact (inv_le_iff_one_le_mul₀ (by positivity)).2 hcut

/-- The Banach-valued dyadic sum converges uniformly and obeys a
quantitative half-Hölder estimate. The hypotheses are the output block
supremum and Lipschitz estimates supplied by the multiplier kernels. -/
theorem dyadicSeries_halfHolder {X E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [CompleteSpace E] (block : ℕ → X → E)
    {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ j x, ‖block j x‖ ≤ C * ((2 : ℝ) ^ j) ^ (-1 / 2 : ℝ))
    (hLip : ∀ j x y, ‖block j x - block j y‖ ≤ C * ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ) * dist x y) :
    TendstoUniformly (fun N x => ∑ j ∈ Finset.range N, block j x)
        (fun x => ∑' j, block j x) atTop ∧
      (∀ x, ‖∑' j, block j x‖ ≤ 4 * C) ∧
      (∀ x y, ‖(∑' j, block j x) - ∑' j, block j y‖ ≤ 14 * C * Real.sqrt (dist x y)) := by
  simp_rw [dyadic_neg_half_pow] at hsup
  simp_rw [dyadic_half_pow] at hLip
  let r := (Real.sqrt 2)⁻¹
  have hg : Summable (fun j : ℕ => r ^ j) := sqrt_two_inv_geom
  have habs (x : X) : Summable (fun j => ‖block j x‖) :=
    (hg.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hsup j x)
  have hbound (x : X) : ‖∑' j, block j x‖ ≤ 4 * C := by
    calc
      _ ≤ ∑' j, ‖block j x‖ := norm_tsum_le_tsum_norm (habs x)
      _ ≤ ∑' j : ℕ, C * r ^ j := (habs x).tsum_le_tsum (fun j => hsup j x) (hg.mul_left C)
      _ = C * ∑' j : ℕ, r ^ j := tsum_mul_left
      _ ≤ C * 4 := mul_le_mul_of_nonneg_left sqrt_two_inv_geom_sum hC
      _ = _ := mul_comm _ _
  refine ⟨tendstoUniformly_tsum_nat (hg.mul_left C) hsup, hbound, ?_⟩
  intro x y
  by_cases hxy : x = y
  · simp [hxy]
  let d := dist x y
  have hd : 0 < d := dist_pos.mpr hxy
  by_cases hlarge : 1 ≤ d
  · have hroot : 1 ≤ Real.sqrt d := (Real.le_sqrt (by norm_num) hd.le).2 (by simpa using hlarge)
    calc
      _ ≤ ‖∑' j, block j x‖ + ‖∑' j, block j y‖ := norm_sub_le _ _
      _ ≤ 8 * C := by linarith [hbound x, hbound y]
      _ ≤ (14 * C) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hroot (by positivity)
  obtain ⟨n, hlow, hhigh⟩ := exists_dyadic_split hd (lt_of_not_ge hlarge)
  let size := fun j => ‖block j x - block j y‖
  have hsize (j : ℕ) : size j ≤ (2 * C) * r ^ j := by
    change ‖block j x - block j y‖ ≤ _
    refine (norm_sub_le _ _).trans ?_
    calc
      _ ≤ C * r ^ j + C * r ^ j := add_le_add (hsup j x) (hsup j y)
      _ = _ := by ring
  have hs : Summable size :=
    (hg.mul_left (2 * C)).of_nonneg_of_le (fun _ => norm_nonneg _) hsize
  have hprefix : (∑ j ∈ Finset.range n, size j) ≤ 6 * C * Real.sqrt d := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, C * (Real.sqrt 2) ^ j * d :=
        Finset.sum_le_sum fun j _ => hLip j x y
      _ = C * d * ∑ j ∈ Finset.range n, (Real.sqrt 2) ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ C * d * (3 * (Real.sqrt 2) ^ n) :=
        mul_le_mul_of_nonneg_left (sqrt_two_geom_prefix n) (mul_nonneg hC hd.le)
      _ = (3 * C) * (d * (Real.sqrt 2) ^ n) := by ring
      _ ≤ (3 * C) * (2 * Real.sqrt d) := mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = _ := by ring
  have htail : (∑' j : ℕ, size (j + n)) ≤ 8 * C * Real.sqrt d := by
    have hmajor : Summable (fun j : ℕ => ((2 * C) * r ^ n) * r ^ j) := hg.mul_left _
    calc
      _ ≤ ∑' j : ℕ, ((2 * C) * r ^ n) * r ^ j := by
        apply ((summable_nat_add_iff n).2 hs).tsum_le_tsum _ hmajor
        intro j
        exact (hsize (j + n)).trans_eq (by rw [pow_add]; ring)
      _ = ((2 * C) * r ^ n) * ∑' j : ℕ, r ^ j := tsum_mul_left
      _ ≤ ((2 * C) * r ^ n) * 4 := mul_le_mul_of_nonneg_left sqrt_two_inv_geom_sum (by positivity)
      _ = (8 * C) * r ^ n := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hhigh (by positivity)
  rw [← (habs x).of_norm.tsum_sub (habs y).of_norm]
  calc
    _ ≤ ∑' j, size j := norm_tsum_le_tsum_norm hs
    _ = (∑ j ∈ Finset.range n, size j) + ∑' j : ℕ, size (j + n) :=
      (hs.sum_add_tsum_nat_add n).symm
    _ ≤ _ := by linarith

/-- The dyadic increment estimate in Mathlib's Hölder-continuity form. -/
theorem dyadicSeries_holderWith {X E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [CompleteSpace E] (block : ℕ → X → E)
    {C : ℝ≥0}
    (hsup : ∀ j x, ‖block j x‖ ≤ C * ((2 : ℝ) ^ j) ^ (-1 / 2 : ℝ))
    (hLip : ∀ j x y, ‖block j x - block j y‖ ≤ C * ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ) * dist x y) :
    HolderWith (14 * C) (1 / 2) (fun x => ∑' j, block j x) := by
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ (NNReal.coe_nonneg _),
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_div, NNReal.coe_rpow,
    NNReal.coe_one, ← dist_nndist, dist_eq_norm, ← Real.sqrt_eq_rpow] using
    (dyadicSeries_halfHolder block C.coe_nonneg hsup hLip).2.2 x y

end TorusEuler
