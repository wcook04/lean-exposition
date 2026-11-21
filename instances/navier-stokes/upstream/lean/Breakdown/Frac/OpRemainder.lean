import Breakdown.Frac.StOperator

open scoped ContDiff

noncomputable section

namespace Breakdown

private lemma lineValue_hasDerivAt {f : Space → Space} (hf : ContDiff ℝ 3 f) (x z : Space)
    {k : ℕ} (hk : k < 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ k f (x + s • z) (fun _ => z))
      (iteratedFDeriv ℝ (k + 1) f (x + t • z) (fun _ => z)) t := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) (x + t • z) :=
    (hf.differentiable_iteratedFDeriv (by exact_mod_cast hk)) _
  have hline : HasDerivAt (fun s : ℝ => x + s • z) z t := by
    simpa using ((hasDerivAt_id t).smul_const z).const_add x
  have h1 := hd.hasFDerivAt.comp_hasDerivAt t hline
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Space) Space
    (fun _ => z)).hasFDerivAt.comp_hasDerivAt t h1
  exact h2

private lemma unitInterval_bound {g g' : ℝ → Space} {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ t, HasDerivAt g (g' t) t) (h0 : g 0 = 0)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖g' t‖ ≤ B) : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖g t‖ ≤ B := by
  intro t ht
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := g') (C := B)
    (fun s _ => (hg s).hasDerivWithinAt) (fun s hs => hb s (Set.Ico_subset_Icc_self hs)) t ht
  rw [h0, sub_zero, sub_zero] at h
  exact h.trans (mul_le_of_le_one_right hB ht.2)

theorem remainderBound : RemainderBoundStatement := by
  intro f hf x z C hC
  set φ : ℕ → ℝ → Space := fun k s => iteratedFDeriv ℝ k f (x + s • z) (fun _ => z) with hφ
  have hd : ∀ k < 3, ∀ t, HasDerivAt (φ k) (φ (k + 1) t) t :=
    fun k hk t => lineValue_hasDerivAt hf x z hk t
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • z ∈ Metric.closedBall x ‖z‖ := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x (Metric.mem_closedBall_self (norm_nonneg _)))
  have hB0 : 0 ≤ C * ‖z‖ ^ 3 := mul_nonneg hC0 (pow_nonneg (norm_nonneg _) 3)
  have h3 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖φ 3 t‖ ≤ C * ‖z‖ ^ 3 := by
    intro t ht
    refine ((iteratedFDeriv ℝ 3 f (x + t • z)).le_opNorm _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (hC _ (hmem t ht)) (pow_nonneg (norm_nonneg _) 3)
  have h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖φ 2 t - φ 2 0‖ ≤ C * ‖z‖ ^ 3 :=
    unitInterval_bound (g := fun t => φ 2 t - φ 2 0) hB0
      (fun t => (hd 2 (by norm_num) t).sub_const _) (sub_self _) h3
  have h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖φ 1 t - φ 1 0 - t • φ 2 0‖ ≤ C * ‖z‖ ^ 3 := by
    refine unitInterval_bound (g := fun t => φ 1 t - φ 1 0 - t • φ 2 0) hB0 (fun t => ?_)
      (by simp) h2
    exact (((hd 1 (by norm_num) t).sub_const _).sub ((hasDerivAt_id' t).smul_const (φ 2 0))).congr_deriv
      (by simp)
  have h0 := unitInterval_bound
    (g := fun t => φ 0 t - φ 0 0 - t • φ 1 0 - (t ^ 2 / 2) • φ 2 0) hB0 (fun t => ?_)
      (by simp) h1 1 (Set.right_mem_Icc.2 zero_le_one)
  · have hv : (![z, z] : Fin 2 → Space) = fun _ => z := by
      funext i
      fin_cases i <;> rfl
    have he : secondOrderRemainder f x z =
        φ 0 1 - φ 0 0 - (1 : ℝ) • φ 1 0 - ((1 : ℝ) ^ 2 / 2) • φ 2 0 := by
      simp only [secondOrderRemainder, hφ, hv, one_smul, zero_smul, add_zero,
        iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply]
      norm_num
    rw [he]
    exact h0
  · have hq : HasDerivAt (fun s : ℝ => (s ^ 2 / 2) • φ 2 0) (t • φ 2 0) t :=
      (((hasDerivAt_pow 2 t).div_const 2).smul_const (φ 2 0)).congr_deriv (by norm_num)
    exact ((((hd 0 (by norm_num) t).sub_const _).sub ((hasDerivAt_id' t).smul_const (φ 1 0))).sub
      hq).congr_deriv (by simp)

end Breakdown
