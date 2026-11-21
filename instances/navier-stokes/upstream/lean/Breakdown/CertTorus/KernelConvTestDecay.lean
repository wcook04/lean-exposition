import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter
open scoped ContDiff Convolution

noncomputable section

namespace Breakdown.FarField

open Freq

private def mulRev : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := (ContinuousLinearMap.mul ℝ ℝ).flip

private lemma mulRev_apply (a b : ℝ) : mulRev a b = b * a := rfl

private lemma precompL_mulRev (u : Space →L[ℝ] ℝ) (v : ℝ) :
    (mulRev.precompL Space) u v = v • u := by
  ext w
  simp [mulRev_apply]

private lemma conv_mulRev_eq (g k : Space → ℝ) (y : Space) :
    (g ⋆[mulRev, volume] k) y = ∫ t, k (y - t) * g t := by
  simp [convolution_def, mulRev_apply]

private lemma integrable_kernel_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : Space → ℝ} {u : Space → E} (hk : Continuous k) (hu : Continuous u)
    (hcu : HasCompactSupport u) (y : Space) :
    Integrable (fun t => k (y - t) • u t) := by
  have hc : HasCompactSupport (fun t => k (y - t) • u t) :=
    HasCompactSupport.smul_left (f := fun t => k (y - t)) hcu
  exact ((hk.comp (continuous_const.sub continuous_id)).smul hu).integrable_of_hasCompactSupport hc

private lemma hasFDerivAt_conv_mulRev {g k : Space → ℝ} (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (hk : Continuous k) (y : Space) :
    HasFDerivAt (g ⋆[mulRev, volume] k) (∫ t, k (y - t) • fderiv ℝ g t) y := by
  have h := hcg.hasFDerivAt_convolution_left mulRev hg (hk.locallyIntegrable (μ := volume)) y
  simpa [convolution_def, precompL_mulRev] using h

private lemma conv_deriv_apply {g k : Space → ℝ} (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (hk : Continuous k) (y v : Space) :
    (∫ t, k (y - t) • fderiv ℝ g t) v = ∫ t, k (y - t) * fderiv ℝ g t v := by
  rw [ContinuousLinearMap.integral_apply
    (integrable_kernel_smul hk (hg.continuous_fderiv one_ne_zero) (hcg.fderiv ℝ) y)]
  rfl

private lemma integral_kernel_mul_deriv {g k : Space → ℝ} (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (hk : ContDiff ℝ 1 k) (y v : Space) :
    ∫ t, k (y - t) * fderiv ℝ g t v = ∫ t, fderiv ℝ k (y - t) v * g t := by
  have hkd : ∀ t, HasFDerivAt (fun t => k (y - t)) (-(fderiv ℝ k (y - t))) t := by
    intro t
    have h1 := (hk.differentiable one_ne_zero (y - t)).hasFDerivAt
    have h2 : HasFDerivAt (fun t : Space => y - t) (-(ContinuousLinearMap.id ℝ Space)) t :=
      (hasFDerivAt_id t).const_sub y
    exact (h1.comp t h2).congr_fderiv (by ext v; simp)
  have hfd : ∀ t, fderiv ℝ (fun t => k (y - t)) t v = -(fderiv ℝ k (y - t) v) := by
    intro t
    rw [(hkd t).fderiv]
    rfl
  have hkc : Continuous k := hk.continuous
  have hkdc : Continuous (fderiv ℝ k) := hk.continuous_fderiv one_ne_zero
  have i1 : Integrable (fun t => fderiv ℝ (fun t => k (y - t)) t v * g t) := by
    simp_rw [hfd]
    have := integrable_kernel_smul (k := fun x => -(fderiv ℝ k x v)) (u := g)
      ((hkdc.clm_apply continuous_const).neg) hg.continuous hcg y
    simpa using this
  have i2 : Integrable (fun t => k (y - t) * fderiv ℝ g t v) :=
    integrable_kernel_smul (u := fun t => fderiv ℝ g t v) hkc
      ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hcg.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] ℝ => L v) (by simp)) y
  have i3 : Integrable (fun t => k (y - t) * g t) :=
    integrable_kernel_smul hkc hg.continuous hcg y
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) i1 i2 i3
    (fun t _ => (hkd t).differentiableAt) (fun t _ => (hg.differentiable one_ne_zero) t)
  rw [hibp]
  simp_rw [hfd]
  rw [← integral_neg]
  congr 1
  funext t
  ring

private lemma norm_integral_kernel_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : Space → ℝ) (u : Space → E) (y : Space) (S : Set Space) (Q : ℝ) (hu : Integrable u)
    (hsupp : ∀ t, u t ≠ 0 → t ∈ S) (hk : ∀ t ∈ S, |k (y - t)| ≤ Q) :
    ‖∫ t, k (y - t) • u t‖ ≤ Q * ∫ t, ‖u t‖ := by
  calc ‖∫ t, k (y - t) • u t‖ ≤ ∫ t, Q * ‖u t‖ := by
        refine norm_integral_le_of_norm_le (hu.norm.const_mul Q) (Eventually.of_forall fun t => ?_)
        by_cases ht : u t = 0
        · simp [ht]
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hk t (hsupp t ht)) (norm_nonneg _)
    _ = Q * ∫ t, ‖u t‖ := integral_const_mul Q _

private lemma one_add_norm_le (y t : Space) {R s : ℝ} (hR : 0 ≤ R) (hs : 0 < s) (ht : ‖t‖ ≤ R) :
    1 + ‖y‖ ≤ (1 + R) * (1 + 1 / s) * (‖y - t‖ + s) := by
  have hd : 0 ≤ ‖y - t‖ := norm_nonneg _
  have h1 : (1 + 1 / s) * (‖y - t‖ + s) = ‖y - t‖ + 1 + s + ‖y - t‖ / s := by
    field_simp
    ring
  have h2 : 0 ≤ ‖y - t‖ / s := div_nonneg hd hs.le
  have h3 : ‖y‖ ≤ ‖t‖ + ‖y - t‖ := norm_le_insert' y t
  calc 1 + ‖y‖ ≤ 1 + R + ‖y - t‖ := by linarith
    _ ≤ (1 + R) * (1 + ‖y - t‖) := by nlinarith [mul_nonneg hR hd]
    _ ≤ (1 + R) * ((1 + 1 / s) * (‖y - t‖ + s)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [h1]
        linarith
    _ = (1 + R) * (1 + 1 / s) * (‖y - t‖ + s) := by ring

private lemma kernel_bound_on_ball {k : Space → ℝ} {C τ R : ℝ} (hτ : 0 < τ) (hR : 0 ≤ R)
    (hk : ∀ x, |k x| ≤ C / (‖x‖ + Real.sqrt τ) ^ 4) (y t : Space) (ht : ‖t‖ ≤ R) :
    |k (y - t)| ≤ C * ((1 + R) * (1 + 1 / Real.sqrt τ)) ^ 4 / (1 + ‖y‖) ^ 4 := by
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hle : 1 + ‖y‖ ≤ (1 + R) * (1 + 1 / Real.sqrt τ) * (‖y - t‖ + Real.sqrt τ) :=
    one_add_norm_le y t hR hs ht
  generalize Real.sqrt τ = s at hs hle hk ⊢
  generalize (1 + R) * (1 + 1 / s) = A at hle ⊢
  have hA0 : 0 < A := by
    by_contra h
    push Not at h
    have : A * (‖y - t‖ + s) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith [norm_nonneg y]
  have hd : 0 < ‖y - t‖ + s := by positivity
  have hC : 0 ≤ C := by
    by_contra h
    push Not at h
    have := div_neg_of_neg_of_pos h (pow_pos hd 4)
    linarith [abs_nonneg (k (y - t)), hk (y - t)]
  calc |k (y - t)| ≤ C / (‖y - t‖ + s) ^ 4 := hk (y - t)
    _ = C * A ^ 4 / (A * (‖y - t‖ + s)) ^ 4 := by
        rw [mul_pow, mul_comm C (A ^ 4), mul_div_mul_left _ _ (pow_ne_zero 4 hA0.ne')]
    _ ≤ C * A ^ 4 / (1 + ‖y‖) ^ 4 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ (by positivity) hle 4

private lemma norm_sum_smul_unit_le (a : Fin 3 → Fin 3 → Fin 3 → ℝ) (M : ℝ)
    (h : ∀ i j k, |a i j k| ≤ M) :
    ‖∑ i, (∑ j, ∑ k, a i j k) • unitVector i‖ ≤ 27 * M := by
  calc ‖∑ i, (∑ j, ∑ k, a i j k) • unitVector i‖
      ≤ ∑ i, ‖(∑ j, ∑ k, a i j k) • unitVector i‖ := norm_sum_le _ _
    _ = ∑ i, ‖∑ j, ∑ k, a i j k‖ := by simp [norm_smul, unitVector]
    _ ≤ ∑ i, ∑ j, ∑ k, ‖a i j k‖ := Finset.sum_le_sum fun i _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, M := by
        gcongr with i _ j _ k _
        exact h i j k
    _ = 27 * M := by
        simp
        ring

private lemma norm_sum_smulRight_unit_le (a : Fin 3 → Fin 3 → Fin 3 → (Space →L[ℝ] ℝ)) (M : ℝ)
    (h : ∀ i j k, ‖a i j k‖ ≤ M) :
    ‖∑ i, (∑ j, ∑ k, a i j k).smulRight (unitVector i)‖ ≤ 27 * M := by
  calc ‖∑ i, (∑ j, ∑ k, a i j k).smulRight (unitVector i)‖
      ≤ ∑ i, ‖(∑ j, ∑ k, a i j k).smulRight (unitVector i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖∑ j, ∑ k, a i j k‖ := by
        simp [ContinuousLinearMap.norm_smulRight_apply, unitVector]
    _ ≤ ∑ i, ∑ j, ∑ k, ‖a i j k‖ := Finset.sum_le_sum fun i _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, M := by
        gcongr with i _ j _ k _
        exact h i j k
    _ = 27 * M := by
        simp
        ring


private def testProd (φ : Space → Space) (j k : Fin 3) (z : Space) : ℝ := φ z j * φ z k

private lemma apply_sum_smulRight_unit (a : Fin 3 → (Space →L[ℝ] ℝ)) (v : Space) (i : Fin 3) :
    ((∑ l, (a l).smulRight (unitVector l)) v) i = a i v := by
  simp [unitVector, Pi.single_apply, mul_ite, Finset.sum_ite_eq]

private lemma div_four_le (M r : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r) {n : ℕ} (hn : n ≤ 4) :
    M / (1 + r) ^ 4 ≤ M / (1 + r) ^ n :=
  div_le_div_of_nonneg_left hM (by positivity) (pow_le_pow_right₀ (by linarith) hn)

theorem kernelConvTestDecay_of_kernel :
    LerayKernelBound → LerayKernelMeasurable → LerayKernelC1 → LerayKernelDivFree →
      KernelConvTestDecay := by
  intro hB _ hC1 hDiv τ hτ φ hφ
  obtain ⟨hφs, hφc, -⟩ := hφ
  obtain ⟨C, hCb⟩ := hB
  obtain ⟨R₀, hR₀⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  have hR : 0 ≤ max R₀ 0 := le_max_right _ _
  have hsuppR : ∀ t ∈ tsupport φ, ‖t‖ ≤ max R₀ 0 := by
    intro t ht
    have h := hR₀ ht
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_left _ _)
  have hFs : ∀ j k, ContDiff ℝ ∞ (testProd φ j k) := by
    intro j k
    have h1 := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hφs
    have h2 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hφs
    exact h1.mul h2
  have hF1 : ∀ j k, ContDiff ℝ 1 (testProd φ j k) := fun j k =>
    (hFs j k).of_le (by exact_mod_cast le_top)
  have hFc : ∀ j k, HasCompactSupport (testProd φ j k) := by
    intro j k
    exact hφc.comp_left (g := fun v : Space => v j * v k) (by simp)
  have hFsupp : ∀ j k, tsupport (testProd φ j k) ⊆ tsupport φ := by
    intro j k
    apply closure_mono
    intro t ht
    simp only [Function.mem_support] at ht ⊢
    intro h0
    apply ht
    simp [testProd, h0]
  have hKc1 : ∀ i j k, ContDiff ℝ 1 (lerayKernel i j k τ) := fun i j k => hC1 i j k τ hτ
  have hKc : ∀ i j k, Continuous (lerayKernel i j k τ) := fun i j k => (hKc1 i j k).continuous
  have hFint : ∀ j k, Integrable (testProd φ j k) := fun j k =>
    (hFs j k).continuous.integrable_of_hasCompactSupport (hFc j k)
  have hFdint : ∀ j k, Integrable (fun t => fderiv ℝ (testProd φ j k) t) := fun j k =>
    ((hF1 j k).continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport ((hFc j k).fderiv ℝ)
  have hform : (fun y => -kernelConv τ (tensorField φ φ) y) =
      fun y => -∑ i, (∑ j, ∑ k, (testProd φ j k ⋆[mulRev, volume] lerayKernel i j k τ) y) •
        unitVector i := by
    funext y
    congr 1
    unfold kernelConv
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [conv_mulRev_eq]
        rfl
      · intro k _
        exact integrable_kernel_smul (hKc i j k) (hFs j k).continuous (hFc j k) y
    · intro j _
      exact integrable_finsetSum _ fun k _ =>
        integrable_kernel_smul (hKc i j k) (hFs j k).continuous (hFc j k) y
  rw [hform]
  have hcs : ∀ i j k, ContDiff ℝ ∞ (testProd φ j k ⋆[mulRev, volume] lerayKernel i j k τ) :=
    fun i j k => (hFc j k).contDiff_convolution_left mulRev (hFs j k)
      ((hKc i j k).locallyIntegrable (μ := volume))
  have hcd : ∀ i j k y, HasFDerivAt (testProd φ j k ⋆[mulRev, volume] lerayKernel i j k τ)
      (∫ t, lerayKernel i j k τ (y - t) • fderiv ℝ (testProd φ j k) t) y := fun i j k y =>
    hasFDerivAt_conv_mulRev (hF1 j k) (hFc j k) (hKc i j k) y
  have hfd : ∀ y, HasFDerivAt
      (fun y => -∑ i, (∑ j, ∑ k, (testProd φ j k ⋆[mulRev, volume] lerayKernel i j k τ) y) •
        unitVector i)
      (-∑ i, (∑ j, ∑ k, ∫ t, lerayKernel i j k τ (y - t) • fderiv ℝ (testProd φ j k) t).smulRight
        (unitVector i)) y := by
    intro y
    apply HasFDerivAt.neg
    apply HasFDerivAt.fun_sum
    intro i _
    apply HasFDerivAt.smul_const
    apply HasFDerivAt.fun_sum
    intro j _
    apply HasFDerivAt.fun_sum
    intro k _
    exact hcd i j k y
  have hC0 : 0 ≤ C := by
    have h := hCb 0 0 0 τ 0 hτ
    have hpos : 0 < (‖(0 : Space)‖ + Real.sqrt τ) ^ 4 := by
      have := Real.sqrt_pos.mpr hτ
      positivity
    by_contra hneg
    push Not at hneg
    have := div_neg_of_neg_of_pos hneg hpos
    linarith [abs_nonneg (lerayKernel 0 0 0 τ 0)]
  set A := (1 + max R₀ 0) * (1 + 1 / Real.sqrt τ) with hA
  set S := ∑ j : Fin 3, ∑ k : Fin 3,
    ((∫ t, ‖testProd φ j k t‖) + ∫ t, ‖fderiv ℝ (testProd φ j k) t‖) with hS
  have hnn : ∀ j k, 0 ≤ (∫ t, ‖testProd φ j k t‖) + ∫ t, ‖fderiv ℝ (testProd φ j k) t‖ :=
    fun j k => add_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _)
  have hSle : ∀ j k, (∫ t, ‖testProd φ j k t‖) + ∫ t, ‖fderiv ℝ (testProd φ j k) t‖ ≤ S := by
    intro j k
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => ∑ k : Fin 3,
      ((∫ t, ‖testProd φ j k t‖) + ∫ t, ‖fderiv ℝ (testProd φ j k) t‖))
      (fun j _ => Finset.sum_nonneg fun k _ => hnn j k) (Finset.mem_univ j))
    exact Finset.single_le_sum (f := fun k =>
      ((∫ t, ‖testProd φ j k t‖) + ∫ t, ‖fderiv ℝ (testProd φ j k) t‖))
      (fun k _ => hnn j k) (Finset.mem_univ k)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hnn j k
  have hKb : ∀ i j k (y t : Space), t ∈ tsupport φ →
      |lerayKernel i j k τ (y - t)| ≤ C * A ^ 4 / (1 + ‖y‖) ^ 4 := fun i j k y t ht =>
    kernel_bound_on_ball hτ hR (fun x => hCb i j k τ x hτ) y t (hsuppR t ht)
  have hQ0 : ∀ y : Space, 0 ≤ C * A ^ 4 / (1 + ‖y‖) ^ 4 := fun y => by positivity
  have hcb : ∀ i j k y, |(testProd φ j k ⋆[mulRev, volume] lerayKernel i j k τ) y| ≤
      C * A ^ 4 / (1 + ‖y‖) ^ 4 * S := by
    intro i j k y
    rw [conv_mulRev_eq, ← Real.norm_eq_abs]
    have h := norm_integral_kernel_le (lerayKernel i j k τ) (testProd φ j k) y (tsupport φ)
      (C * A ^ 4 / (1 + ‖y‖) ^ 4) (hFint j k)
      (fun t ht => hFsupp j k (subset_tsupport _ ht)) (fun t ht => hKb i j k y t ht)
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (hQ0 y))
    have := hSle j k
    have : 0 ≤ ∫ t, ‖fderiv ℝ (testProd φ j k) t‖ := integral_nonneg fun _ => norm_nonneg _
    linarith
  have hDb : ∀ i j k y, ‖∫ t, lerayKernel i j k τ (y - t) • fderiv ℝ (testProd φ j k) t‖ ≤
      C * A ^ 4 / (1 + ‖y‖) ^ 4 * S := by
    intro i j k y
    have h := norm_integral_kernel_le (lerayKernel i j k τ) (fun t => fderiv ℝ (testProd φ j k) t)
      y (tsupport φ) (C * A ^ 4 / (1 + ‖y‖) ^ 4) (hFdint j k)
      (fun t ht => hFsupp j k (support_fderiv_subset ℝ ht)) (fun t ht => hKb i j k y t ht)
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (hQ0 y))
    have := hSle j k
    have : 0 ≤ ∫ t, ‖testProd φ j k t‖ := integral_nonneg fun _ => norm_nonneg _
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (ContDiff.sum fun i _ => (ContDiff.sum fun j _ => ContDiff.sum fun k _ =>
      hcs i j k).smul contDiff_const).neg
  · intro y
    unfold divergenceAt
    rw [(hfd y).fderiv]
    have hzero : ∀ j k, ∑ i, (∫ t, lerayKernel i j k τ (y - t) • fderiv ℝ (testProd φ j k) t)
        (unitVector i) = 0 := by
      intro j k
      have h1 : ∀ i, (∫ t, lerayKernel i j k τ (y - t) • fderiv ℝ (testProd φ j k) t)
          (unitVector i) =
          ∫ t, fderiv ℝ (lerayKernel i j k τ) (y - t) (unitVector i) * testProd φ j k t := by
        intro i
        rw [conv_deriv_apply (hF1 j k) (hFc j k) (hKc i j k) y (unitVector i)]
        exact integral_kernel_mul_deriv (hF1 j k) (hFc j k) (hKc1 i j k) y _
      simp_rw [h1]
      rw [← integral_finsetSum]
      · have h2 : ∀ t, ∑ i, fderiv ℝ (lerayKernel i j k τ) (y - t) (unitVector i) *
            testProd φ j k t = 0 := by
          intro t
          rw [← Finset.sum_mul, hDiv j k τ hτ (y - t), zero_mul]
        simp [h2]
      · intro i _
        exact integrable_kernel_smul (k := fun x => fderiv ℝ (lerayKernel i j k τ) x (unitVector i))
          (((hKc1 i j k).continuous_fderiv one_ne_zero).clm_apply continuous_const)
          (hFs j k).continuous (hFc j k) y
    have hcomp : ∀ i, ((-∑ l, (∑ j, ∑ k, ∫ t, lerayKernel l j k τ (y - t) •
        fderiv ℝ (testProd φ j k) t).smulRight (unitVector l)) (unitVector i)) i =
        -∑ j, ∑ k, (∫ t, lerayKernel i j k τ (y - t) • fderiv ℝ (testProd φ j k) t)
          (unitVector i) := by
      intro i
      rw [ContinuousLinearMap.neg_apply, PiLp.neg_apply, apply_sum_smulRight_unit]
      simp
    rw [Finset.sum_congr rfl fun i _ => hcomp i, Finset.sum_neg_distrib, neg_eq_zero,
      Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun k _ => hzero j k
  · refine ⟨27 * C * A ^ 4 * S, fun y => ⟨?_, ?_⟩⟩
    · rw [norm_neg]
      refine (norm_sum_smul_unit_le
        (fun i j k => (testProd φ j k ⋆[mulRev, volume] lerayKernel i j k τ) y) _
        (fun i j k => hcb i j k y)).trans ?_
      have h := div_four_le (27 * C * A ^ 4 * S) ‖y‖ (by positivity) (norm_nonneg y)
        (n := 1) (by norm_num)
      rw [pow_one] at h
      refine le_trans (le_of_eq ?_) h
      ring
    · rw [(hfd y).fderiv, norm_neg]
      refine (norm_sum_smulRight_unit_le
        (fun i j k => ∫ t, lerayKernel i j k τ (y - t) • fderiv ℝ (testProd φ j k) t) _
        (fun i j k => hDb i j k y)).trans ?_
      have h := div_four_le (27 * C * A ^ 4 * S) ‖y‖ (by positivity) (norm_nonneg y)
        (n := 2) (by norm_num)
      refine le_trans (le_of_eq ?_) h
      ring

end Breakdown.FarField
