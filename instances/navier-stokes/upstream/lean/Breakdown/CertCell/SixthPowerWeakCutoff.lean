import Breakdown.CertCell.SixthPowerStatements

open MeasureTheory Metric Set Filter Topology

noncomputable section

namespace Breakdown

private lemma norm_add_sq_le_weighted {E : Type*} [SeminormedAddCommGroup E] (a b : E) {δ : ℝ}
    (hδ : 0 < δ) : ‖a + b‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + δ⁻¹) * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : 0 ≤ ‖a + b‖ := norm_nonneg _
  have key : δ⁻¹ * (δ * ‖a‖ - ‖b‖) ^ 2 = δ * ‖a‖ ^ 2 + δ⁻¹ * ‖b‖ ^ 2 - 2 * ‖a‖ * ‖b‖ := by
    field_simp
    ring
  have h3 : 0 ≤ δ⁻¹ * (δ * ‖a‖ - ‖b‖) ^ 2 := mul_nonneg (inv_nonneg.2 hδ.le) (sq_nonneg _)
  have h4 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ h2 h1 2
  nlinarith

private lemma le_add_cube_div_sq {u a : ℝ} (hu : 0 ≤ u) (ha : 0 < a) : u ≤ a + u ^ 3 / a ^ 2 := by
  rcases le_or_gt u a with h | h
  · have : 0 ≤ u ^ 3 / a ^ 2 := by positivity
    linarith
  · have h2 : u ≤ u ^ 3 / a ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h3 : a ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ ha.le h.le 2
      have h4 := mul_le_mul_of_nonneg_left h3 hu
      nlinarith
    linarith

private lemma le_cube_of_rpow_third_le {x c : ℝ} (hx : 0 ≤ x) (h : x ^ ((1 : ℝ) / 3) ≤ c) :
    x ≤ c ^ 3 := by
  have h0 : 0 ≤ x ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hx _
  have h1 : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  calc x = (x ^ ((1 : ℝ) / 3)) ^ 3 := h1.symm
    _ ≤ c ^ 3 := pow_le_pow_left₀ h0 h 3

private lemma norm_unitVector_eq_one (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private lemma continuous_matSq : Continuous matSq := by
  unfold matSq
  exact continuous_finsetSum _ (fun i _ =>
    ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.norm.pow 2))

private def unitBump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

private def cutoff (R : ℝ) (y : Space) : ℝ := unitBump (R⁻¹ • y)

private lemma cutoff_contDiff (R : ℝ) : ContDiff ℝ 1 (cutoff R) :=
  (unitBump.contDiff (n := 1)).comp (contDiff_id.const_smul R⁻¹)

private lemma cutoff_nonneg (R : ℝ) (y : Space) : 0 ≤ cutoff R y := unitBump.nonneg

private lemma cutoff_le_one (R : ℝ) (y : Space) : cutoff R y ≤ 1 := unitBump.le_one

private lemma cutoff_eq_one {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ ≤ R) : cutoff R y = 1 := by
  apply unitBump.one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  show R⁻¹ * ‖y‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]
  linarith

private lemma cutoff_eq_zero {R : ℝ} (hR : 0 < R) {y : Space} (hy : 2 * R ≤ ‖y‖) :
    cutoff R y = 0 := by
  unfold cutoff
  rw [← Function.notMem_support, unitBump.support_eq, mem_ball_zero_iff, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  show ¬ R⁻¹ * ‖y‖ < 2
  rw [inv_mul_lt_iff₀ hR]
  linarith

private lemma fderiv_cutoff (R : ℝ) (y : Space) :
    fderiv ℝ (cutoff R) y =
      (fderiv ℝ unitBump (R⁻¹ • y)).comp (R⁻¹ • ContinuousLinearMap.id ℝ Space) := by
  have hb : DifferentiableAt ℝ unitBump (R⁻¹ • y) :=
    (unitBump.contDiff (n := 1)).differentiable one_ne_zero _
  exact (hb.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul R⁻¹)).fderiv

private lemma exists_fderiv_unitBump_bound : ∃ M, ∀ x, ‖fderiv ℝ unitBump x‖ ≤ M :=
  ((unitBump.contDiff (n := 1)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (unitBump.hasCompactSupport.fderiv ℝ)

private lemma norm_fderiv_cutoff_le {R M : ℝ} (hR : 0 < R)
    (hM : ∀ x, ‖fderiv ℝ unitBump x‖ ≤ M) (y : Space) : ‖fderiv ℝ (cutoff R) y‖ ≤ M / R := by
  rw [fderiv_cutoff]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hR.le)
  intro v
  rw [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
  calc ‖fderiv ℝ unitBump (R⁻¹ • y) (R⁻¹ • v)‖
        ≤ ‖fderiv ℝ unitBump (R⁻¹ • y)‖ * ‖R⁻¹ • v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * (R⁻¹ * ‖v‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
        exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
    _ = M / R * ‖v‖ := by ring

private lemma fderiv_cutoff_eq_zero_of_lt {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ < R) :
    fderiv ℝ (cutoff R) y = 0 := by
  have h : cutoff R =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)] with z hz
    exact cutoff_eq_one hR (mem_ball_zero_iff.1 hz).le
  rw [h.fderiv_eq, fderiv_const_apply]

private lemma fderiv_cutoff_eq_zero_of_gt {R : ℝ} (hR : 0 < R) {y : Space} (hy : 2 * R < ‖y‖) :
    fderiv ℝ (cutoff R) y = 0 := by
  have h : cutoff R =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact cutoff_eq_zero hR (le_of_lt hz)
  rw [h.fderiv_eq, fderiv_const_apply]

private lemma cutoff_smul_hasCompactSupport {R : ℝ} (hR : 0 < R) (W : Space → Space) :
    HasCompactSupport (fun y => cutoff R y • W y) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * R)) (fun y hy => ?_)
  rw [mem_closedBall_zero_iff, not_le] at hy
  rw [cutoff_eq_zero hR hy.le, zero_smul]

private lemma matSq_fderiv_cutoff_smul_le {R δ : ℝ} (hδ : 0 < δ) {W : Space → Space}
    (hW : ContDiff ℝ 1 W) (y : Space) :
    matSq (fderiv ℝ (fun z => cutoff R z • W z) y) ≤
      (1 + δ) * matSq (fderiv ℝ W y) +
        (1 + δ⁻¹) * (3 * (‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2)) := by
  rw [fderiv_fun_smul ((cutoff_contDiff R).differentiable one_ne_zero y)
    (hW.differentiable one_ne_zero y)]
  have key : ∀ i : Fin 3,
      ‖(cutoff R y • fderiv ℝ W y + (fderiv ℝ (cutoff R) y).smulRight (W y)) (unitVector i)‖ ^ 2 ≤
        (1 + δ) * ‖fderiv ℝ W y (unitVector i)‖ ^ 2 +
          (1 + δ⁻¹) * (‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2) := by
    intro i
    have he := norm_unitVector_eq_one i
    have hc0 := cutoff_nonneg R y
    have hc1 := cutoff_le_one R y
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    refine (norm_add_sq_le_weighted _ _ hδ).trans ?_
    have h1 : ‖cutoff R y • fderiv ℝ W y (unitVector i)‖ ^ 2 ≤
        ‖fderiv ℝ W y (unitVector i)‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
      exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left (norm_nonneg _) hc1) 2
    have h2 : ‖fderiv ℝ (cutoff R) y (unitVector i) • W y‖ ^ 2 ≤
        ‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2 := by
      rw [norm_smul, mul_pow]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (by positivity)
      calc ‖fderiv ℝ (cutoff R) y (unitVector i)‖
          ≤ ‖fderiv ℝ (cutoff R) y‖ * ‖unitVector i‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (cutoff R) y‖ := by rw [he, mul_one]
    have hd1 : 0 ≤ 1 + δ := by linarith
    have hd2 : 0 ≤ 1 + δ⁻¹ := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hd1) (mul_le_mul_of_nonneg_left h2 hd2)
  simp only [matSq, Fin.sum_univ_three]
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  linarith

private lemma integral_fderiv_cutoff_sq_mul_le {R M s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hM : ∀ x, ‖fderiv ℝ unitBump x‖ ≤ M) {W : Space → Space} (hW : ContDiff ℝ 1 W)
    (h6 : Integrable (fun y => ‖W y‖ ^ 6)) :
    Integrable (fun y => ‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2) ∧
    ∫ y, ‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2 ≤
      M ^ 2 * (8 * volume.real (ball (0 : Space) 1) * s +
        (∫ y in (ball (0 : Space) R)ᶜ, ‖W y‖ ^ 6) / s ^ 2) := by
  have ha : 0 < s / R := div_pos hs hR
  have hB : MeasurableSet (closedBall (0 : Space) (2 * R)) := measurableSet_closedBall
  have hO : MeasurableSet (ball (0 : Space) R)ᶜ := measurableSet_ball.compl
  have hIB : Integrable ((closedBall (0 : Space) (2 * R)).indicator (1 : Space → ℝ)) := by
    have : IntegrableOn (fun _ : Space => (1 : ℝ)) (closedBall (0 : Space) (2 * R)) :=
      integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne
    exact (integrable_indicator_iff hB).2 this
  have hIO : Integrable ((ball (0 : Space) R)ᶜ.indicator (fun y => ‖W y‖ ^ 6)) := h6.indicator hO
  have hI := (hIB.const_mul ((M / R) ^ 2 * (s / R))).add (hIO.const_mul ((M / R) ^ 2 / (s / R) ^ 2))
  have hdom : ∀ y, ‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2 ≤
      (M / R) ^ 2 * (s / R) * (closedBall (0 : Space) (2 * R)).indicator 1 y +
        (M / R) ^ 2 / (s / R) ^ 2 * (ball (0 : Space) R)ᶜ.indicator (fun y => ‖W y‖ ^ 6) y := by
    intro y
    have hIB0 : 0 ≤ (closedBall (0 : Space) (2 * R)).indicator (1 : Space → ℝ) y :=
      indicator_nonneg (fun _ _ => zero_le_one) y
    have hIO0 : 0 ≤ (ball (0 : Space) R)ᶜ.indicator (fun y => ‖W y‖ ^ 6) y :=
      indicator_nonneg (fun _ _ => by positivity) y
    have hrhs : 0 ≤ (M / R) ^ 2 * (s / R) * (closedBall (0 : Space) (2 * R)).indicator 1 y +
        (M / R) ^ 2 / (s / R) ^ 2 * (ball (0 : Space) R)ᶜ.indicator (fun y => ‖W y‖ ^ 6) y := by
      positivity
    by_cases h1 : ‖y‖ < R
    · rw [fderiv_cutoff_eq_zero_of_lt hR h1]
      simpa using hrhs
    by_cases h2 : 2 * R < ‖y‖
    · rw [fderiv_cutoff_eq_zero_of_gt hR h2]
      simpa using hrhs
    have hyB : y ∈ closedBall (0 : Space) (2 * R) := mem_closedBall_zero_iff.2 (not_lt.1 h2)
    have hyO : y ∈ (ball (0 : Space) R)ᶜ := fun hy => h1 (mem_ball_zero_iff.1 hy)
    rw [indicator_of_mem hyB, indicator_of_mem hyO, Pi.one_apply, mul_one]
    have hD2 : ‖fderiv ℝ (cutoff R) y‖ ^ 2 ≤ (M / R) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_cutoff_le hR hM y) 2
    have hi := le_add_cube_div_sq (sq_nonneg ‖W y‖) ha
    have h6' : (‖W y‖ ^ 2) ^ 3 = ‖W y‖ ^ 6 := by ring
    rw [h6'] at hi
    calc ‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2 ≤ (M / R) ^ 2 * ‖W y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hD2 (by positivity)
      _ ≤ (M / R) ^ 2 * (s / R + ‖W y‖ ^ 6 / (s / R) ^ 2) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
      _ = (M / R) ^ 2 * (s / R) + (M / R) ^ 2 / (s / R) ^ 2 * ‖W y‖ ^ 6 := by ring
  have hcont : Continuous (fun y => ‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2) :=
    (((cutoff_contDiff R).continuous_fderiv one_ne_zero).norm.pow 2).mul
      (hW.continuous.norm.pow 2)
  have hg : Integrable (fun y => ‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2) := by
    refine Integrable.mono' hI hcont.aestronglyMeasurable (Eventually.of_forall (fun y => ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    exact hdom y
  refine ⟨hg, ?_⟩
  calc ∫ y, ‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2
      ≤ ∫ y, ((M / R) ^ 2 * (s / R) * (closedBall (0 : Space) (2 * R)).indicator 1 y +
        (M / R) ^ 2 / (s / R) ^ 2 * (ball (0 : Space) R)ᶜ.indicator (fun y => ‖W y‖ ^ 6) y) :=
        integral_mono hg hI hdom
    _ = (M / R) ^ 2 * (s / R) * volume.real (closedBall (0 : Space) (2 * R)) +
        (M / R) ^ 2 / (s / R) ^ 2 * ∫ y in (ball (0 : Space) R)ᶜ, ‖W y‖ ^ 6 := by
        rw [integral_add (hIB.const_mul _) (hIO.const_mul _), integral_const_mul,
          integral_const_mul, integral_indicator_one hB, integral_indicator hO]
    _ = _ := by
        rw [Measure.addHaar_real_closedBall volume (0 : Space) (by positivity : (0 : ℝ) ≤ 2 * R),
          finrank_euclideanSpace_fin]
        field_simp
        ring

private lemma setIntegral_ball_le {C R δ s M : ℝ} (hC : 0 ≤ C) (h : SmoothSixthPowerBound C)
    (hR : 0 < R) (hδ : 0 < δ) (hs : 0 < s) (hM : ∀ x, ‖fderiv ℝ unitBump x‖ ≤ M)
    {W : Space → Space} (hW : ContDiff ℝ 1 W) (h6 : Integrable (fun y => ‖W y‖ ^ 6))
    (h2 : Integrable (fun y => matSq (fderiv ℝ W y))) :
    ∫ y in ball (0 : Space) R, ‖W y‖ ^ 6 ≤
      (C * ((1 + δ) * (∫ y, matSq (fderiv ℝ W y)) +
        (1 + δ⁻¹) * (3 * (M ^ 2 * (8 * volume.real (ball (0 : Space) 1) * s +
          (∫ y in (ball (0 : Space) R)ᶜ, ‖W y‖ ^ 6) / s ^ 2))))) ^ 3 := by
  have hv : ContDiff ℝ 1 (fun y => cutoff R y • W y) := (cutoff_contDiff R).smul hW
  have hvc : HasCompactSupport (fun y => cutoff R y • W y) := cutoff_smul_hasCompactSupport hR W
  have hDv : Continuous (fderiv ℝ (fun y => cutoff R y • W y)) := hv.continuous_fderiv one_ne_zero
  have hfv : Integrable (fun y => matSq (fderiv ℝ (fun z => cutoff R z • W z) y)) := by
    refine Continuous.integrable_of_hasCompactSupport (continuous_matSq.comp hDv) ?_
    refine (hvc.fderiv ℝ).mono (fun y hy => ?_)
    rw [Function.mem_support] at hy ⊢
    intro h0
    apply hy
    simp only [h0, matSq, zero_apply, norm_zero]
    norm_num
  have hnv : Integrable (fun y => ‖cutoff R y • W y‖ ^ 6) := by
    refine (hv.continuous.norm.pow 6).integrable_of_hasCompactSupport (hvc.mono (fun y hy => ?_))
    rw [Function.mem_support] at hy ⊢
    intro h0
    apply hy
    simp [Pi.pow_apply, h0]
  obtain ⟨hg, hgle⟩ := integral_fderiv_cutoff_sq_mul_le hR hs hM hW h6
  have hrhs := (h2.const_mul (1 + δ)).add ((hg.const_mul 3).const_mul (1 + δ⁻¹))
  have hF : ∫ y, matSq (fderiv ℝ (fun z => cutoff R z • W z) y) ≤
      (1 + δ) * (∫ y, matSq (fderiv ℝ W y)) +
        (1 + δ⁻¹) * (3 * (M ^ 2 * (8 * volume.real (ball (0 : Space) 1) * s +
          (∫ y in (ball (0 : Space) R)ᶜ, ‖W y‖ ^ 6) / s ^ 2))) := by
    calc ∫ y, matSq (fderiv ℝ (fun z => cutoff R z • W z) y)
        ≤ ∫ y, ((1 + δ) * matSq (fderiv ℝ W y) +
          (1 + δ⁻¹) * (3 * (‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2))) :=
          integral_mono hfv hrhs (fun y => matSq_fderiv_cutoff_smul_le hδ hW y)
      _ = (1 + δ) * (∫ y, matSq (fderiv ℝ W y)) +
          (1 + δ⁻¹) * (3 * ∫ y, ‖fderiv ℝ (cutoff R) y‖ ^ 2 * ‖W y‖ ^ 2) := by
          rw [integral_add (h2.const_mul _) ((hg.const_mul 3).const_mul _), integral_const_mul,
            integral_const_mul, integral_const_mul]
      _ ≤ _ := by gcongr
  have hsm := h _ hv hvc
  have hv6 : ∫ y, ‖cutoff R y • W y‖ ^ 6 ≤
      (C * ∫ y, matSq (fderiv ℝ (fun z => cutoff R z • W z) y)) ^ 3 :=
    le_cube_of_rpow_third_le (integral_nonneg (fun y => by positivity)) hsm
  have hball : ∫ y in ball (0 : Space) R, ‖W y‖ ^ 6 ≤ ∫ y, ‖cutoff R y • W y‖ ^ 6 := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_mono (h6.indicator measurableSet_ball) hnv (fun y => ?_)
    by_cases hy : y ∈ ball (0 : Space) R
    · rw [indicator_of_mem hy]
      dsimp only
      rw [cutoff_eq_one hR (mem_ball_zero_iff.1 hy).le, one_smul]
    · rw [indicator_of_notMem hy]
      positivity
  have h0 : 0 ≤ ∫ y, matSq (fderiv ℝ (fun z => cutoff R z • W z) y) :=
    integral_nonneg (fun y => by unfold matSq; positivity)
  calc ∫ y in ball (0 : Space) R, ‖W y‖ ^ 6 ≤ ∫ y, ‖cutoff R y • W y‖ ^ 6 := hball
    _ ≤ (C * ∫ y, matSq (fderiv ℝ (fun z => cutoff R z • W z) y)) ^ 3 := hv6
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hC h0) (mul_le_mul_of_nonneg_left hF hC) 3

theorem sixthPower_le_of_contDiff_integrable {C : ℝ} (hC : 0 ≤ C) (h : SmoothSixthPowerBound C)
    (W : Space → Space) (hW : ContDiff ℝ 1 W) (h6 : Integrable (fun y => ‖W y‖ ^ 6))
    (h2 : Integrable (fun y => matSq (fderiv ℝ W y))) :
    ∫ y, ‖W y‖ ^ 6 ≤ (C * ∫ y, matSq (fderiv ℝ W y)) ^ 3 := by
  obtain ⟨M, hM⟩ := exists_fderiv_unitBump_bound
  have hunion : (⋃ n : ℕ, ball (0 : Space) ((n : ℝ) + 1)) = univ := by
    refine eq_univ_of_forall (fun y => mem_iUnion.2 ?_)
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    exact ⟨n, mem_ball_zero_iff.2 (by linarith)⟩
  have hA : Tendsto (fun n : ℕ => ∫ y in ball (0 : Space) ((n : ℝ) + 1), ‖W y‖ ^ 6) atTop
      (𝓝 (∫ y, ‖W y‖ ^ 6)) := by
    have := tendsto_setIntegral_of_monotone (μ := volume) (f := fun y => ‖W y‖ ^ 6)
      (s := fun n : ℕ => ball (0 : Space) ((n : ℝ) + 1)) (fun n => measurableSet_ball)
      (fun m n hmn => ball_subset_ball (by gcongr)) h6.integrableOn
    rwa [hunion, Measure.restrict_univ] at this
  have hT : Tendsto (fun n : ℕ => ∫ y in (ball (0 : Space) ((n : ℝ) + 1))ᶜ, ‖W y‖ ^ 6) atTop
      (𝓝 0) := by
    have hsub := (tendsto_const_nhds (f := atTop) (x := ∫ y, ‖W y‖ ^ 6)).sub hA
    rw [sub_self] at hsub
    refine hsub.congr (fun n => ?_)
    have := integral_add_compl (μ := volume) (f := fun y => ‖W y‖ ^ 6)
      (measurableSet_ball (x := (0 : Space)) (ε := (n : ℝ) + 1)) h6
    linarith
  have hstep : ∀ δ s : ℝ, 0 < δ → 0 < s →
      ∫ y, ‖W y‖ ^ 6 ≤ (C * ((1 + δ) * (∫ y, matSq (fderiv ℝ W y)) +
        (1 + δ⁻¹) * (3 * (M ^ 2 * (8 * volume.real (ball (0 : Space) 1) * s + 0 / s ^ 2))))) ^ 3 := by
    intro δ s hδ hs
    have hcont : Continuous (fun t : ℝ => (C * ((1 + δ) * (∫ y, matSq (fderiv ℝ W y)) +
        (1 + δ⁻¹) * (3 * (M ^ 2 * (8 * volume.real (ball (0 : Space) 1) * s + t / s ^ 2))))) ^ 3) := by
      fun_prop
    exact le_of_tendsto_of_tendsto' hA ((hcont.tendsto 0).comp hT)
      (fun n => setIntegral_ball_le hC h (by positivity) hδ hs hM hW h6 h2)
  have hδstep : ∀ δ : ℝ, 0 < δ → ∫ y, ‖W y‖ ^ 6 ≤
      (C * ((1 + δ) * (∫ y, matSq (fderiv ℝ W y)) +
        24 * M ^ 2 * volume.real (ball (0 : Space) 1) * (δ ^ 2 + δ))) ^ 3 := by
    intro δ hδ
    have hb := hstep δ (δ ^ 2) hδ (by positivity)
    have he : (1 + δ⁻¹) * (3 * (M ^ 2 * (8 * volume.real (ball (0 : Space) 1) * δ ^ 2 +
        0 / (δ ^ 2) ^ 2))) = 24 * M ^ 2 * volume.real (ball (0 : Space) 1) * (δ ^ 2 + δ) := by
      field_simp
      ring
    rwa [he] at hb
  have hc : Continuous (fun δ : ℝ => (C * ((1 + δ) * (∫ y, matSq (fderiv ℝ W y)) +
      24 * M ^ 2 * volume.real (ball (0 : Space) 1) * (δ ^ 2 + δ))) ^ 3) := by
    fun_prop
  have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hval : (C * ((1 + 0) * (∫ y, matSq (fderiv ℝ W y)) +
      24 * M ^ 2 * volume.real (ball (0 : Space) 1) * ((0 : ℝ) ^ 2 + 0))) ^ 3 =
      (C * ∫ y, matSq (fderiv ℝ W y)) ^ 3 := by
    ring
  rw [hval] at hlim
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall (fun δ hδ => hδstep δ hδ))

end Breakdown
