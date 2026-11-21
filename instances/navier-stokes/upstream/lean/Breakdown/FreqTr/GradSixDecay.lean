import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.GradSixDecay


theorem opNorm_le_three_mul (A : Space →L[ℝ] Space) :
    ‖A‖ ≤ 3 * Real.sqrt (∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2) := by
  set s := Real.sqrt (∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2)
  have hi : ∀ i, ‖A (unitVector i)‖ ≤ s := fun i =>
    (le_abs_self _).trans (Real.abs_le_sqrt
      (Finset.single_le_sum (f := fun j => ‖A (unitVector j)‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)))
  refine A.opNorm_le_bound (by positivity) fun v => ?_
  have hv : v = ∑ i : Fin 3, v.ofLp i • unitVector i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
    simp [unitVector]
  rw [hv, map_sum]
  calc ‖∑ i : Fin 3, A (v.ofLp i • unitVector i)‖
      ≤ ∑ i : Fin 3, ‖A (v.ofLp i • unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * s := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [map_smul, norm_smul]
        exact mul_le_mul (PiLp.norm_apply_le v i) (hi i) (norm_nonneg _) (norm_nonneg _)
    _ = 3 * s * ‖∑ i : Fin 3, v.ofLp i • unitVector i‖ := by
        rw [← hv]; simp; ring

def unitBump : ContDiffBump (0 : Space) := ⟨1, 2, by norm_num, by norm_num⟩

def cutoff (R : ℝ) (y : Space) : ℝ := unitBump (R⁻¹ • y)

theorem cutoff_contDiff (R : ℝ) : ContDiff ℝ ∞ (cutoff R) :=
  unitBump.contDiff.comp (contDiff_id.const_smul R⁻¹)

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ ≤ R) : cutoff R y = 1 := by
  apply unitBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  show R⁻¹ * ‖y‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]; linarith

theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {y : Space} (hy : 2 * R ≤ ‖y‖) : cutoff R y = 0 := by
  apply unitBump.zero_of_le_dist
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  show 2 ≤ R⁻¹ * ‖y‖
  rw [le_inv_mul_iff₀ hR]; linarith

theorem cutoff_nonneg (R : ℝ) (y : Space) : 0 ≤ cutoff R y := unitBump.nonneg

theorem cutoff_le_one (R : ℝ) (y : Space) : cutoff R y ≤ 1 := unitBump.le_one

theorem exists_fderiv_cutoff_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ y : Space,
    ‖fderiv ℝ (cutoff R) y‖ ≤ K / R := by
  obtain ⟨K, hK⟩ := Continuous.bounded_above_of_compact_support
    ((unitBump.contDiff (n := 1)).continuous_fderiv one_ne_zero)
    (unitBump.hasCompactSupport.fderiv ℝ)
  refine ⟨K, (norm_nonneg _).trans (hK 0), fun R hR y => ?_⟩
  have h1 : HasFDerivAt (fun y : Space => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_smul R⁻¹
  have h2 : HasFDerivAt (unitBump : Space → ℝ) (fderiv ℝ unitBump (R⁻¹ • y)) (R⁻¹ • y) :=
    ((unitBump.contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt
  rw [show cutoff R = (unitBump : Space → ℝ) ∘ fun y => R⁻¹ • y from rfl, (h2.comp y h1).fderiv]
  have hn : ‖R⁻¹ • ContinuousLinearMap.id ℝ Space‖ ≤ R⁻¹ := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    exact mul_le_of_le_one_right (inv_nonneg.2 hR.le) ContinuousLinearMap.norm_id_le
  calc ‖(fderiv ℝ unitBump (R⁻¹ • y)).comp (R⁻¹ • ContinuousLinearMap.id ℝ Space)‖
      ≤ ‖fderiv ℝ unitBump (R⁻¹ • y)‖ * ‖R⁻¹ • ContinuousLinearMap.id ℝ Space‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K * R⁻¹ := mul_le_mul (hK _) hn (norm_nonneg _) ((norm_nonneg _).trans (hK 0))
    _ = K / R := (div_eq_mul_inv _ _).symm

theorem fderiv_cutoff_eq_zero_of_lt {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ < R) :
    fderiv ℝ (cutoff R) y = 0 := by
  have : cutoff R =ᶠ[nhds y] fun _ => (1 : ℝ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show y ∈ Metric.ball (0 : Space) R by simpa using hy)]
      with z hz
    exact cutoff_eq_one hR (mem_ball_zero_iff.1 hz).le
  rw [this.fderiv_eq]; simp

theorem fderiv_cutoff_eq_zero_of_gt {R : ℝ} (hR : 0 < R) {y : Space} (hy : 2 * R < ‖y‖) :
    fderiv ℝ (cutoff R) y = 0 := by
  have : cutoff R =ᶠ[nhds y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact cutoff_eq_zero hR (le_of_lt hz)
  rw [this.fderiv_eq]; simp

theorem one_add_norm_rpow_neg_natCast (y : Space) (k : ℕ) :
    (1 + ‖y‖) ^ (-(k : ℝ)) = ((1 + ‖y‖) ^ k)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem integrable_one_add_norm_rpow {r : ℝ} (hr : 3 < r) :
    Integrable (fun y : Space => (1 + ‖y‖) ^ (-r)) volume :=
  integrable_one_add_norm (by simpa [finrank_euclideanSpace_fin] using hr)

theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem integrable_sum_sq_fderiv {f : Space → Space} (hf : ContDiff ℝ ∞ f) {C : ℝ}
    (hC : ∀ y, ‖fderiv ℝ f y‖ ≤ C / (1 + ‖y‖) ^ 2) :
    Integrable (fun y => ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2) volume := by
  have hc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  refine integrable_finsetSum _ fun i _ => ?_
  refine Integrable.mono' ((integrable_one_add_norm_rpow (r := 4) (by norm_num)).const_mul (C ^ 2))
    ((hc.clm_apply continuous_const).norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ C / (1 + ‖y‖) ^ 2 := (norm_nonneg _).trans (hC y)
  have h1 : ‖fderiv ℝ f y (unitVector i)‖ ≤ C / (1 + ‖y‖) ^ 2 :=
    ((fderiv ℝ f y).le_opNorm _).trans (by rw [norm_unitVector, mul_one]; exact hC y)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, one_add_norm_rpow_neg_natCast]
  calc ‖fderiv ℝ f y (unitVector i)‖ ^ 2 ≤ (C / (1 + ‖y‖) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = C ^ 2 * ((1 + ‖y‖) ^ 4)⁻¹ := by rw [div_pow, ← pow_mul]; norm_num [div_eq_mul_inv]

theorem memLp_one_add_norm_rpow {a : ℝ} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ (⊤ : ℝ≥0∞))
    (h3 : 3 < a * p.toReal) : MemLp (fun y : Space => (1 + ‖y‖) ^ (-a)) p volume := by
  have hm : Continuous (fun y : Space => (1 + ‖y‖) ^ (-a)) :=
    (continuous_const.add continuous_norm).rpow_const fun y =>
      Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)))
  refine (integrable_norm_rpow_iff hm.aestronglyMeasurable hp0 hpt).1 ?_
  refine (integrable_one_add_norm_rpow h3).congr (Filter.Eventually.of_forall fun y => ?_)
  have hy0 : 0 ≤ 1 + ‖y‖ := add_nonneg zero_le_one (norm_nonneg y)
  simp only
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hy0 _), ← Real.rpow_mul hy0]
  ring_nf

theorem memLp_six_of_le {f : Space → Space} (hf : Continuous f) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C / (1 + ‖y‖)) : MemLp f 6 volume := by
  refine ((memLp_one_add_norm_rpow (a := 1) (by norm_num) (by norm_num)
    (by norm_num)).const_mul C).of_le hf.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine (hC y).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (mul_nonneg h0 (Real.rpow_nonneg (by positivity) _)), Real.rpow_neg_one,
    div_eq_mul_inv]

theorem norm_fderiv_cutoff_smul_le {f : Space → Space} (hf : ContDiff ℝ ∞ f) (R : ℝ) (y : Space) :
    ‖fderiv ℝ (cutoff R • f) y‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ (cutoff R) y‖ * ‖f y‖ := by
  rw [fderiv_smul ((cutoff_contDiff R).differentiable (by simp) y) (hf.differentiable (by simp) y)]
  refine (norm_add_le _ _).trans (add_le_add ?_ (le_of_eq (ContinuousLinearMap.norm_smulRight_apply _ _)))
  rw [norm_smul, Real.norm_of_nonneg (cutoff_nonneg R y)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one R y)

theorem cross_le_indicator {f : Space → Space} {C K R : ℝ} (hC0 : 0 ≤ C) (hK0 : 0 ≤ K) (hR : 0 < R)
    (hC : ∀ y, ‖f y‖ ≤ C / (1 + ‖y‖)) (hK : ∀ y, ‖fderiv ℝ (cutoff R) y‖ ≤ K / R) (y : Space) :
    ‖fderiv ℝ (cutoff R) y‖ * ‖f y‖ ≤
      (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => K * C / R ^ 2) y := by
  by_cases hy : y ∈ Metric.closedBall (0 : Space) (2 * R)
  · rw [indicator_of_mem hy]
    by_cases h' : ‖y‖ < R
    · rw [fderiv_cutoff_eq_zero_of_lt hR h']; simp only [norm_zero, zero_mul]; positivity
    · have hfy : ‖f y‖ ≤ C / R :=
        (hC y).trans (div_le_div_of_nonneg_left hC0 hR (by linarith [not_lt.1 h']))
      calc ‖fderiv ℝ (cutoff R) y‖ * ‖f y‖ ≤ (K / R) * (C / R) :=
            mul_le_mul (hK y) hfy (norm_nonneg _) (by positivity)
        _ = K * C / R ^ 2 := by ring
  · rw [indicator_of_notMem hy, fderiv_cutoff_eq_zero_of_gt hR
      (lt_of_not_ge fun h => hy (mem_closedBall_zero_iff.2 h))]
    simp

theorem eLpNorm_cutoff_smul_le {f : Space → Space} (hf : ContDiff ℝ ∞ f) {C K R : ℝ} (hC0 : 0 ≤ C)
    (hK0 : 0 ≤ K) (hR : 0 < R) (hC : ∀ y, ‖f y‖ ≤ C / (1 + ‖y‖))
    (hK : ∀ y, ‖fderiv ℝ (cutoff R) y‖ ≤ K / R) :
    eLpNorm (cutoff R • f) 6 volume ≤
      (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞) *
        (eLpNorm (fderiv ℝ f) 2 volume + ENNReal.ofReal (K * C / R ^ 2) *
          volume (Metric.closedBall (0 : Space) (2 * R)) ^ (1 / 2 : ℝ)) := by
  have hu : ContDiff ℝ 1 (cutoff R • f) :=
    (show ContDiff ℝ ∞ (fun y => cutoff R y • f y) from (cutoff_contDiff R).smul hf).of_le (by simp)
  have hs : HasCompactSupport (cutoff R • f) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * R)) fun x hx => by
      simp [cutoff_eq_zero hR (le_of_lt (lt_of_not_ge fun h => hx (mem_closedBall_zero_iff.2 h)))]
  have hg := eLpNorm_le_eLpNorm_fderiv_of_eq volume hu hs (p := 2) (p' := 6) (by norm_num)
    (by simp) (by simp; norm_num)
  have e6 : ((6 : NNReal) : ℝ≥0∞) = 6 := rfl
  have e2 : ((2 : NNReal) : ℝ≥0∞) = 2 := rfl
  rw [e6, e2] at hg
  refine hg.trans (mul_le_mul_right ?_ _)
  have hcd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hcc : Continuous (fun y => ‖fderiv ℝ (cutoff R) y‖ * ‖f y‖) :=
    ((cutoff_contDiff R).continuous_fderiv (by simp)).norm.mul hf.continuous.norm
  calc eLpNorm (fderiv ℝ (cutoff R • f)) 2 volume
      ≤ eLpNorm ((fun y => ‖fderiv ℝ f y‖) + fun y => ‖fderiv ℝ (cutoff R) y‖ * ‖f y‖) 2 volume :=
        eLpNorm_mono_real fun y => by
          simp only [Pi.add_apply]
          exact norm_fderiv_cutoff_smul_le hf R y
    _ ≤ eLpNorm (fun y => ‖fderiv ℝ f y‖) 2 volume +
          eLpNorm (fun y => ‖fderiv ℝ (cutoff R) y‖ * ‖f y‖) 2 volume :=
        eLpNorm_add_le hcd.norm.aestronglyMeasurable hcc.aestronglyMeasurable (by norm_num)
    _ ≤ eLpNorm (fderiv ℝ f) 2 volume + ENNReal.ofReal (K * C / R ^ 2) *
          volume (Metric.closedBall (0 : Space) (2 * R)) ^ (1 / 2 : ℝ) := by
        rw [eLpNorm_norm]
        refine add_le_add le_rfl ?_
        refine (eLpNorm_mono_real (g := (Metric.closedBall (0 : Space) (2 * R)).indicator
          (fun _ => K * C / R ^ 2)) fun y => ?_).trans (le_of_eq ?_)
        · rw [Real.norm_of_nonneg (by positivity)]
          exact cross_le_indicator hC0 hK0 hR hC hK y
        · rw [eLpNorm_indicator_const measurableSet_closedBall (by norm_num) (by norm_num),
            Real.enorm_of_nonneg (by positivity)]
          norm_num

theorem tendsto_cross_bound (K C : ℝ) :
    Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (K * C / (((n : ℝ) + 1) ^ 2) ^ 2) *
      volume (Metric.closedBall (0 : Space) (2 * ((n : ℝ) + 1) ^ 2)) ^ (1 / 2 : ℝ))
      Filter.atTop (nhds 0) := by
  set V := volume (Metric.ball (0 : Space) 1)
  have hV : V ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  have heq : (fun n : ℕ => ENNReal.ofReal (K * C / (((n : ℝ) + 1) ^ 2) ^ 2) *
      volume (Metric.closedBall (0 : Space) (2 * ((n : ℝ) + 1) ^ 2)) ^ (1 / 2 : ℝ)) =
      fun n : ℕ => ENNReal.ofReal (K * C * Real.sqrt 8 / ((n : ℝ) + 1)) * V ^ (1 / 2 : ℝ) := by
    funext n
    have hm : 0 < (n : ℝ) + 1 := by positivity
    rw [Measure.addHaar_closedBall volume 0 (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← mul_assoc,
      ← ENNReal.ofReal_mul' (by positivity)]
    congr 2
    rw [finrank_euclideanSpace_fin, ← Real.sqrt_eq_rpow,
      show (2 * ((n : ℝ) + 1) ^ 2) ^ 3 = 8 * (((n : ℝ) + 1) ^ 3) ^ 2 by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    field_simp
  rw [heq]
  have h1 : Filter.Tendsto (fun n : ℕ => K * C * Real.sqrt 8 / ((n : ℝ) + 1)) Filter.atTop
      (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hV)

theorem eLpNorm_fderiv_le {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (hS : Integrable (fun y => ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2) volume) :
    eLpNorm (fderiv ℝ f) 2 volume ≤
      ENNReal.ofReal (3 * Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2)) := by
  set S := fun y => ∑ i : Fin 3, ‖fderiv ℝ f y (unitVector i)‖ ^ 2 with hSdef
  have hS0 : ∀ y, 0 ≤ S y := fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc : Continuous (fun y => 3 * Real.sqrt (S y)) :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2))
  have hpow : ∀ y, ‖3 * Real.sqrt (S y)‖ ^ (2 : ℝ≥0∞).toReal = 9 * S y := by
    intro y
    rw [Real.norm_of_nonneg (by positivity)]
    norm_num [mul_pow, Real.sq_sqrt (hS0 y)]
  have hm : MemLp (fun y => 3 * Real.sqrt (S y)) 2 volume :=
    (integrable_norm_rpow_iff hc.aestronglyMeasurable (by norm_num) (by norm_num)).1
      ((hS.const_mul 9).congr (Filter.Eventually.of_forall fun y => (hpow y).symm))
  refine (eLpNorm_mono_real fun y => opNorm_le_three_mul (fderiv ℝ f y)).trans (le_of_eq ?_)
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp_rw [hpow]
  rw [integral_const_mul]
  congr 1
  rw [show ((2 : ℝ≥0∞).toReal)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by norm_num), show Real.sqrt 9 = 3 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

theorem eLpNorm_six_le {f : Space → Space} (hf : ContDiff ℝ ∞ f) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C / (1 + ‖y‖) ∧ ‖fderiv ℝ f y‖ ≤ C / (1 + ‖y‖) ^ 2) :
    eLpNorm f 6 volume ≤
      (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume := by
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0).1
  obtain ⟨K, hK0, hK⟩ := exists_fderiv_cutoff_le
  have hR : ∀ n : ℕ, 0 < ((n : ℝ) + 1) ^ 2 := fun n => by positivity
  have hlim := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 6) (μ := volume)
    (f := fun n : ℕ => cutoff (((n : ℝ) + 1) ^ 2) • f)
    (fun n => ((cutoff_contDiff _).continuous.smul hf.continuous).aestronglyMeasurable) f
    (Filter.Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      show cutoff _ x • f x = f x
      rw [cutoff_eq_one (hR n) (by nlinarith), one_smul])
  refine hlim.trans ?_
  have hT := ENNReal.Tendsto.const_mul
    (tendsto_const_nhds (x := eLpNorm (fderiv ℝ f) 2 volume) |>.add (tendsto_cross_bound K C))
    (Or.inr ENNReal.coe_ne_top)
    (a := (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞))
  rw [add_zero] at hT
  rw [← hT.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n =>
    eLpNorm_cutoff_smul_le hf hC0 hK0 (hR n) (fun y => (hC y).1) (hK _ (hR n)))

end Internal.GradSixDecay

theorem gradSixDecay :
    GradSixDecay := by
  refine ⟨(SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ) * 3,
    fun f hf => ?_⟩
  obtain ⟨hfs, -, C, hC⟩ := hf
  refine ⟨Internal.GradSixDecay.memLp_six_of_le hfs.continuous fun y => (hC y).1, ?_⟩
  have hS := Internal.GradSixDecay.integrable_sum_sq_fderiv hfs fun y => (hC y).2
  have h1 := (Internal.GradSixDecay.eLpNorm_six_le hfs hC).trans
    (mul_le_mul_right (Internal.GradSixDecay.eLpNorm_fderiv_le hfs hS) _)
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) h1
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity)] at h2
  linarith [h2]

end Breakdown.Freq
