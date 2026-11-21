import Breakdown.Cert.Statement
import Breakdown.Cert.SupBoundTestField
import Breakdown.FreqTr.GradSixDecay

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal.SliceSupNormSmooth

open Breakdown.Freq.Internal.EmbedNegSsp Breakdown.Freq.Internal.GradSixDecay

theorem colSq_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

def columns (A : Space →L[ℝ] Space) : PiLp 2 (fun _ : Fin 3 => Space) :=
  WithLp.toLp 2 fun i => A (unitVector i)

theorem sqrt_colSq_eq (A : Space →L[ℝ] Space) : Real.sqrt (matSq A) = ‖columns A‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (columns A)), PiLp.norm_sq_eq_of_L2]
  rfl

theorem columns_add (A B : Space →L[ℝ] Space) : columns (A + B) = columns A + columns B := by
  rw [columns, columns, columns, ← WithLp.toLp_add]
  rfl

theorem sqrt_colSq_add_le (A B : Space →L[ℝ] Space) :
    Real.sqrt (matSq (A + B)) ≤ Real.sqrt (matSq A) + Real.sqrt (matSq B) := by
  rw [sqrt_colSq_eq, sqrt_colSq_eq, sqrt_colSq_eq, columns_add]
  exact norm_add_le _ _

theorem sqrt_colSq_smul (c : ℝ) (A : Space →L[ℝ] Space) :
    Real.sqrt (matSq (c • A)) = |c| * Real.sqrt (matSq A) := by
  have h : matSq (c • A) = c ^ 2 * matSq A := by
    simp only [matSq, smul_apply, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, Finset.mul_sum]
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem sqrt_colSq_smulRight_le (L : Space →L[ℝ] ℝ) (v : Space) :
    Real.sqrt (matSq (L.smulRight v)) ≤ 2 * (‖L‖ * ‖v‖) := by
  have hi : ∀ i : Fin 3, ‖(L.smulRight v) (unitVector i)‖ ^ 2 ≤ (‖L‖ * ‖v‖) ^ 2 := by
    intro i
    rw [ContinuousLinearMap.smulRight_apply, norm_smul]
    refine pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) 2
    simpa [norm_unitVector] using L.le_opNorm (unitVector i)
  have h : matSq (L.smulRight v) ≤ (2 * (‖L‖ * ‖v‖)) ^ 2 := by
    calc matSq (L.smulRight v) ≤ ∑ _i : Fin 3, (‖L‖ * ‖v‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => hi i
      _ = 3 * (‖L‖ * ‖v‖) ^ 2 := by simp
      _ ≤ (2 * (‖L‖ * ‖v‖)) ^ 2 := by nlinarith [sq_nonneg (‖L‖ * ‖v‖)]
  calc Real.sqrt (matSq (L.smulRight v)) ≤ Real.sqrt ((2 * (‖L‖ * ‖v‖)) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = 2 * (‖L‖ * ‖v‖) := Real.sqrt_sq (by positivity)

theorem norm_apply_le_sqrt_colSq (A : Space →L[ℝ] Space) (i : Fin 3) :
    ‖A (unitVector i)‖ ≤ Real.sqrt (matSq A) :=
  (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun j => ‖A (unitVector j)‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)))

theorem continuous_colSq : Continuous matSq :=
  continuous_finsetSum _ fun _ _ => ((continuous_id.clm_apply continuous_const).norm.pow 2)

theorem continuous_traceSecond {f : Space → Space} (hf : ContDiff ℝ ∞ f) :
    Continuous (sumSecondPartialsAt f) := by
  have e : sumSecondPartialsAt f = fun y => ∑ i : Fin 3, pd (pd f i) i y := funext (sumSecondPartialsAt_eq hf)
  rw [e]
  exact continuous_finsetSum _ fun i _ => (contDiff_pd (contDiff_pd hf i) i).continuous

theorem pd_smul_eq {a : Space → ℝ} {f : Space → Space} (ha : Differentiable ℝ a)
    (hf : Differentiable ℝ f) (i : Fin 3) :
    pd (fun y => a y • f y) i = fun y => a y • pd f i y + pd a i y • f y := by
  funext y
  simp only [pd]
  rw [fderiv_fun_smul (ha y) (hf y)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]

theorem pd_add_eq {f g : Space → Space} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) : pd (fun y => f y + g y) i = fun y => pd f i y + pd g i y := by
  funext y
  simp only [pd]
  rw [fderiv_fun_add (hf y) (hg y)]
  rfl

theorem traceSecond_smul_eq {a : Space → ℝ} {f : Space → Space} (ha : ContDiff ℝ ∞ a)
    (hf : ContDiff ℝ ∞ f) (y : Space) :
    sumSecondPartialsAt (fun z => a z • f z) y =
      a y • sumSecondPartialsAt f y + (2 : ℝ) • ∑ i : Fin 3, pd a i y • pd f i y +
        (∑ i : Fin 3, pd (pd a i) i y) • f y := by
  have da := differentiable_of_smooth ha
  have df := differentiable_of_smooth hf
  rw [sumSecondPartialsAt_eq (f := fun z => a z • f z) (ha.smul hf), sumSecondPartialsAt_eq hf]
  have key : ∀ i : Fin 3, pd (pd (fun z => a z • f z) i) i y =
      a y • pd (pd f i) i y + (2 : ℝ) • (pd a i y • pd f i y) + pd (pd a i) i y • f y := by
    intro i
    have dai := differentiable_of_smooth (contDiff_pd ha i)
    have dfi := differentiable_of_smooth (contDiff_pd hf i)
    rw [pd_smul_eq da df, pd_add_eq (f := fun z => a z • pd f i z) (g := fun z => pd a i z • f z)
      (da.smul dfi) (dai.smul df), pd_smul_eq da dfi,
      pd_smul_eq dai df]
    simp only [two_smul]
    abel
  simp only [key, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul]

theorem pd_scaled {g : Space → ℝ} (hg : Differentiable ℝ g) (k c : ℝ) (i : Fin 3) :
    pd (fun y => k * g (c • y)) i = fun y => k * c * pd g i (c • y) := by
  funext y
  have hl : HasFDerivAt (fun y : Space => c • y) (c • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_smul c
  have h : HasFDerivAt (fun y => k * g (c • y))
      (k • ((fderiv ℝ g (c • y)).comp (c • ContinuousLinearMap.id ℝ Space))) y :=
    ((hg (c • y)).hasFDerivAt.comp y hl).const_mul k
  simp only [pd]
  rw [h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

theorem cutoff_second_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ y : Space,
    |∑ i : Fin 3, pd (pd (cutoff R) i) i y| ≤ K / R ^ 2 := by
  have hb : ContDiff ℝ ∞ (unitBump : Space → ℝ) := unitBump.contDiff
  have hbd : Differentiable ℝ (unitBump : Space → ℝ) := differentiable_of_smooth hb
  have hc : ∀ i : Fin 3, ∃ C, ∀ z, ‖pd (pd (unitBump : Space → ℝ) i) i z‖ ≤ C := fun i =>
    (contDiff_pd (contDiff_pd hb i) i).continuous.bounded_above_of_compact_support
      (hasCompactSupport_pd (hasCompactSupport_pd unitBump.hasCompactSupport i) i)
  choose C hC using hc
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => (norm_nonneg _).trans (hC i 0),
    fun R hR y => ?_⟩
  have e0 : cutoff R = fun z => 1 * (unitBump : Space → ℝ) (R⁻¹ • z) := by
    funext z
    simp [cutoff]
  have e : ∀ i : Fin 3, pd (pd (cutoff R) i) i y =
      R⁻¹ * R⁻¹ * pd (pd (unitBump : Space → ℝ) i) i (R⁻¹ • y) := by
    intro i
    rw [e0, pd_scaled hbd,
      pd_scaled (g := pd (unitBump : Space → ℝ) i) (differentiable_of_smooth (contDiff_pd hb i))]
    ring
  simp only [e]
  calc |∑ i : Fin 3, R⁻¹ * R⁻¹ * pd (pd (unitBump : Space → ℝ) i) i (R⁻¹ • y)|
      ≤ ∑ i : Fin 3, |R⁻¹ * R⁻¹ * pd (pd (unitBump : Space → ℝ) i) i (R⁻¹ • y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, R⁻¹ * R⁻¹ * C i := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < R⁻¹ * R⁻¹)]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hC i (R⁻¹ • y))
          (by positivity)
    _ = (∑ i, C i) / R ^ 2 := by
        rw [← Finset.mul_sum]
        field_simp

theorem pd_pd_zero_of_eventuallyEq {a : Space → ℝ} {z : Space} {c : ℝ}
    (h : a =ᶠ[𝓝 z] fun _ => c) (i j : Fin 3) : pd (pd a i) j z = 0 := by
  have h1 : pd a i =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [h.eventually_nhds] with y hy
    show fderiv ℝ a y (unitVector i) = 0
    rw [Filter.EventuallyEq.fderiv_eq (show a =ᶠ[𝓝 y] fun _ => c from hy)]
    simp
  show fderiv ℝ (pd a i) z (unitVector j) = 0
  rw [h1.fderiv_eq]
  simp

theorem cutoff_second_zero_of_lt {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ < R) :
    ∑ i : Fin 3, pd (pd (cutoff R) i) i y = 0 := by
  have hc : cutoff R =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (show y ∈ Metric.ball (0 : Space) R by simpa using hy)] with z hz
    exact cutoff_eq_one hR (mem_ball_zero_iff.1 hz).le
  exact Finset.sum_eq_zero fun i _ => pd_pd_zero_of_eventuallyEq hc i i

theorem cutoff_second_zero_of_gt {R : ℝ} (hR : 0 < R) {y : Space} (hy : 2 * R < ‖y‖) :
    ∑ i : Fin 3, pd (pd (cutoff R) i) i y = 0 := by
  have hc : cutoff R =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact cutoff_eq_zero hR hz.le
  exact Finset.sum_eq_zero fun i _ => pd_pd_zero_of_eventuallyEq hc i i

theorem eLpNorm_two_eq_sqrt {E : Type*} [NormedAddCommGroup E] {F : Space → E}
    (hF : MemLp F 2 volume) :
    eLpNorm F 2 volume = ENNReal.ofReal (Real.sqrt (∫ y, ‖F y‖ ^ 2)) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, Real.sqrt_eq_rpow]
  simp

theorem annulus_bound {f : Space → Space} (hf : Continuous f) {a : Space → ℝ} {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R) (hb : ∀ y, |a y| ≤ M)
    (hs : ∀ y, a y ≠ 0 → R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R) :
    eLpNorm (fun y => a y * ‖f y‖) 2 volume ≤
      ENNReal.ofReal (M * (2 * R)) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) *
        eLpNorm ({y : Space | R ≤ ‖y‖}.indicator f) 6 volume := by
  set B := Metric.closedBall (0 : Space) (2 * R) with hB
  set T := {y : Space | R ≤ ‖y‖}.indicator f with hT
  have hTm : AEStronglyMeasurable T volume :=
    hf.aestronglyMeasurable.indicator (measurableSet_le measurable_const measurable_norm)
  have hpt : ∀ y, ‖a y * ‖f y‖‖ ≤ B.indicator (fun z => M * ‖T z‖) y := by
    intro y
    by_cases h0 : a y = 0
    · rw [h0, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun z _ => by positivity) y
    · obtain ⟨h1, h2⟩ := hs y h0
      have hyB : y ∈ B := by simpa [hB] using h2
      have hTy : T y = f y := Set.indicator_of_mem (show y ∈ {y : Space | R ≤ ‖y‖} from h1) f
      rw [Set.indicator_of_mem hyB, hTy, norm_mul, Real.norm_eq_abs, norm_norm]
      exact mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _)
  have hvol : volume B ^ (1 / 3 : ℝ) =
      ENNReal.ofReal (2 * R) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) := by
    rw [hB, Measure.addHaar_closedBall volume 0 (by positivity), finrank_euclideanSpace_fin,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hsm : AEStronglyMeasurable (fun z => M * ‖T z‖) (volume.restrict B) :=
    (hTm.norm.const_mul M).restrict
  have hexp : 1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal = (1 / 3 : ℝ) := by norm_num
  calc eLpNorm (fun y => a y * ‖f y‖) 2 volume
      ≤ eLpNorm (B.indicator fun z => M * ‖T z‖) 2 volume := eLpNorm_mono_real hpt
    _ = eLpNorm (fun z => M * ‖T z‖) 2 (volume.restrict B) :=
        eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall
    _ ≤ eLpNorm (fun z => M * ‖T z‖) 6 (volume.restrict B) *
          (volume.restrict B) Set.univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hsm
    _ ≤ eLpNorm (fun z => M * ‖T z‖) 6 volume * volume B ^ (1 / 3 : ℝ) := by
        rw [Measure.restrict_apply_univ, hexp]
        gcongr
        exact Measure.restrict_le_self
    _ = ENNReal.ofReal M * eLpNorm T 6 volume *
          (ENNReal.ofReal (2 * R) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ)) := by
        rw [show (fun z => M * ‖T z‖) = M • fun z => ‖T z‖ from rfl, eLpNorm_const_smul,
          eLpNorm_norm, Real.enorm_of_nonneg hM, hvol]
    _ = _ := by
        rw [ENNReal.ofReal_mul hM]
        ring

theorem tail_tendsto {f : Space → Space} (hc : Continuous f) (hf : MemLp f 6 volume) :
    Tendsto (fun R : ℝ => eLpNorm ({y : Space | R ≤ ‖y‖}.indicator f) 6 volume) atTop (𝓝 0) := by
  have h6 : (6 : ℝ≥0∞) ≠ 0 := by norm_num
  have h6t : (6 : ℝ≥0∞) ≠ ⊤ := by norm_num
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h6 h6t]
  have hfin : ∫⁻ y, ‖f y‖ₑ ^ (6 : ℝ≥0∞).toReal ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h6 h6t hf.eLpNorm_lt_top).ne
  have hlim : Tendsto (fun R : ℝ => ∫⁻ y, ‖({y : Space | R ≤ ‖y‖}.indicator f) y‖ₑ ^
      (6 : ℝ≥0∞).toReal) atTop (𝓝 (∫⁻ _ : Space, 0)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun y => ‖f y‖ₑ ^ (6 : ℝ≥0∞).toReal)
      (Eventually.of_forall fun R => ?_) (Eventually.of_forall fun R => ae_of_all _ fun y => ?_)
      hfin (ae_of_all _ fun y => ?_)
    · exact (hc.measurable.indicator (measurableSet_le measurable_const measurable_norm)).enorm.pow_const _
    · exact ENNReal.rpow_le_rpow (enorm_indicator_le_enorm_self _ _) (by positivity)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop ‖y‖] with R hR
      have hy : y ∉ {y : Space | R ≤ ‖y‖} := by simpa using hR
      rw [Set.indicator_of_notMem hy, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [lintegral_zero] at hlim
  have hp := (ENNReal.continuous_rpow_const (y := 1 / (6 : ℝ≥0∞).toReal)).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hp
  exact hp.comp hlim

theorem grad_cut_bound {u : Space → Space} (hu : ContDiff ℝ ∞ u) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ R : ℝ, 0 < R → ∀ y : Space, ‖fderiv ℝ (cutoff R) y‖ ≤ K / R) {R : ℝ} (hR : 0 < R) :
    eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ (fun z => cutoff R z • u z) y))) 2 volume ≤
      eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ u y))) 2 volume +
        ENNReal.ofReal (4 * K) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) *
          eLpNorm ({y : Space | R ≤ ‖y‖}.indicator u) 6 volume := by
  have hχ : ContDiff ℝ ∞ (cutoff R) := cutoff_contDiff R
  have hp : Continuous fun y => Real.sqrt (matSq (fderiv ℝ u y)) :=
    Real.continuous_sqrt.comp (continuous_colSq.comp (hu.continuous_fderiv (by simp)))
  have hq : Continuous fun y => 2 * ‖fderiv ℝ (cutoff R) y‖ * ‖u y‖ :=
    (continuous_const.mul (hχ.continuous_fderiv (by simp)).norm).mul hu.continuous.norm
  have hpt : ∀ y, ‖Real.sqrt (matSq (fderiv ℝ (fun z => cutoff R z • u z) y))‖ ≤
      Real.sqrt (matSq (fderiv ℝ u y)) + 2 * ‖fderiv ℝ (cutoff R) y‖ * ‖u y‖ := by
    intro y
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
      fderiv_fun_smul ((differentiable_of_smooth hχ) y) ((differentiable_of_smooth hu) y)]
    refine (sqrt_colSq_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [sqrt_colSq_smul, abs_of_nonneg (cutoff_nonneg R y)]
      exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (cutoff_le_one R y)
    · exact (sqrt_colSq_smulRight_le _ _).trans (le_of_eq (by ring))
  have hann := annulus_bound hu.continuous (a := fun y => 2 * ‖fderiv ℝ (cutoff R) y‖)
    (M := 2 * K / R) (by positivity) hR
    (fun y => by
      rw [abs_of_nonneg (by positivity)]
      have h := hK R hR y
      calc 2 * ‖fderiv ℝ (cutoff R) y‖ ≤ 2 * (K / R) := by linarith
        _ = 2 * K / R := by ring)
    (fun y hy => by
      refine ⟨le_of_not_gt fun h => hy ?_, le_of_not_gt fun h => hy ?_⟩
      · simp [fderiv_cutoff_eq_zero_of_lt hR h]
      · simp [fderiv_cutoff_eq_zero_of_gt hR h])
  have e : 2 * K / R * (2 * R) = 4 * K := by
    rw [div_mul_eq_mul_div, div_eq_iff hR.ne']
    ring
  rw [e] at hann
  calc _ ≤ eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ u y)) +
          2 * ‖fderiv ℝ (cutoff R) y‖ * ‖u y‖) 2 volume := eLpNorm_mono_real hpt
    _ ≤ eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ u y))) 2 volume +
          eLpNorm (fun y => 2 * ‖fderiv ℝ (cutoff R) y‖ * ‖u y‖) 2 volume :=
        eLpNorm_add_le (f := fun y => Real.sqrt (matSq (fderiv ℝ u y)))
          (g := fun y => 2 * ‖fderiv ℝ (cutoff R) y‖ * ‖u y‖)
          hp.aestronglyMeasurable hq.aestronglyMeasurable (by norm_num)
    _ ≤ _ := add_le_add le_rfl hann

theorem traceSecond_cut_bound {u : Space → Space} (hu : ContDiff ℝ ∞ u) {K₁ K₂ : ℝ} (hK₁0 : 0 ≤ K₁)
    (hK₁ : ∀ R : ℝ, 0 < R → ∀ y : Space, ‖fderiv ℝ (cutoff R) y‖ ≤ K₁ / R) (hK₂0 : 0 ≤ K₂)
    (hK₂ : ∀ R : ℝ, 0 < R → ∀ y : Space, |∑ i : Fin 3, pd (pd (cutoff R) i) i y| ≤ K₂ / R ^ 2)
    {R : ℝ} (hR : 1 ≤ R) :
    eLpNorm (fun y => ‖sumSecondPartialsAt (fun z => cutoff R z • u z) y‖) 2 volume ≤
      eLpNorm (fun y => ‖sumSecondPartialsAt u y‖) 2 volume +
        ENNReal.ofReal (6 * K₁ / R) *
          eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ u y))) 2 volume +
        ENNReal.ofReal (2 * K₂) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) *
          eLpNorm ({y : Space | R ≤ ‖y‖}.indicator u) 6 volume := by
  have hR0 : 0 < R := by linarith
  have hχ : ContDiff ℝ ∞ (cutoff R) := cutoff_contDiff R
  have hp : Continuous fun y => Real.sqrt (matSq (fderiv ℝ u y)) :=
    Real.continuous_sqrt.comp (continuous_colSq.comp (hu.continuous_fderiv (by simp)))
  have hl : Continuous fun y => ‖sumSecondPartialsAt u y‖ := (continuous_traceSecond hu).norm
  have hs : Continuous fun y => ∑ i : Fin 3, pd (pd (cutoff R) i) i y :=
    continuous_finsetSum _ fun i _ => (contDiff_pd (contDiff_pd hχ i) i).continuous
  have hr : Continuous fun y => |∑ i : Fin 3, pd (pd (cutoff R) i) i y| * ‖u y‖ :=
    hs.abs.mul hu.continuous.norm
  have hpt : ∀ y, ‖‖sumSecondPartialsAt (fun z => cutoff R z • u z) y‖‖ ≤
      ‖sumSecondPartialsAt u y‖ + 6 * K₁ / R * Real.sqrt (matSq (fderiv ℝ u y)) +
        |∑ i : Fin 3, pd (pd (cutoff R) i) i y| * ‖u y‖ := by
    intro y
    rw [norm_norm, traceSecond_smul_eq hχ hu y]
    have h1 : ‖cutoff R y • sumSecondPartialsAt u y‖ ≤ ‖sumSecondPartialsAt u y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (cutoff_nonneg R y)]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one R y)
    have hi : ∀ i : Fin 3, ‖pd (cutoff R) i y • pd u i y‖ ≤
        K₁ / R * Real.sqrt (matSq (fderiv ℝ u y)) := by
      intro i
      rw [norm_smul]
      refine mul_le_mul ?_ (norm_apply_le_sqrt_colSq _ i) (norm_nonneg _) (by positivity)
      refine le_trans ?_ (hK₁ R hR0 y)
      simpa [norm_unitVector, pd] using (fderiv ℝ (cutoff R) y).le_opNorm (unitVector i)
    have h2 : ‖(2 : ℝ) • ∑ i : Fin 3, pd (cutoff R) i y • pd u i y‖ ≤
        6 * K₁ / R * Real.sqrt (matSq (fderiv ℝ u y)) := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc 2 * ‖∑ i : Fin 3, pd (cutoff R) i y • pd u i y‖
          ≤ 2 * ∑ _i : Fin 3, K₁ / R * Real.sqrt (matSq (fderiv ℝ u y)) :=
            mul_le_mul_of_nonneg_left
              ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hi i)) (by norm_num)
        _ = 6 * K₁ / R * Real.sqrt (matSq (fderiv ℝ u y)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have h3 : ‖(∑ i : Fin 3, pd (pd (cutoff R) i) i y) • u y‖ =
        |∑ i : Fin 3, pd (pd (cutoff R) i) i y| * ‖u y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    refine norm_add₃_le.trans ?_
    rw [h3]
    linarith
  have hrb := annulus_bound hu.continuous
    (a := fun y => |∑ i : Fin 3, pd (pd (cutoff R) i) i y|) (M := K₂ / R ^ 2) (by positivity) hR0
    (fun y => by rw [abs_abs]; exact hK₂ R hR0 y)
    (fun y hy => by
      refine ⟨le_of_not_gt fun h => hy ?_, le_of_not_gt fun h => hy ?_⟩
      · simp [cutoff_second_zero_of_lt hR0 h]
      · simp [cutoff_second_zero_of_gt hR0 h])
  have e : K₂ / R ^ 2 * (2 * R) ≤ 2 * K₂ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hK₂0 hR0.le) (sub_nonneg.2 hR)]
  have hrb' : eLpNorm (fun y => |∑ i : Fin 3, pd (pd (cutoff R) i) i y| * ‖u y‖) 2 volume ≤
      ENNReal.ofReal (2 * K₂) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) *
        eLpNorm ({y : Space | R ≤ ‖y‖}.indicator u) 6 volume :=
    hrb.trans (by gcongr)
  have hc : eLpNorm (fun y => 6 * K₁ / R * Real.sqrt (matSq (fderiv ℝ u y))) 2 volume =
      ENNReal.ofReal (6 * K₁ / R) *
        eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ u y))) 2 volume := by
    rw [show (fun y => 6 * K₁ / R * Real.sqrt (matSq (fderiv ℝ u y))) =
      (6 * K₁ / R) • fun y => Real.sqrt (matSq (fderiv ℝ u y)) from rfl, eLpNorm_const_smul,
      Real.enorm_of_nonneg (by positivity)]
  calc _ ≤ eLpNorm (fun y => ‖sumSecondPartialsAt u y‖ + 6 * K₁ / R * Real.sqrt (matSq (fderiv ℝ u y)) +
          |∑ i : Fin 3, pd (pd (cutoff R) i) i y| * ‖u y‖) 2 volume := eLpNorm_mono_real hpt
    _ ≤ eLpNorm (fun y => ‖sumSecondPartialsAt u y‖ +
          6 * K₁ / R * Real.sqrt (matSq (fderiv ℝ u y))) 2 volume +
          eLpNorm (fun y => |∑ i : Fin 3, pd (pd (cutoff R) i) i y| * ‖u y‖) 2 volume :=
        eLpNorm_add_le
          (f := fun y => ‖sumSecondPartialsAt u y‖ + 6 * K₁ / R * Real.sqrt (matSq (fderiv ℝ u y)))
          (g := fun y => |∑ i : Fin 3, pd (pd (cutoff R) i) i y| * ‖u y‖)
          (hl.add (continuous_const.mul hp)).aestronglyMeasurable hr.aestronglyMeasurable
          (by norm_num)
    _ ≤ eLpNorm (fun y => ‖sumSecondPartialsAt u y‖) 2 volume +
          eLpNorm (fun y => 6 * K₁ / R * Real.sqrt (matSq (fderiv ℝ u y))) 2 volume +
          eLpNorm (fun y => |∑ i : Fin 3, pd (pd (cutoff R) i) i y| * ‖u y‖) 2 volume :=
        add_le_add (eLpNorm_add_le (f := fun y => ‖sumSecondPartialsAt u y‖)
          (g := fun y => 6 * K₁ / R * Real.sqrt (matSq (fderiv ℝ u y)))
          hl.aestronglyMeasurable (continuous_const.mul hp).aestronglyMeasurable (by norm_num))
          le_rfl
    _ ≤ _ := by
        rw [hc]
        exact add_le_add le_rfl hrb'

end Internal.SliceSupNormSmooth

open Internal.SliceSupNormSmooth Breakdown.Freq.Internal.EmbedNegSsp
  Breakdown.Freq.Internal.GradSixDecay in
theorem smoothSupNormBound (u : Space → Space) (hu : ContDiff ℝ ∞ u) (h6 : MemLp u 6 volume)
    (hG : Integrable (fun y => matSq (fderiv ℝ u y)))
    (hL : Integrable (fun y => ‖sumSecondPartialsAt u y‖ ^ 2)) (x : Space) :
    ‖u x‖ ^ 2 ≤ (1 / (2 * Real.pi)) * Real.sqrt (∫ y, matSq (fderiv ℝ u y)) *
      Real.sqrt (∫ y, ‖sumSecondPartialsAt u y‖ ^ 2) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_fderiv_cutoff_le
  obtain ⟨K₂, hK₂0, hK₂⟩ := cutoff_second_bound
  have hp : Continuous fun y => Real.sqrt (matSq (fderiv ℝ u y)) :=
    Real.continuous_sqrt.comp (continuous_colSq.comp (hu.continuous_fderiv (by simp)))
  have hl : Continuous fun y => ‖sumSecondPartialsAt u y‖ := (continuous_traceSecond hu).norm
  have hpy : ∀ y, ‖Real.sqrt (matSq (fderiv ℝ u y))‖ ^ 2 = matSq (fderiv ℝ u y) := fun y => by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (colSq_nonneg _)]
  have hp2 : MemLp (fun y => Real.sqrt (matSq (fderiv ℝ u y))) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).2
      (hG.congr (ae_of_all _ fun y => (hpy y).symm))
  have hl2 : MemLp (fun y => ‖sumSecondPartialsAt u y‖) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).2
      (hL.congr (ae_of_all _ fun y => by simp only [norm_norm]))
  have hpE : eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ u y))) 2 volume =
      ENNReal.ofReal (Real.sqrt (∫ y, matSq (fderiv ℝ u y))) := by
    rw [eLpNorm_two_eq_sqrt hp2]
    simp only [hpy]
  have hlE : eLpNorm (fun y => ‖sumSecondPartialsAt u y‖) 2 volume =
      ENNReal.ofReal (Real.sqrt (∫ y, ‖sumSecondPartialsAt u y‖ ^ 2)) := by
    rw [eLpNorm_two_eq_sqrt hl2]
    simp only [norm_norm]
  set EP := eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ u y))) 2 volume with hEP
  set EL := eLpNorm (fun y => ‖sumSecondPartialsAt u y‖) 2 volume with hEL
  set V : ℝ≥0∞ := volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) with hV
  have hVt : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  set T : ℝ → ℝ≥0∞ := fun R => eLpNorm ({y : Space | R ≤ ‖y‖}.indicator u) 6 volume with hTdef
  have hT : Tendsto T atTop (𝓝 0) := tail_tendsto hu.continuous h6
  have hPt : EP ≠ ⊤ := hp2.eLpNorm_lt_top.ne
  have hLt : EL ≠ ⊤ := hl2.eLpNorm_lt_top.ne
  have hTt : ∀ R, T R ≠ ⊤ := fun R =>
    (lt_of_le_of_lt (eLpNorm_indicator_le _) h6.eLpNorm_lt_top).ne
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.pi)) with hc
  have step : ∀ R : ℝ, 1 ≤ R → ‖x‖ ≤ R → ENNReal.ofReal (‖u x‖ ^ 2) ≤
      c * (EP + ENNReal.ofReal (4 * K₁) * V * T R) *
        (EL + ENNReal.ofReal (6 * K₁ / R) * EP + ENNReal.ofReal (2 * K₂) * V * T R) := by
    intro R hR1 hxR
    have hR : 0 < R := by linarith
    have hχ : ContDiff ℝ ∞ (cutoff R) := cutoff_contDiff R
    have hw : ContDiff ℝ ∞ (fun z => cutoff R z • u z) := hχ.smul hu
    have hwc : HasCompactSupport (fun z => cutoff R z • u z) :=
      HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * R)) fun y hy => by
        have h2 : 2 * R ≤ ‖y‖ := le_of_lt (by simpa using hy)
        simp only [cutoff_eq_zero hR h2, zero_smul]
    have hsup := supBound_test_field (fun z => cutoff R z • u z) hw hwc x
    have hwx : cutoff R x • u x = u x := by rw [cutoff_eq_one hR hxR, one_smul]
    simp only [hwx] at hsup
    have hA : eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ (fun z => cutoff R z • u z) y)))
        2 volume ≤ EP + ENNReal.ofReal (4 * K₁) * V * T R := grad_cut_bound hu hK₁0 hK₁ hR
    have hB : eLpNorm (fun y => ‖sumSecondPartialsAt (fun z => cutoff R z • u z) y‖) 2 volume ≤
        EL + ENNReal.ofReal (6 * K₁ / R) * EP + ENNReal.ofReal (2 * K₂) * V * T R :=
      traceSecond_cut_bound hu hK₁0 hK₁ hK₂0 hK₂ hR1
    have hPw : Continuous fun y => Real.sqrt (matSq (fderiv ℝ (fun z => cutoff R z • u z) y)) :=
      Real.continuous_sqrt.comp (continuous_colSq.comp (hw.continuous_fderiv (by simp)))
    have hLw : Continuous fun y => ‖sumSecondPartialsAt (fun z => cutoff R z • u z) y‖ :=
      (continuous_traceSecond hw).norm
    have hD : ENNReal.ofReal (4 * K₁) * V * T R < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hVt.lt_top) (hTt R).lt_top
    have hD' : ENNReal.ofReal (2 * K₂) * V * T R < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hVt.lt_top) (hTt R).lt_top
    have hPw2 : MemLp (fun y => Real.sqrt (matSq (fderiv ℝ (fun z => cutoff R z • u z) y)))
        2 volume :=
      ⟨hPw.aestronglyMeasurable, lt_of_le_of_lt hA (ENNReal.add_lt_top.2 ⟨hPt.lt_top, hD⟩)⟩
    have hLw2 : MemLp (fun y => ‖sumSecondPartialsAt (fun z => cutoff R z • u z) y‖) 2 volume :=
      ⟨hLw.aestronglyMeasurable, lt_of_le_of_lt hB (ENNReal.add_lt_top.2
        ⟨ENNReal.add_lt_top.2 ⟨hLt.lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hPt.lt_top⟩,
          hD'⟩)⟩
    have ePw : eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ (fun z => cutoff R z • u z) y)))
        2 volume = ENNReal.ofReal (Real.sqrt (∫ y, ∑ i : Fin 3,
          ‖fderiv ℝ (fun z => cutoff R z • u z) y (unitVector i)‖ ^ 2)) := by
      rw [eLpNorm_two_eq_sqrt hPw2]
      simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (colSq_nonneg _)]
      rfl
    have eLw : eLpNorm (fun y => ‖sumSecondPartialsAt (fun z => cutoff R z • u z) y‖) 2 volume =
        ENNReal.ofReal (Real.sqrt (∫ y, ‖sumSecondPartialsAt (fun z => cutoff R z • u z) y‖ ^ 2)) := by
      rw [eLpNorm_two_eq_sqrt hLw2]
      simp only [norm_norm]
    calc ENNReal.ofReal (‖u x‖ ^ 2)
        ≤ ENNReal.ofReal ((1 / (2 * Real.pi)) * Real.sqrt (∫ y, ∑ i : Fin 3,
            ‖fderiv ℝ (fun z => cutoff R z • u z) y (unitVector i)‖ ^ 2) *
            Real.sqrt (∫ y, ‖sumSecondPartialsAt (fun z => cutoff R z • u z) y‖ ^ 2)) :=
          ENNReal.ofReal_le_ofReal hsup
      _ = c * eLpNorm (fun y => Real.sqrt (matSq (fderiv ℝ (fun z => cutoff R z • u z) y)))
            2 volume * eLpNorm (fun y => ‖sumSecondPartialsAt (fun z => cutoff R z • u z) y‖) 2 volume := by
          rw [ePw, eLw, hc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by gcongr
  have hlim : Tendsto (fun R : ℝ => c * (EP + ENNReal.ofReal (4 * K₁) * V * T R) *
      (EL + ENNReal.ofReal (6 * K₁ / R) * EP + ENNReal.ofReal (2 * K₂) * V * T R)) atTop
      (𝓝 (c * EP * EL)) := by
    have hD1 : Tendsto (fun R => ENNReal.ofReal (4 * K₁) * V * T R) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (4 * K₁) * V) hT
        (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt))
    have hD2 : Tendsto (fun R => ENNReal.ofReal (2 * K₂) * V * T R) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * K₂) * V) hT
        (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt))
    have hK : Tendsto (fun R : ℝ => ENNReal.ofReal (6 * K₁ / R)) atTop (𝓝 0) := by
      have h : Tendsto (fun R : ℝ => 6 * K₁ / R) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using ENNReal.tendsto_ofReal h
    have h1 : Tendsto (fun R => EP + ENNReal.ofReal (4 * K₁) * V * T R) atTop (𝓝 EP) := by
      simpa using (tendsto_const_nhds (x := EP)).add hD1
    have h2 : Tendsto (fun R => EL + ENNReal.ofReal (6 * K₁ / R) * EP +
        ENNReal.ofReal (2 * K₂) * V * T R) atTop (𝓝 EL) := by
      simpa using ((tendsto_const_nhds (x := EL)).add
        (ENNReal.Tendsto.mul_const hK (Or.inr hPt))).add hD2
    exact ENNReal.Tendsto.mul (ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top))
      (Or.inr hLt) h2 (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPt))
  have hfin : ENNReal.ofReal (‖u x‖ ^ 2) ≤ c * EP * EL := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (max 1 ‖x‖)] with R hR
    exact step R ((le_max_left _ _).trans hR) ((le_max_right _ _).trans hR)
  rw [hpE, hlE, hc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfin
  exact hfin

end CertReduction

end Breakdown
