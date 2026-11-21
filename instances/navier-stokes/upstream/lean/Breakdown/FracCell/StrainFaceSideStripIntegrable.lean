import Breakdown.FracCell.StrainFaceDefs
import Breakdown.FracCell.ModeHeightAxis

open scoped ContDiff ENNReal NNReal
open MeasureTheory Filter Topology
open scoped Convolution

noncomputable section

namespace Breakdown.SteadyCert.SideStripSixInternal

open Breakdown.Freq.Internal.GradSixDecay

private theorem normPow_conv_le_of_dom (φ : ContDiffBump (0 : Space)) (f : Space → Space)
    (E : Space → ℝ) (hE : Integrable E) (k : ℕ) (hk : 1 ≤ k) (hdom : ∀ z, ‖f z‖ ^ k ≤ E z)
    (y : Space) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ k ≤
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖f z‖ ^ k) y := by
  set ρ : Space → ℝ := φ.normed volume with hρ
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => φ.nonneg_normed t
  have hρc : Continuous ρ := φ.continuous_normed
  set d : Space → ℝ≥0 := fun t => (ρ t).toNNReal with hd
  have hdm : Measurable d := hρc.measurable.real_toNNReal
  set μ : Measure Space := volume.withDensity (fun t => (d t : ℝ≥0∞)) with hμ
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have h1 : ∫⁻ t, ENNReal.ofReal (ρ t) = ENNReal.ofReal (∫ t, ρ t) :=
      (ofReal_integral_eq_lintegral_ofReal φ.integrable_normed (ae_of_all _ hρ0)).symm
    have h2 : ∫ t, ρ t = 1 := φ.integral_normed
    rw [h2, ENNReal.ofReal_one] at h1
    exact h1
  have hint : ∀ g : Space → Space, ∫ t, g t ∂μ = ∫ t, ρ t • g t := by
    intro g
    rw [hμ, integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hd, NNReal.smul_def, Real.coe_toNNReal _ (hρ0 t)]
  have hintR : ∀ g : Space → ℝ, ∫ t, g t ∂μ = ∫ t, ρ t • g t := by
    intro g
    rw [hμ, integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hd, NNReal.smul_def, Real.coe_toNNReal _ (hρ0 t)]
  have hL : (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y = ∫ t, f (y - t) ∂μ := by
    rw [convolution_def, hint]
    rfl
  have hR : (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖f z‖ ^ k) y =
      ∫ t, ‖f (y - t)‖ ^ k ∂μ := by
    rw [convolution_def, hintR]
    rfl
  rw [hL, hR]
  by_cases hfi : Integrable (fun t => f (y - t)) μ
  · obtain ⟨C, hC⟩ := hρc.bounded_above_of_compact_support φ.hasCompactSupport_normed
    have hIt : Integrable (fun t => E (y - t)) := hE.comp_sub_left y
    have hEμ : Integrable (fun t => E (y - t)) μ := by
      rw [hμ, integrable_withDensity_iff_integrable_smul hdm]
      refine (hIt.const_mul C).mono' ?_ (ae_of_all _ fun t => ?_)
      · exact (hdm.coe_nnreal_real.aestronglyMeasurable).smul hIt.aestronglyMeasurable
      · have hE0 : 0 ≤ E (y - t) := (by positivity : (0 : ℝ) ≤ ‖f (y - t)‖ ^ k).trans (hdom _)
        simp only [hd, NNReal.smul_def, Real.coe_toNNReal _ (hρ0 t), smul_eq_mul, norm_mul,
          Real.norm_eq_abs, abs_of_nonneg (hρ0 t), abs_of_nonneg hE0]
        have h1 : ρ t ≤ C := by simpa [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)] using hC t
        exact mul_le_mul_of_nonneg_right h1 hE0
    have hgi : Integrable (fun t => ‖f (y - t)‖ ^ k) μ :=
      hEμ.mono' (hfi.aestronglyMeasurable.norm.pow k) (ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hdom _)
    have hconv : ConvexOn ℝ Set.univ (fun x : Space => ‖x‖ ^ k) :=
      (convexOn_norm convex_univ).pow (fun x _ => norm_nonneg x) k
    exact hconv.map_integral_le ((continuous_norm.pow k).continuousOn) isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) hfi hgi
  · rw [integral_undef hfi, norm_zero, zero_pow (by omega)]
    exact integral_nonneg fun t => by positivity

private theorem sum_integral_le {ι : Type*} (s : Finset ι) (h : ι → Space → ℝ) (B : Space → ℝ)
    (h0 : ∀ i z, 0 ≤ h i z) (hB : Integrable B) (hle : ∀ z, ∑ i ∈ s, h i z ≤ B z) :
    ∑ i ∈ s, ∫ z, h i z ≤ ∫ z, B z := by
  classical
  have e : ∑ i ∈ s, ∫ z, h i z = ∑ i ∈ s.filter (fun i => Integrable (h i)), ∫ z, h i z := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rfl
    · exact integral_undef hi
  rw [e, ← integral_finsetSum _ (fun i hi => (Finset.mem_filter.1 hi).2)]
  exact integral_mono (integrable_finsetSum _ fun i hi => (Finset.mem_filter.1 hi).2) hB fun z =>
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => h0 i z).trans
      (hle z)

private theorem conv_sum_le (φ : ContDiffBump (0 : Space)) (c : Fin 3 → Space → Space)
    (E : Space → ℝ) (hE : Integrable E) (hdom : ∀ z, ∑ j : Fin 3, ‖c j z‖ ^ 2 ≤ E z) (y : Space) :
    ∑ j : Fin 3, (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖c j z‖ ^ 2) y ≤
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] E) y := by
  have hex := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hE.locallyIntegrable y
  have hI : Integrable (fun t => φ.normed volume t * E (y - t)) := by
    simpa [ConvolutionExistsAt] using hex
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact sum_integral_le Finset.univ (fun j t => φ.normed volume t * ‖c j (y - t)‖ ^ 2) _
    (fun j t => mul_nonneg (φ.nonneg_normed t) (by positivity)) hI fun t => by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hdom _) (φ.nonneg_normed t)

private theorem mollify_fderiv_apply (φ : ContDiffBump (0 : Space)) (g : Space → Space)
    (c : Fin 3 → Space → Space) (hloc : LocallyIntegrable g volume)
    (hw : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∀ j : Fin 3,
      ∫ y, (fderiv ℝ ψ y (unitVector j)) • g y = -∫ y, ψ y • c j y) (y : Space) (j : Fin 3) :
    fderiv ℝ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y (unitVector j) =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] c j) y := by
  have hcf : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hcd : ContDiff ℝ ∞ (φ.normed volume) := φ.contDiff_normed
  have hd1 : ContDiff ℝ 1 (φ.normed volume) := hcd.of_le (by simp)
  have hder := hcf.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hd1 hloc y
  rw [hder.fderiv]
  have hex := (hcf.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).precompL Space)
    (hcd.continuous_fderiv (by simp)) hloc y
  rw [convolution_eq_swap, ContinuousLinearMap.integral_apply hex.integrable_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  set ψ : Space → ℝ := fun s => φ.normed volume (y - s) with hψ
  have hψt : IsTestScalar ψ := by
    refine ⟨hcd.comp (contDiff_const.sub contDiff_id), ?_⟩
    exact hcf.comp_homeomorph (Homeomorph.subLeft y)
  have hψd : ∀ s, fderiv ℝ ψ s (unitVector j) = -fderiv ℝ (φ.normed volume) (y - s) (unitVector j) := by
    intro s
    have h1 : HasFDerivAt (φ.normed volume) (fderiv ℝ (φ.normed volume) (y - s)) (y - s) :=
      ((hcd.differentiable (by simp)) (y - s)).hasFDerivAt
    have h2 : HasFDerivAt ψ ((fderiv ℝ (φ.normed volume) (y - s)).comp (-ContinuousLinearMap.id ℝ Space)) s :=
      h1.comp s ((hasFDerivAt_id s).const_sub y)
    rw [h2.fderiv]
    simp
  have hwj := hw ψ hψt j
  simp only [hψd, neg_smul, integral_neg] at hwj
  exact neg_injective hwj

private theorem memLp_six_iff {f : Space → Space} (hf : AEStronglyMeasurable f volume) :
    MemLp f 6 volume ↔ Integrable (fun y => ‖f y‖ ^ 6) := by
  rw [← integrable_norm_rpow_iff hf (by norm_num) (by norm_num)]
  have h : ((6 : ℝ≥0∞).toReal) = ((6 : ℕ) : ℝ) := by norm_num
  simp_rw [h, Real.rpow_natCast]

private theorem cross_tail_le {f : Space → Space} (hf : Continuous f) {K R : ℝ} (hK0 : 0 ≤ K)
    (hR : 0 < R) (hK : ∀ y, ‖fderiv ℝ (cutoff R) y‖ ≤ K / R) :
    eLpNorm (fun y => ‖fderiv ℝ (cutoff R) y‖ * ‖f y‖) 2 volume ≤
      ENNReal.ofReal (2 * K) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) *
        eLpNorm ({y : Space | R ≤ ‖y‖}.indicator f) 6 volume := by
  set B := Metric.closedBall (0 : Space) (2 * R) with hBdef
  set T := {y : Space | R ≤ ‖y‖}.indicator f with hTdef
  have hTm : AEStronglyMeasurable T volume :=
    hf.aestronglyMeasurable.indicator (measurableSet_le measurable_const continuous_norm.measurable)
  have hpt : ∀ y, ‖‖fderiv ℝ (cutoff R) y‖ * ‖f y‖‖ ≤ B.indicator ((K / R) • fun y => ‖T y‖) y := by
    intro y
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases h' : ‖y‖ < R
      · rw [fderiv_cutoff_eq_zero_of_lt hR h']
        simp only [norm_zero, zero_mul]
        positivity
      · have hT : T y = f y :=
          Set.indicator_of_mem (show y ∈ {y : Space | R ≤ ‖y‖} from not_lt.1 h') f
        rw [hT]
        exact mul_le_mul_of_nonneg_right (hK y) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy, fderiv_cutoff_eq_zero_of_gt hR
        (lt_of_not_ge fun h => hy (mem_closedBall_zero_iff.2 h))]
      simp
  refine (eLpNorm_mono_real hpt).trans ?_
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  have hsm : AEStronglyMeasurable ((K / R) • fun y => ‖T y‖) (volume.restrict B) :=
    (hTm.norm.const_smul _).restrict
  have hexp : (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) = (1 / 3 : ℝ) := by norm_num
  have hvol : volume B ^ (1 / 3 : ℝ) = ENNReal.ofReal (2 * R) *
      volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) := by
    rw [hBdef, Measure.addHaar_closedBall volume 0 (by positivity), finrank_euclideanSpace_fin,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  calc eLpNorm ((K / R) • fun y => ‖T y‖) 2 (volume.restrict B)
      ≤ eLpNorm ((K / R) • fun y => ‖T y‖) 6 (volume.restrict B) *
          (volume.restrict B) Set.univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hsm
    _ ≤ eLpNorm ((K / R) • fun y => ‖T y‖) 6 volume * volume B ^ (1 / 3 : ℝ) := by
        rw [Measure.restrict_apply_univ, hexp]
        gcongr
        exact Measure.restrict_le_self
    _ = ENNReal.ofReal (K / R) * eLpNorm T 6 volume *
          (ENNReal.ofReal (2 * R) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ)) := by
        rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_of_nonneg (by positivity), hvol]
    _ = ENNReal.ofReal (2 * K) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) *
          eLpNorm T 6 volume := by
        have h2 : ENNReal.ofReal (2 * K) = ENNReal.ofReal (K / R) * ENNReal.ofReal (2 * R) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
        rw [h2]
        ring

private theorem tail_tendsto {f : Space → Space} (hf : MemLp f 6 volume) :
    Tendsto (fun n : ℕ => eLpNorm ({y : Space | (n : ℝ) + 1 ≤ ‖y‖}.indicator f) 6 volume) atTop
      (𝓝 0) := by
  have h6 : (6 : ℝ≥0∞) ≠ 0 := by norm_num
  have h6t : (6 : ℝ≥0∞) ≠ ⊤ := by norm_num
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h6 h6t]
  have hfin : ∫⁻ y, ‖f y‖ₑ ^ (6 : ℝ≥0∞).toReal ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h6 h6t hf.eLpNorm_lt_top).ne
  have hlim : Tendsto (fun n : ℕ => ∫⁻ y, ‖({y : Space | (n : ℝ) + 1 ≤ ‖y‖}.indicator f) y‖ₑ ^
      (6 : ℝ≥0∞).toReal) atTop (𝓝 (∫⁻ _ : Space, 0)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun y => ‖f y‖ₑ ^ (6 : ℝ≥0∞).toReal)
      (fun n => ?_) (fun n => ae_of_all _ fun y => ?_) hfin (ae_of_all _ fun y => ?_)
    · exact ((hf.1.indicator (measurableSet_le measurable_const
        continuous_norm.measurable)).enorm.pow_const _)
    · dsimp only
      by_cases hy : y ∈ {y : Space | (n : ℝ) + 1 ≤ ‖y‖}
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
        exact zero_le
    · obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hy : y ∉ {y : Space | (n : ℝ) + 1 ≤ ‖y‖} := by
        simp only [Set.mem_ofPred_eq, not_le]
        linarith
      rw [Set.indicator_of_notMem hy, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [lintegral_zero] at hlim
  have hc := (ENNReal.continuous_rpow_const (y := 1 / (6 : ℝ≥0∞).toReal)).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
  exact hc.comp hlim

private theorem smooth_six_of_six {f : Space → Space} (hf : ContDiff ℝ ∞ f) (h6 : MemLp f 6 volume) :
    eLpNorm f 6 volume ≤
      (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume := by
  obtain ⟨K, hK0, hK⟩ := exists_fderiv_cutoff_le
  set D : ℝ≥0∞ := ENNReal.ofReal (2 * K) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) with hD
  have hDt : D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne)
  have hR : ∀ n : ℕ, 0 < (n : ℝ) + 1 := fun n => by positivity
  have hstep : ∀ n : ℕ, eLpNorm (cutoff ((n : ℝ) + 1) • f) 6 volume ≤
      (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞) *
        (eLpNorm (fderiv ℝ f) 2 volume +
          D * eLpNorm ({y : Space | (n : ℝ) + 1 ≤ ‖y‖}.indicator f) 6 volume) := by
    intro n
    have hu : ContDiff ℝ 1 (cutoff ((n : ℝ) + 1) • f) :=
      (show ContDiff ℝ ∞ (fun y => cutoff ((n : ℝ) + 1) y • f y) from
        (cutoff_contDiff _).smul hf).of_le (by simp)
    have hs : HasCompactSupport (cutoff ((n : ℝ) + 1) • f) :=
      HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * ((n : ℝ) + 1))) fun x hx => by
        simp [cutoff_eq_zero (hR n)
          (le_of_lt (lt_of_not_ge fun h => hx (mem_closedBall_zero_iff.2 h)))]
    have hg := eLpNorm_le_eLpNorm_fderiv_of_eq volume hu hs (p := 2) (p' := 6) (by norm_num)
      (by simp) (by simp; norm_num)
    have e6 : ((6 : NNReal) : ℝ≥0∞) = 6 := rfl
    have e2 : ((2 : NNReal) : ℝ≥0∞) = 2 := rfl
    rw [e6, e2] at hg
    refine hg.trans (mul_le_mul_right ?_ _)
    have hcd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
    have hcc : Continuous (fun y => ‖fderiv ℝ (cutoff ((n : ℝ) + 1)) y‖ * ‖f y‖) :=
      ((cutoff_contDiff _).continuous_fderiv (by simp)).norm.mul hf.continuous.norm
    calc eLpNorm (fderiv ℝ (cutoff ((n : ℝ) + 1) • f)) 2 volume
        ≤ eLpNorm ((fun y => ‖fderiv ℝ f y‖) +
            fun y => ‖fderiv ℝ (cutoff ((n : ℝ) + 1)) y‖ * ‖f y‖) 2 volume :=
          eLpNorm_mono_real fun y => by
            simp only [Pi.add_apply]
            exact norm_fderiv_cutoff_smul_le hf _ y
      _ ≤ eLpNorm (fun y => ‖fderiv ℝ f y‖) 2 volume +
            eLpNorm (fun y => ‖fderiv ℝ (cutoff ((n : ℝ) + 1)) y‖ * ‖f y‖) 2 volume :=
          eLpNorm_add_le hcd.norm.aestronglyMeasurable hcc.aestronglyMeasurable (by norm_num)
      _ ≤ _ := by
          rw [eLpNorm_norm]
          exact add_le_add le_rfl (cross_tail_le hf.continuous hK0 (hR n) (hK _ (hR n)))
  have hlim := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 6) (μ := volume)
    (f := fun n : ℕ => cutoff ((n : ℝ) + 1) • f)
    (fun n => ((cutoff_contDiff _).continuous.smul hf.continuous).aestronglyMeasurable) f
    (Filter.Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      show cutoff _ x • f x = f x
      rw [cutoff_eq_one (hR n) (by linarith), one_smul])
  refine hlim.trans ?_
  have h0 : Tendsto (fun n : ℕ => D * eLpNorm ({y : Space | (n : ℝ) + 1 ≤ ‖y‖}.indicator f) 6 volume)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (tail_tendsto h6) (Or.inr hDt)
  have hT := ENNReal.Tendsto.const_mul
    (tendsto_const_nhds (x := eLpNorm (fderiv ℝ f) 2 volume) |>.add h0)
    (Or.inr ENNReal.coe_ne_top)
    (a := (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞))
  rw [add_zero] at hT
  rw [← hT.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hstep)


private theorem six_bound_of_compact (g : Space → Space) (c : Fin 3 → Space → Space) (E : Space → ℝ)
    (hg2 : MemLp g 2 volume) (hgc : HasCompactSupport g) (hE : Integrable E)
    (hdom : ∀ z, ∑ j : Fin 3, ‖c j z‖ ^ 2 ≤ E z)
    (hw : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∀ j : Fin 3,
      ∫ y, (fderiv ℝ ψ y (unitVector j)) • g y = -∫ y, ψ y • c j y) :
    eLpNorm g 6 volume ≤
      (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞) *
        ENNReal.ofReal (3 * Real.sqrt (∫ y, E y)) := by
  have hloc : LocallyIntegrable g volume := hg2.locallyIntegrable (by norm_num)
  have hcE : ∀ j z, ‖c j z‖ ^ 2 ≤ E z := fun j z =>
    (Finset.single_le_sum (f := fun i => ‖c i z‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ j)).trans (hdom z)
  let φ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]
      linarith⟩
  have hρi : ∀ n, Integrable ((φ n).normed volume) := fun n => (φ n).integrable_normed
  have hwc : ∀ n, ContDiff ℝ ∞ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
    fun n => ((φ n).hasCompactSupport_normed).contDiff_convolution_left _ (φ n).contDiff_normed hloc
  have hw6 : ∀ n, MemLp ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 6 volume :=
    fun n => (hwc n).continuous.memLp_of_hasCompactSupport
      (((φ n).hasCompactSupport_normed).convolution _ hgc)
  have hEpt : ∀ n y, ∑ i : Fin 3,
      ‖fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y (unitVector i)‖ ^ 2 ≤
      ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] E) y := by
    intro n y
    simp only [mollify_fderiv_apply (φ n) g c hloc hw y]
    exact (Finset.sum_le_sum fun j _ =>
      normPow_conv_le_of_dom (φ n) (c j) E hE 2 (by norm_num) (hcE j) y).trans
        (conv_sum_le (φ n) c E hE hdom y)
  have hSi : ∀ n, Integrable ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] E) :=
    fun n => (hρi n).integrable_convolution _ hE
  have hEc : ∀ n, Continuous (fun y => ∑ i : Fin 3,
      ‖fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y (unitVector i)‖ ^ 2) := by
    intro n
    exact continuous_finsetSum _ fun i _ =>
      ((((hwc n).continuous_fderiv (by simp)).clm_apply continuous_const).norm).pow 2
  have hEi : ∀ n, Integrable (fun y => ∑ i : Fin 3,
      ‖fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y (unitVector i)‖ ^ 2) :=
    fun n => (hSi n).mono' (hEc n).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
      exact hEpt n y)
  have hEle : ∀ n, ∫ y, ∑ i : Fin 3,
      ‖fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y (unitVector i)‖ ^ 2 ≤
      ∫ y, E y := by
    intro n
    refine (integral_mono (hEi n) (hSi n) (hEpt n)).trans_eq ?_
    rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hρi n) hE]
    simp [ContDiffBump.integral_normed]
  set S := (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞)
    with hSdef
  set B := S * ENNReal.ofReal (3 * Real.sqrt (∫ y, E y)) with hB
  have hbound : ∀ n, eLpNorm ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 6 volume ≤ B :=
    fun n => (smooth_six_of_six (hwc n) (hw6 n)).trans (mul_le_mul_right
      ((eLpNorm_fderiv_le (hwc n) (hEi n)).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hEle n)) (by norm_num)))) _)
  have hae : ∀ᵐ y ∂volume, Tendsto (fun n =>
      ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y) atTop (𝓝 (g y)) := by
    refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := φ) (K := 2) ?_ ?_ hloc
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · refine Eventually.of_forall fun n => le_of_eq ?_
      show 1 / ((n : ℝ) + 1) = 2 * (1 / (2 * ((n : ℝ) + 1)))
      field_simp
  have hlim := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 6) (μ := volume)
    (fun n => (hwc n).continuous.aestronglyMeasurable) g hae
  exact hlim.trans ((Filter.liminf_le_liminf (Eventually.of_forall hbound)).trans
    (le_of_eq (liminf_const B)))


end Breakdown.SteadyCert.SideStripSixInternal

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis
open Set Real
open Breakdown.FracInternal.ModeHeightAxis Breakdown.CellCert.CellAnalysis.LowEntry.Internal

private theorem col_weak {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    {χ : Space → ℝ} (hχ : IsTestScalar χ) (i : Fin 3) (ψ : Space → ℝ) (hψ : IsTestScalar ψ) (j : Fin 3) :
    ∫ y, (fderiv ℝ ψ y (unitVector j)) • (χ y • G y (unitVector i)) =
      -∫ y, ψ y • ((fderiv ℝ χ y (unitVector j)) • G y (unitVector i) +
        χ y • H y (unitVector j) (unitVector i)) := by
  have hw : LocallyIntegrable (fun y => G y (unitVector i)) volume :=
    (col_memLp hs.measurable_gradient hs.gradient_two i).locallyIntegrable (by norm_num)
  have hh : LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume :=
    (second_memLp hs.measurable_second hs.second_two j i).locallyIntegrable (by norm_num)
  have hpc : IsTestScalar (fun y => ψ y * χ y) := ⟨hψ.1.mul hχ.1, hψ.2.mul_right⟩
  have hd : ∀ y, fderiv ℝ (fun y => ψ y * χ y) y (unitVector j) =
      ψ y * fderiv ℝ χ y (unitVector j) + χ y * fderiv ℝ ψ y (unitVector j) := by
    intro y
    show fderiv ℝ (ψ * χ) y (unitVector j) = _
    rw [fderiv_mul ((hψ.1.differentiable (by simp)) y) ((hχ.1.differentiable (by simp)) y)]
    simp
  have hws := hs.weak_second _ hpc i j
  have hcχ : Continuous (fun y => fderiv ℝ χ y (unitVector j)) :=
    (hχ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ (fun y => ψ y * χ y) y (unitVector j) • G y (unitVector i)) :=
    hw.integrable_smul_left_of_hasCompactSupport
      ((hpc.1.continuous_fderiv (by simp)).clm_apply continuous_const) (hpc.2.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => (ψ y * fderiv ℝ χ y (unitVector j)) • G y (unitVector i)) :=
    hw.integrable_smul_left_of_hasCompactSupport (hψ.1.continuous.mul hcχ) (hψ.2.mul_right)
  have i3 : Integrable (fun y => (ψ y * χ y) • H y (unitVector j) (unitVector i)) :=
    hh.integrable_smul_left_of_hasCompactSupport hpc.1.continuous hpc.2
  have e1 : ∀ y, (fderiv ℝ ψ y (unitVector j)) • (χ y • G y (unitVector i)) =
      fderiv ℝ (fun y => ψ y * χ y) y (unitVector j) • G y (unitVector i) -
        (ψ y * fderiv ℝ χ y (unitVector j)) • G y (unitVector i) := by
    intro y
    rw [hd, smul_smul, ← sub_smul]
    congr 1
    ring
  have e2 : ∀ y, ψ y • ((fderiv ℝ χ y (unitVector j)) • G y (unitVector i) +
      χ y • H y (unitVector j) (unitVector i)) =
      (ψ y * fderiv ℝ χ y (unitVector j)) • G y (unitVector i) +
        (ψ y * χ y) • H y (unitVector j) (unitVector i) := by
    intro y
    rw [smul_add, smul_smul, smul_smul]
  simp_rw [e1, e2]
  rw [integral_sub i1 i2, integral_add i2 i3, hws]
  abel

private theorem col_six {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    {χ : Space → ℝ} (hχ : IsTestScalar χ) (hχ1 : ∀ y, |χ y| ≤ 1) (i : Fin 3) :
    MemLp (fun y => χ y • G y (unitVector i)) 6 volume := by
  have hw2 : MemLp (fun y => G y (unitVector i)) 2 volume :=
    col_memLp hs.measurable_gradient hs.gradient_two i
  have hg2 : MemLp (fun y => χ y • G y (unitVector i)) 2 volume :=
    hw2.of_le (hχ.1.continuous.aestronglyMeasurable.smul hw2.1) (Filter.Eventually.of_forall fun y => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 y))
  have hgc : HasCompactSupport (fun y => χ y • G y (unitVector i)) := hχ.2.smul_right
  obtain ⟨K, hK0, hK⟩ := test_bounded hχ
  set c : Fin 3 → Space → Space := fun j y =>
    (fderiv ℝ χ y (unitVector j)) • G y (unitVector i) + χ y • H y (unitVector j) (unitVector i) with hc
  have hcm : ∀ j, MemLp (c j) 2 volume := by
    intro j
    have hh : MemLp (fun y => H y (unitVector j) (unitVector i)) 2 volume :=
      second_memLp hs.measurable_second hs.second_two j i
    have hcχ : Continuous (fun y => fderiv ℝ χ y (unitVector j)) :=
      (hχ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    refine MemLp.add ?_ ?_
    · refine hw2.of_le_mul (c := K) (hcχ.aestronglyMeasurable.smul hw2.1) (Filter.Eventually.of_forall fun y => ?_)
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖fderiv ℝ χ y (unitVector j)‖ ≤ ‖fderiv ℝ χ y‖ * ‖unitVector j‖ := (fderiv ℝ χ y).le_opNorm _
        _ = ‖fderiv ℝ χ y‖ := by simp [unitVector]
        _ ≤ K := hK y
    · refine hh.of_le (hχ.1.continuous.aestronglyMeasurable.smul hh.1) (Filter.Eventually.of_forall fun y => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 y)
  have hE : Integrable (fun y => ∑ j : Fin 3, ‖c j y‖ ^ 2) :=
    integrable_finsetSum _ fun j _ => (memLp_two_iff_integrable_sq_norm (hcm j).1).1 (hcm j)
  have hb := Breakdown.SteadyCert.SideStripSixInternal.six_bound_of_compact
    (fun y => χ y • G y (unitVector i)) c (fun y => ∑ j : Fin 3, ‖c j y‖ ^ 2)
    hg2 hgc hE (fun z => le_rfl) (fun ψ hψ j => col_weak hs hχ i ψ hψ j)
  exact ⟨hg2.1, lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)⟩

private theorem radial_kernel_le (m : ℕ) (n : ℤ) (a : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    ‖gradKernel m n a 0 θ M‖ ≤ ‖M (unitVector 0)‖ + ‖M (unitVector 1)‖ := by
  rw [gradKernel, norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold frameMat
  refine (inner_unit_bound θ _ a).trans ?_
  have e : (![radialUnit θ, angularUnit θ, axialUnit] (0 : Fin 3)) =
      Real.cos θ • unitVector 0 + Real.sin θ • unitVector 1 := by
    show radialUnit θ = _
    simp only [radialUnit, unitVector]
    rw [single_smul 0 (Real.cos θ), single_smul 1 (Real.sin θ)]
  rw [e, map_add, map_smul, map_smul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, Real.norm_eq_abs]
  · exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one θ)
  · exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one θ)

private theorem pow_bnd (r : ℝ) (hr : 0 < r) {w : ℂ} {t : ℝ} (h : ‖w‖ ≤ ‖t‖) :
    ‖w‖ₑ ≤ ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) + ENNReal.ofReal r * ‖t‖ₑ ^ 6 := by
  have h' := h.trans (root_power_bound r ‖t‖ hr (norm_nonneg _))
  calc ‖w‖ₑ = ENNReal.ofReal ‖w‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (r ^ (-(1 / 5 : ℝ)) + r * ‖t‖ ^ 6) := ENNReal.ofReal_le_ofReal h'
    _ = ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) + ENNReal.ofReal r * ‖t‖ₑ ^ 6 := by
      rw [ENNReal.ofReal_add (Real.rpow_nonneg hr.le _) (by positivity), ENNReal.ofReal_mul hr.le,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

private theorem int_of_six {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R Z : ℝ)
    {X : Space → E} (hXm : AEStronglyMeasurable X volume)
    (φ : ℝ → E → ℂ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) {b : Space → ℝ} (hb : MemLp b 6 volume)
    (hbd : ∀ p ∈ Icc (0 : ℝ) R ×ˢ Icc (-Z) Z, ∀ θ,
      ‖φ θ (X (cylPoint p.1 θ p.2))‖ ≤ ‖b (cylPoint p.1 θ p.2)‖) :
    IntegrableOn (fun p : ℝ × ℝ => ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2)))
      (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have hF := kmeas hXm φ hφc
  have hS : MeasurableSet (Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z) := measurableSet_Ioc.prod measurableSet_Icc
  have hSI : (Icc (0 : ℝ) R ×ˢ Icc (-Z) Z : Set (ℝ × ℝ)) =ᵐ[volume] Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z :=
    Measure.set_prod_ae_eq Ioc_ae_eq_Icc.symm (ae_eq_refl _)
  refine IntegrableOn.congr_set_ae ?_ hSI
  have hsub : Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨hp.1.1, trivial⟩
  set g : Space → ENNReal := fun y => ‖b y‖ₑ ^ 6 with hg_def
  have hgm : AEMeasurable g volume := hb.aestronglyMeasurable.enorm.pow_const 6
  have hfin : ∫⁻ y, g y < ⊤ := by
    have h6 : Integrable (fun y => ‖b y‖ ^ 6) :=
      (show MemLp b ((6 : ℕ) : ENNReal) volume by exact_mod_cast hb).integrable_norm_pow (by norm_num)
    have := h6.hasFiniteIntegral
    unfold HasFiniteIntegral at this
    simpa only [enorm_pow, enorm_norm, hg_def] using this
  have hP : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ (-(1 / 5 : ℝ))) (Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z) := by
    have h1 : IntegrableOn (fun r : ℝ => r ^ (-(1 / 5 : ℝ))) (Ioc 0 R) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) (by norm_num : (-1 : ℝ) < -(1 / 5))).1
    have h2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-Z) Z) := integrableOn_const (by simp)
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    simpa using h1.mul_prod h2
  have hpt : ∀ p ∈ Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z,
      ‖∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ ≤
        ENNReal.ofReal (2 * π) * ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ +
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
    intro p hp
    have hr : 0 < p.1 := hp.1.1
    have hp' : p ∈ Icc (0 : ℝ) R ×ˢ Icc (-Z) Z := ⟨⟨hr.le, hp.1.2⟩, hp.2⟩
    have hc : ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ = ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) :=
      Real.enorm_eq_ofReal (Real.rpow_nonneg hr.le _)
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ θ in Ioo (-π) π, ‖φ θ (X (cylPoint p.1 θ p.2))‖ₑ
        ≤ ∫⁻ θ in Ioo (-π) π, (ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) +
            ENNReal.ofReal p.1 * g (cylPoint p.1 θ p.2)) :=
          lintegral_mono fun θ => pow_bnd p.1 hr (hbd p hp' θ)
      _ = ENNReal.ofReal (2 * π) * ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ +
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Real.volume_Ioo, hc,
            show π - -π = 2 * π by ring]
          ring
  have hA : ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ < ⊤ := hP.2
  have hB : ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z,
      ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) < ⊤ := by
    refine lt_of_le_of_lt ?_ hfin
    rw [← half_eq g hgm]
    exact lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
  refine ⟨hF.mono_measure (Measure.restrict_mono hsub le_rfl), ?_⟩
  unfold HasFiniteIntegral
  have hm1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (2 * π) * ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ :=
    measurable_const.mul (measurable_fst.pow_const _).enorm
  calc ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, ‖∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ
      ≤ ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, (ENNReal.ofReal (2 * π) * ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ +
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := setLIntegral_mono' hS hpt
    _ = ENNReal.ofReal (2 * π) * (∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ) +
          ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z,
            ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
        rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA, hB⟩

private theorem ball_of_box {R Z ρ : ℝ} (hρ : ρ = 2 * |R| + |Z| + 1) {p : ℝ × ℝ}
    (hp : p ∈ Icc (0 : ℝ) R ×ˢ Icc (-Z) Z) (θ : ℝ) : ‖cylPoint p.1 θ p.2‖ ≤ ρ := by
  refine (cylPoint_norm _ _ _).trans ?_
  have h1 : |p.1| ≤ |R| := by rw [abs_of_nonneg hp.1.1]; exact hp.1.2.trans (le_abs_self R)
  have h2 : |p.2| ≤ |Z| :=
    abs_le.2 ⟨by linarith [hp.2.1, le_abs_self Z, neg_abs_le Z], hp.2.2.trans (le_abs_self Z)⟩
  rw [hρ]
  linarith

private theorem radial_col_int {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    (m' : ℕ) (n : ℤ) (a : Fin 3) (R Z : ℝ) :
    IntegrableOn (gradMode m' n G a 0) (Icc 0 R ×ˢ Icc (-Z) Z) := by
  set ρ : ℝ := 2 * |R| + |Z| + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hχ : IsTestScalar (radialCutoff ρ) := ⟨contDiff_radialCutoff hρ0, hasCompactSupport_radialCutoff hρ0⟩
  have hχ1 : ∀ y, |radialCutoff ρ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (radialCutoff_nonneg ρ y)]
    exact radialCutoff_le_one ρ y
  have hb : MemLp (fun y => ‖radialCutoff ρ y • G y (unitVector 0)‖ +
      ‖radialCutoff ρ y • G y (unitVector 1)‖) 6 volume :=
    (col_six hs hχ hχ1 0).norm.add (col_six hs hχ hχ1 1).norm
  have hint := (int_of_six R Z hs.measurable_gradient (gradKernel m' n a 0) (gradKernel_cont m' n a 0) hb
    (fun p hp θ => by
      rw [radialCutoff_eq_one hρ0 (ball_of_box hρ hp θ), one_smul, one_smul,
        Real.norm_of_nonneg (by positivity)]
      exact radial_kernel_le m' n a θ _)).const_mul (1 / (2 * π) : ℂ)
  refine IntegrableOn.congr_fun hint (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  rw [gradMode_eq m' n G a 0 p]

private theorem vel_col_int {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    (m' : ℕ) (n : ℤ) (a : Fin 3) (R Z : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => modeVec m' n v p.1 p.2 a) (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have hint := (Breakdown.FracInternal.ModeHeightAxis.vel_int R Z hs.velocity_six (velKernel m' n a)
    (velKernel_cont m' n a) (velKernel_bound m' n a)).const_mul (1 / (2 * π) : ℂ)
  refine IntegrableOn.congr_fun hint (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  rw [modeVec_eq m' n v a p]

private def thirdKer (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ) (T : Space →L[ℝ] Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (frameThird θ T a b c : ℂ)

private theorem thirdKer_cont (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => thirdKer m n a b c q.1 q.2) := by
  unfold thirdKer frameThird frameUnit
  exact (phase_cont m n).mul (Complex.continuous_ofReal.comp
    (((continuous_snd.clm_apply ((unit_cont c).comp continuous_fst)).clm_apply
      ((unit_cont b).comp continuous_fst)).inner ((unit_cont a).comp continuous_fst)))

private theorem thirdKer_bound (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ) (T : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖thirdKer m n a b c θ T‖ ≤ ‖T‖ := by
  rw [thirdKer, norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold frameThird frameUnit
  refine (inner_unit_bound θ _ a).trans ((T.le_opNorm₂ _ _).trans ?_)
  calc ‖T‖ * ‖![radialUnit θ, angularUnit θ, axialUnit] c‖ * ‖![radialUnit θ, angularUnit θ, axialUnit] b‖
      ≤ ‖T‖ * 1 * 1 := by gcongr <;> exact unit_norm θ _
    _ = ‖T‖ := by ring

private theorem third_eq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3)
    (p : ℝ × ℝ) : modeThird m n H a b c p =
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, thirdKer m n a b c θ (H (cylPoint p.1 θ p.2)) := by
  unfold modeThird
  rw [per_interval]
  · rfl
  · intro θ
    simp only [phase_per, cylPoint_per, frameThird, frameUnit, radialUnit, angularUnit,
      Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem bil_le (T : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖T‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖T (unitVector i) (unitVector j)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ T (by positivity) fun x y => ?_
  have hx : x = ∑ i, x i • unitVector i := by
    simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x).symm
  have hy : y = ∑ j, y j • unitVector j := by
    simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y).symm
  have hT : T x y = ∑ i, ∑ j, (x i * y j) • T (unitVector i) (unitVector j) := by
    conv_lhs => rw [hx, hy]
    simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [hT, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_mul]
  have h1 : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have h2 : |y j| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y j
  have h3 := norm_nonneg (T (unitVector i) (unitVector j))
  calc |x i| * |y j| * ‖T (unitVector i) (unitVector j)‖
      ≤ ‖x‖ * ‖y‖ * ‖T (unitVector i) (unitVector j)‖ := by gcongr
    _ = ‖T (unitVector i) (unitVector j)‖ * ‖x‖ * ‖y‖ := by ring

private theorem second_loc {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    LocallyIntegrable H volume := by
  have hsum : MemLp (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖) 2 volume :=
    memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
      (second_memLp hs.measurable_second hs.second_two i j).norm
  refine (hsum.locallyIntegrable (by norm_num)).mono hs.measurable_second (Filter.Eventually.of_forall fun y => ?_)
  refine (bil_le (H y)).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

private theorem third_weighted {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    (m' : ℕ) (n : ℤ) (a b c : Fin 3) (R Z : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m' n H a b c p) (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have hint := (weighted_int R Z (second_loc hs) (thirdKer m' n a b c) (thirdKer_cont m' n a b c)
    (thirdKer_bound m' n a b c)).const_mul (1 / (2 * π) : ℂ)
  refine IntegrableOn.congr_fun hint (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  rw [third_eq m' n H a b c p]
  ring

private theorem coef_mul {s : Set (ℝ × ℝ)} (hs : IsCompact s) {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f s)
    {g : ℝ × ℝ → ℝ} (hg : Continuous g) : IntegrableOn (fun p => ((g p : ℝ) : ℂ) * f p) s :=
  IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp hg).continuousOn hf hs

private theorem rect_sub (K : CellBox) (hK : IsCellBox K) : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ := by
  intro p hp
  simp only [CellBox.rect, mem_prod, mem_Icc] at hp
  exact ⟨⟨hK.r_order.1.trans hp.1.1, hp.1.2⟩, ⟨by linarith [hp.2.1, hK.z_order.1, hK.z_order.2], hp.2.2⟩⟩

private theorem icc_pair {u w l : ℝ} (huw : u < w) (hl : l = u ∨ l = w) :
    Icc (min l (u + w - l)) (max l (u + w - l)) = Icc u w := by
  rcases hl with h | h <;> rw [h]
  · rw [show u + w - u = w by ring, min_eq_left huw.le, max_eq_right huw.le]
  · rw [show u + w - w = u by ring, min_eq_right huw.le, max_eq_left huw.le]

private theorem radial_pair {K : CellBox} {V G0 T : ℝ × ℝ → ℂ}
    (hV : IntegrableOn V K.rect) (hG0 : IntegrableOn G0 K.rect) (lv ot : ℝ)
    (hset : Icc (min lv ot) (max lv ot) = Icc K.r₁ K.r₂)
    (hT : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - ot) / (lv - ot) : ℝ) : ℂ) * T p) K.rect) :
    IntegrableOn (fun p : ℝ × ℝ => (((1 / (lv - ot) : ℝ)) : ℂ) * V p + (((p.1 - ot) / (lv - ot) : ℝ) : ℂ) * G0 p)
        (Icc (min lv ot) (max lv ot) ×ˢ Icc K.z₁ K.z₂) ∧
      IntegrableOn (fun p : ℝ × ℝ => (((1 / (lv - ot) : ℝ)) : ℂ) * G0 p + (((p.1 - ot) / (lv - ot) : ℝ) : ℂ) * T p)
        (Icc (min lv ot) (max lv ot) ×ˢ Icc K.z₁ K.z₂) := by
  rw [hset]
  have hc := rect_compact K
  exact ⟨(coef_mul hc hV (g := fun _ => 1 / (lv - ot)) continuous_const).add
      (coef_mul hc hG0 (g := fun p => (p.1 - ot) / (lv - ot)) (by fun_prop)),
    (coef_mul hc hG0 (g := fun _ => 1 / (lv - ot)) continuous_const).add hT⟩

private theorem height_pair {K : CellBox} {V G2 T : ℝ × ℝ → ℂ}
    (hV : IntegrableOn V K.rect) (hG2 : IntegrableOn G2 K.rect)
    (hT : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * T p) K.rect) (lv ot : ℝ)
    (hset : Icc (min lv ot) (max lv ot) = Icc K.z₁ K.z₂) :
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (lv - ot) : ℝ)) : ℂ) * V p
        + (((p.2 - ot) / (lv - ot) : ℝ) : ℂ) * G2 p) * ((1 : ℝ) : ℂ))
        (Icc K.r₁ K.r₂ ×ˢ Icc (min lv ot) (max lv ot)) ∧
      IntegrableOn (fun p : ℝ × ℝ => ((((1 / (lv - ot) : ℝ)) : ℂ) * G2 p
        + (((p.2 - ot) / (lv - ot) : ℝ) : ℂ) * T p) * ((p.1 : ℝ) : ℂ))
        (Icc K.r₁ K.r₂ ×ˢ Icc (min lv ot) (max lv ot)) := by
  rw [hset]
  have hc := rect_compact K
  refine ⟨?_, ?_⟩
  · have h := (coef_mul hc hV (g := fun _ => 1 / (lv - ot)) continuous_const).add
      (coef_mul hc hG2 (g := fun p => (p.2 - ot) / (lv - ot)) (by fun_prop))
    refine h.congr_fun (fun p _ => ?_) (rect_meas K)
    simp only [Pi.add_apply, Complex.ofReal_one, mul_one]
  · have h := (coef_mul hc hG2 (g := fun p => 1 / (lv - ot) * p.1) (by fun_prop)).add
      (coef_mul hc hT (g := fun p => (p.2 - ot) / (lv - ot)) (by fun_prop))
    refine h.congr_fun (fun p _ => ?_) (rect_meas K)
    simp only [Pi.add_apply]
    push_cast
    ring

theorem sideStripIntegrable_holds : SideStripIntegrableStatement := by
  intro k N c K S B L hL x hx n e a he
  have hs : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := by rw [hL.order_eq]; exact hx.1
  have hK : IsCellBox L.box := hL.box_eq ▸ hL.box_valid
  have he' : e.val = 0 → L.box.r₁ ≠ 0 := by rw [hL.box_eq]; exact he
  clear he
  have hsub := rect_sub L.box hK
  have hc : IsCompact L.box.rect := rect_compact L.box
  have hV : IntegrableOn (L.velMode n x a) L.box.rect :=
    (vel_col_int hs L.order n a L.box.r₂ L.box.z₂).mono_set hsub
  have hG0 : IntegrableOn (L.gradModeOf n x a 0) L.box.rect :=
    (radial_col_int hs L.order n a L.box.r₂ L.box.z₂).mono_set hsub
  have hG2 : IntegrableOn (L.gradModeOf n x a 2) L.box.rect :=
    (modeHeightAxis L.order x.1 x.2.1 x.2.2.1 hs n a L.box.r₂ L.box.z₂).mono_set hsub
  have hT : ∀ b c : Fin 3, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * L.secondModeOf n x a b c p) L.box.rect :=
    fun b c => (third_weighted hs L.order n a b c L.box.r₂ L.box.z₂).mono_set hsub
  have hTu : L.box.r₁ ≠ 0 → ∀ b c : Fin 3, IntegrableOn (L.secondModeOf n x a b c) L.box.rect := by
    intro h0 b c
    have hpos : 0 < L.box.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
    have hne : ∀ p ∈ L.box.rect, p.1 ≠ 0 := fun p hp => ne_of_gt (lt_of_lt_of_le hpos hp.1.1)
    have hco : ContinuousOn (fun p : ℝ × ℝ => ((1 / p.1 : ℝ) : ℂ)) L.box.rect :=
      Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.div continuous_fst.continuousOn hne)
    refine (IntegrableOn.continuousOn_mul hco (hT b c) hc).congr_fun (fun p hp => ?_) (rect_meas _)
    dsimp only
    rw [← mul_assoc, ← Complex.ofReal_mul, one_div_mul_cancel (hne p hp), Complex.ofReal_one, one_mul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hot : L.sideOther e = L.box.r₁ + L.box.r₂ - L.sideLevel e := by
      rw [CellLayout.sideOther, if_pos h]
    have hl : (L.sideLevel e = L.box.r₁ ∧ e.val = 0) ∨ (L.sideLevel e = L.box.r₂ ∧ e.val = 1) := by
      unfold CellLayout.sideLevel
      rcases (by omega : e.val = 0 ∨ e.val = 1) with h' | h' <;> simp [h']
    rw [hot]
    refine radial_pair hV hG0 (L.sideLevel e) _ (icc_pair hK.r_order.2 (hl.imp And.left And.left)) ?_
    by_cases h0 : L.box.r₁ = 0
    · have hl2 : L.sideLevel e = L.box.r₂ := by
        rcases hl with hl | hl
        · exact absurd h0 (he' hl.2)
        · exact hl.1
      refine IntegrableOn.congr_fun ((hT 0 0).const_mul (((1 / L.box.r₂ : ℝ)) : ℂ)) (fun p _ => ?_) (rect_meas _)
      rw [hl2, h0]
      simp only [zero_add, sub_self, sub_zero]
      push_cast
      ring
    · exact coef_mul hc (hTu h0 0 0) (by fun_prop)
  · have h2 : ¬ e.val < 2 := by omega
    have hot : L.sideOther e = L.box.z₁ + L.box.z₂ - L.sideLevel e := by
      rw [CellLayout.sideOther, if_neg h2]
    have hl : L.sideLevel e = L.box.z₁ ∨ L.sideLevel e = L.box.z₂ := by
      unfold CellLayout.sideLevel
      rcases (by omega : e.val = 2 ∨ e.val = 3) with h' | h' <;> simp [h']
    rw [hot]
    exact height_pair hV hG2 (hT 2 2) (L.sideLevel e) _ (icc_pair hK.z_order.2 hl)

end Breakdown.CellCert.CellFormula
