import Breakdown.FracCell.StCornerModesOpen
import Breakdown.FracCell.LowEntry
import Breakdown.FracCert.SecondOrderComplete
import Breakdown.FreqTr.GradSixDecay
import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal NNReal
open MeasureTheory Filter Topology
open scoped Convolution

noncomputable section

namespace Breakdown.SteadyCert.ModeHeightAxisInternal

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


end Breakdown.SteadyCert.ModeHeightAxisInternal

namespace Breakdown.FracInternal.ModeHeightAxis

open Set Real
open Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.CellAnalysis
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem half_le (R Z : ℝ) :
    volume.restrict (Icc (0 : ℝ) R ×ˢ Icc (-Z) Z) ≤ volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  refine Measure.restrict_mono_ae ?_
  have hsub : Icc (0 : ℝ) R ×ˢ Icc (-Z) Z ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨hp.1.1, trivial⟩
  refine hsub.eventuallyLE.trans ?_
  have : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) =ᵐ[volume] Ici (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    Measure.set_prod_ae_eq Ioi_ae_eq_Ici (ae_eq_refl _)
  exact this.symm.le

theorem kmeas {X : Space → E} (hXm : AEStronglyMeasurable X volume)
    (φ : ℝ → E → ℂ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  have hf : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => φ q.2 (X (cylArg q))) muU :=
    hφc.comp_aestronglyMeasurable (measurable_snd.aestronglyMeasurable.prodMk
      (hXm.comp_quasiMeasurePreserving qmp))
  rw [muU_def] at hf
  exact hf.integral_prod_right'

theorem half_eq (g : Space → ENNReal) (hgm : AEMeasurable g volume) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) = ∫⁻ y, g y := by
  rw [← key g, muU_def, lintegral_prod]
  · congr 1; funext p
    dsimp only
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
      (hgm.comp_quasiMeasurePreserving (muU_def ▸ qmp))

theorem weighted_int (R Z : ℝ) {X : Space → E} (hX : LocallyIntegrable X volume)
    (φ : ℝ → E → ℂ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2)))
      (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have hXm := hX.aestronglyMeasurable
  have hF := kmeas hXm φ hφc
  have hS : MeasurableSet (Icc (0 : ℝ) R ×ˢ Icc (-Z) Z) := measurableSet_Icc.prod measurableSet_Icc
  set ρ : ℝ := 2 * |R| + |Z| with hρ
  set g : Space → ENNReal := (Metric.closedBall (0 : Space) ρ).indicator (fun y => ‖X y‖ₑ) with hg_def
  have hball : ∀ p ∈ Icc (0 : ℝ) R ×ˢ Icc (-Z) Z, ∀ θ,
      cylPoint p.1 θ p.2 ∈ Metric.closedBall (0 : Space) ρ := by
    intro p hp θ
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (LowEntry.Internal.cylPoint_norm _ _ _).trans ?_
    have h1 : |p.1| ≤ |R| := by rw [abs_of_nonneg hp.1.1]; exact hp.1.2.trans (le_abs_self R)
    have h2 : |p.2| ≤ |Z| := abs_le.2 ⟨by linarith [hp.2.1, le_abs_self Z], hp.2.2.trans (le_abs_self Z)⟩
    rw [hρ]
    linarith
  have hpt : ∀ p ∈ Icc (0 : ℝ) R ×ˢ Icc (-Z) Z,
      ‖(p.1 : ℂ) * ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ ≤
        ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
    intro p hp
    have hi : ‖∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ ≤
        ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun θ => ?_)
      rw [hg_def, Set.indicator_of_mem (hball p hp θ), ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hφb θ _)
    have hw : ‖((p.1 : ℝ) : ℂ)‖ₑ = ENNReal.ofReal p.1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.1.1]
    rw [enorm_mul, hw]
    exact mul_le_mul' le_rfl hi
  have hgm : AEMeasurable g volume := hXm.enorm.indicator measurableSet_closedBall
  have hfin : ∫⁻ y, g y < ⊤ := by
    rw [hg_def, lintegral_indicator measurableSet_closedBall]
    exact (hX.integrableOn_isCompact (isCompact_closedBall 0 ρ)).2
  refine ⟨(Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul
    (hF.mono_measure (half_le R Z)), ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt ?_ hfin
  calc ∫⁻ p in Icc (0 : ℝ) R ×ˢ Icc (-Z) Z,
        ‖(p.1 : ℂ) * ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ
      ≤ ∫⁻ p in Icc (0 : ℝ) R ×ˢ Icc (-Z) Z,
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := setLIntegral_mono' hS hpt
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := lintegral_mono' (half_le R Z) le_rfl
    _ = ∫⁻ y, g y := half_eq g hgm

theorem root_power_bound (r t : ℝ) (hr : 0 < r) (_ht : 0 ≤ t) : t ≤ r ^ (-(1 / 5 : ℝ)) + r * t ^ 6 := by
  set s := r ^ (-(1 / 5 : ℝ)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hr _
  have h5 : s ^ 5 = r⁻¹ := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hr.le,
      show (-(1 / 5 : ℝ)) * ((5 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have h6 : 0 ≤ r * t ^ 6 := by positivity
  by_cases h : t ≤ s
  · linarith
  · push Not at h
    have h5' : s ^ 5 < t ^ 5 := pow_lt_pow_left₀ h hs0.le (by norm_num)
    have h1 : 1 < r * t ^ 5 := by
      rw [h5] at h5'
      have := mul_lt_mul_of_pos_left h5' hr
      rwa [mul_inv_cancel₀ hr.ne'] at this
    have ht0 : 0 < t := hs0.trans h
    have h2 : t * 1 < t * (r * t ^ 5) := mul_lt_mul_of_pos_left h1 ht0
    have e : t * (r * t ^ 5) = r * t ^ 6 := by ring
    linarith

theorem pt_bound (r : ℝ) (hr : 0 < r) (φ : ℝ → Space → ℂ) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) (θ : ℝ) (u : Space) :
    ‖φ θ u‖ₑ ≤ ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) + ENNReal.ofReal r * ‖u‖ₑ ^ 6 := by
  have h := (hφb θ u).trans (root_power_bound r ‖u‖ hr (norm_nonneg _))
  calc ‖φ θ u‖ₑ = ENNReal.ofReal ‖φ θ u‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (r ^ (-(1 / 5 : ℝ)) + r * ‖u‖ ^ 6) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) + ENNReal.ofReal r * ‖u‖ₑ ^ 6 := by
      rw [ENNReal.ofReal_add (Real.rpow_nonneg hr.le _) (by positivity), ENNReal.ofReal_mul hr.le,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem vel_int (R Z : ℝ) {v : Space → Space} (hv : MemLp v 6 volume) (φ : ℝ → Space → ℂ)
    (hφc : Continuous (fun q : ℝ × Space => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) :
    IntegrableOn (fun p : ℝ × ℝ => ∫ θ in Ioo (-π) π, φ θ (v (cylPoint p.1 θ p.2)))
      (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have hvm := hv.aestronglyMeasurable
  have hF := kmeas hvm φ hφc
  have hS : MeasurableSet (Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z) := measurableSet_Ioc.prod measurableSet_Icc
  have hSI : (Icc (0 : ℝ) R ×ˢ Icc (-Z) Z : Set (ℝ × ℝ)) =ᵐ[volume] Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z :=
    Measure.set_prod_ae_eq Ioc_ae_eq_Icc.symm (ae_eq_refl _)
  refine IntegrableOn.congr_set_ae ?_ hSI
  have hsub : Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨hp.1.1, trivial⟩
  set g : Space → ENNReal := fun y => ‖v y‖ₑ ^ 6 with hg_def
  have hgm : AEMeasurable g volume := hvm.enorm.pow_const 6
  have hfin : ∫⁻ y, g y < ⊤ := by
    have h6 : Integrable (fun y => ‖v y‖ ^ 6) :=
      (show MemLp v ((6 : ℕ) : ENNReal) volume by exact_mod_cast hv).integrable_norm_pow (by norm_num)
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
      ‖∫ θ in Ioo (-π) π, φ θ (v (cylPoint p.1 θ p.2))‖ₑ ≤
        ENNReal.ofReal (2 * π) * ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ +
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
    intro p hp
    have hr : 0 < p.1 := hp.1.1
    have hc : ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ = ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) :=
      Real.enorm_eq_ofReal (Real.rpow_nonneg hr.le _)
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ θ in Ioo (-π) π, ‖φ θ (v (cylPoint p.1 θ p.2))‖ₑ
        ≤ ∫⁻ θ in Ioo (-π) π, (ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) +
            ENNReal.ofReal p.1 * g (cylPoint p.1 θ p.2)) :=
          lintegral_mono fun θ => pt_bound p.1 hr φ hφb θ _
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
  calc ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, ‖∫ θ in Ioo (-π) π, φ θ (v (cylPoint p.1 θ p.2))‖ₑ
      ≤ ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, (ENNReal.ofReal (2 * π) * ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ +
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := setLIntegral_mono' hS hpt
    _ = ENNReal.ofReal (2 * π) * (∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ) +
          ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z,
            ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
        rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA, hB⟩



theorem axial_eq_unit : axialUnit = unitVector 2 := rfl

theorem col_memLp {G : Space → (Space →L[ℝ] Space)} (hG1 : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) (i : Fin 3) :
    MemLp (fun y => G y (unitVector i)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector i)) volume :=
    (continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hG1
  refine (memLp_two_iff_integrable_sq_norm hm).2 (hG2.mono' (hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Finset.single_le_sum (f := fun i' => ‖G y (unitVector i')‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ i)

theorem second_memLp {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2))
    (i j : Fin 3) : MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
    ((continuous_id.clm_apply continuous_const).clm_apply continuous_const).comp_aestronglyMeasurable hH
  refine (memLp_two_iff_integrable_sq_norm hm).2 (h2.mono' (hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (Finset.single_le_sum (f := fun j' => ‖H y (unitVector i) (unitVector j')‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ‖H y (unitVector i') (unitVector j')‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))

theorem test_bounded {χ : Space → ℝ} (hχ : IsTestScalar χ) : ∃ K, 0 ≤ K ∧ ∀ y, ‖fderiv ℝ χ y‖ ≤ K := by
  obtain ⟨K, hK⟩ := (hχ.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hχ.2.fderiv (𝕜 := ℝ))
  exact ⟨max K 0, le_max_right _ _, fun y => (hK y).trans (le_max_left _ _)⟩

theorem cut_weak {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    {χ : Space → ℝ} (hχ : IsTestScalar χ) (ψ : Space → ℝ) (hψ : IsTestScalar ψ) (j : Fin 3) :
    ∫ y, (fderiv ℝ ψ y (unitVector j)) • (χ y • G y axialUnit) =
      -∫ y, ψ y • ((fderiv ℝ χ y (unitVector j)) • G y axialUnit + χ y • H y (unitVector j) axialUnit) := by
  have hw : LocallyIntegrable (fun y => G y axialUnit) volume :=
    (col_memLp hs.measurable_gradient hs.gradient_two 2).locallyIntegrable (by norm_num)
  have hh : LocallyIntegrable (fun y => H y (unitVector j) axialUnit) volume := by
    rw [axial_eq_unit]
    exact (second_memLp hs.measurable_second hs.second_two j 2).locallyIntegrable (by norm_num)
  have hpc : IsTestScalar (fun y => ψ y * χ y) := ⟨hψ.1.mul hχ.1, hψ.2.mul_right⟩
  have hd : ∀ y, fderiv ℝ (fun y => ψ y * χ y) y (unitVector j) =
      ψ y * fderiv ℝ χ y (unitVector j) + χ y * fderiv ℝ ψ y (unitVector j) := by
    intro y
    show fderiv ℝ (ψ * χ) y (unitVector j) = _
    rw [fderiv_mul ((hψ.1.differentiable (by simp)) y) ((hχ.1.differentiable (by simp)) y)]
    simp
  have hws := hs.weak_second _ hpc 2 j
  rw [← axial_eq_unit] at hws
  have hcψ : Continuous (fun y => fderiv ℝ ψ y (unitVector j)) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcχ : Continuous (fun y => fderiv ℝ χ y (unitVector j)) :=
    (hχ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsψ : HasCompactSupport (fun y => fderiv ℝ ψ y (unitVector j)) := hψ.2.fderiv_apply (𝕜 := ℝ) _
  have hsχ : HasCompactSupport (fun y => fderiv ℝ χ y (unitVector j)) := hχ.2.fderiv_apply (𝕜 := ℝ) _
  have i1 : Integrable (fun y => fderiv ℝ (fun y => ψ y * χ y) y (unitVector j) • G y axialUnit) :=
    hw.integrable_smul_left_of_hasCompactSupport
      ((hpc.1.continuous_fderiv (by simp)).clm_apply continuous_const) (hpc.2.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => (ψ y * fderiv ℝ χ y (unitVector j)) • G y axialUnit) :=
    hw.integrable_smul_left_of_hasCompactSupport (hψ.1.continuous.mul hcχ) (hψ.2.mul_right)
  have i3 : Integrable (fun y => (ψ y * χ y) • H y (unitVector j) axialUnit) :=
    hh.integrable_smul_left_of_hasCompactSupport hpc.1.continuous hpc.2
  have e1 : ∀ y, (fderiv ℝ ψ y (unitVector j)) • (χ y • G y axialUnit) =
      fderiv ℝ (fun y => ψ y * χ y) y (unitVector j) • G y axialUnit -
        (ψ y * fderiv ℝ χ y (unitVector j)) • G y axialUnit := by
    intro y
    rw [hd, smul_smul, ← sub_smul]
    congr 1
    ring
  have e2 : ∀ y, ψ y • ((fderiv ℝ χ y (unitVector j)) • G y axialUnit + χ y • H y (unitVector j) axialUnit) =
      (ψ y * fderiv ℝ χ y (unitVector j)) • G y axialUnit + (ψ y * χ y) • H y (unitVector j) axialUnit := by
    intro y
    rw [smul_add, smul_smul, smul_smul]
  simp_rw [e1, e2]
  rw [integral_sub i1 i2, integral_add i2 i3, hws]
  abel

theorem cut_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    {χ : Space → ℝ} (hχ : IsTestScalar χ) (hχ1 : ∀ y, |χ y| ≤ 1) :
    MemLp (fun y => χ y • G y axialUnit) 6 volume := by
  have hw2 : MemLp (fun y => G y axialUnit) 2 volume :=
    col_memLp hs.measurable_gradient hs.gradient_two 2
  have hg2 : MemLp (fun y => χ y • G y axialUnit) 2 volume :=
    hw2.of_le (hχ.1.continuous.aestronglyMeasurable.smul hw2.1) (Filter.Eventually.of_forall fun y => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 y))
  have hgc : HasCompactSupport (fun y => χ y • G y axialUnit) := hχ.2.smul_right
  obtain ⟨K, hK0, hK⟩ := test_bounded hχ
  set c : Fin 3 → Space → Space := fun j y =>
    (fderiv ℝ χ y (unitVector j)) • G y axialUnit + χ y • H y (unitVector j) axialUnit with hc
  have hcm : ∀ j, MemLp (c j) 2 volume := by
    intro j
    have hh : MemLp (fun y => H y (unitVector j) axialUnit) 2 volume := by
      rw [axial_eq_unit]
      exact second_memLp hs.measurable_second hs.second_two j 2
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
  have hb := Breakdown.SteadyCert.ModeHeightAxisInternal.six_bound_of_compact (fun y => χ y • G y axialUnit) c (fun y => ∑ j : Fin 3, ‖c j y‖ ^ 2)
    hg2 hgc hE (fun z => le_rfl) (fun ψ hψ j => cut_weak hs hχ ψ hψ j)
  exact ⟨hg2.1, lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)⟩

theorem kernel_axial (m : ℕ) (n : ℤ) (a : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    gradKernel m n a 2 θ M = velKernel m n a θ (M axialUnit) := by
  unfold gradKernel velKernel
  congr 2
  fin_cases a <;> rfl

end Breakdown.FracInternal.ModeHeightAxis

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis
open Set Real
open Breakdown.FracInternal.ModeHeightAxis Breakdown.CellCert.CellAnalysis.LowEntry.Internal

theorem modeHeightAxis : ModeHeightAxisStatement := by
  intro m v G H hs n a R Z
  set ρ : ℝ := 2 * |R| + |Z| + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hχ : IsTestScalar (radialCutoff ρ) := ⟨contDiff_radialCutoff hρ0, hasCompactSupport_radialCutoff hρ0⟩
  have hχ1 : ∀ y, |radialCutoff ρ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (radialCutoff_nonneg ρ y)]
    exact radialCutoff_le_one ρ y
  have h6 := cut_memLp hs hχ hχ1
  have hint := (vel_int R Z h6 (velKernel m n a) (velKernel_cont m n a) (velKernel_bound m n a)).const_mul
    (1 / (2 * π) : ℂ)
  refine IntegrableOn.congr_fun hint (fun p hp => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  rw [gradMode_eq m n G a 2 p]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  have hn : ‖cylPoint p.1 θ p.2‖ ≤ ρ := by
    refine (cylPoint_norm _ _ _).trans ?_
    have h1 : |p.1| ≤ |R| := by rw [abs_of_nonneg hp.1.1]; exact hp.1.2.trans (le_abs_self R)
    have h2 : |p.2| ≤ |Z| := abs_le.2 ⟨by linarith [hp.2.1, le_abs_self Z, neg_abs_le Z], hp.2.2.trans (le_abs_self Z)⟩
    rw [hρ]
    linarith
  simp only [radialCutoff_eq_one hρ0 hn, one_smul, kernel_axial]

end Breakdown.CellCert.CellFormula
