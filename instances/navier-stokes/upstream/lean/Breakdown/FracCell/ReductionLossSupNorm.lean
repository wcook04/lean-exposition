import Breakdown.FracCell.ReductionLossDefs
import Breakdown.Cert.SupBoundTestField
import Breakdown.FreqTr.GradSixDecay

open scoped ContDiff ENNReal NNReal
open MeasureTheory Filter Topology
open scoped Convolution

noncomputable section

namespace Breakdown

namespace FracInternal.SupNormBound

open SteadyCert
open Breakdown.Freq.Internal.EmbedNegSsp
open Breakdown.Freq.Internal.GradSixDecay

private theorem normPow_conv_le (φ : ContDiffBump (0 : Space)) (f : Space → Space)
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

private theorem conv_sum_eq (φ : ContDiffBump (0 : Space)) (h : Fin 3 → Space → Space)
    (hh : ∀ i, LocallyIntegrable (h i) volume) (y : Space) :
    ∑ i : Fin 3, (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h i) y =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ∑ i : Fin 3, h i z) y := by
  have hex : ∀ i, Integrable (fun t => φ.normed volume t • h i (y - t)) := fun i => by
    simpa [ConvolutionExistsAt] using (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
      (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) (hh i) y
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [← integral_finsetSum _ (fun i _ => hex i)]
  congr 1
  funext t
  rw [Finset.smul_sum]

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

private theorem pd_smul {a : Space → ℝ} {f : Space → Space} (ha : Differentiable ℝ a)
    (hf : Differentiable ℝ f) (i : Fin 3) :
    pd (fun y => a y • f y) i = fun y => pd a i y • f y + a y • pd f i y := by
  funext y
  simp only [pd]
  rw [fderiv_fun_smul (ha y) (hf y)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

private theorem pd_add {f g : Space → Space} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) : pd (fun y => f y + g y) i = fun y => pd f i y + pd g i y := by
  funext y
  simp only [pd]
  rw [fderiv_fun_add (hf y) (hg y)]
  rfl

private theorem second_sum_smul {a : Space → ℝ} {f : Space → Space} (ha : ContDiff ℝ ∞ a)
    (hf : ContDiff ℝ ∞ f) (x : Space) :
    sumSecondPartialsAt (fun y => a y • f y) x =
      (∑ i : Fin 3, pd (pd a i) i x) • f x + (2 : ℝ) • ∑ i : Fin 3, pd a i x • pd f i x +
        a x • sumSecondPartialsAt f x := by
  have hs : ContDiff ℝ ∞ (fun y => a y • f y) := ha.smul hf
  rw [sumSecondPartialsAt_eq hs, sumSecondPartialsAt_eq hf]
  have h1 : ∀ i, pd (pd (fun y => a y • f y) i) i x =
      pd (pd a i) i x • f x + (2 : ℝ) • (pd a i x • pd f i x) + a x • pd (pd f i) i x := by
    intro i
    have da := differentiable_of_smooth ha
    have df := differentiable_of_smooth hf
    have dai := differentiable_of_smooth (contDiff_pd ha i)
    have dfi := differentiable_of_smooth (contDiff_pd hf i)
    rw [pd_smul da df, pd_add (f := fun y => pd a i y • f y) (g := fun y => a y • pd f i y)
      (dai.smul df) (da.smul dfi), pd_smul dai df, pd_smul da dfi]
    simp only
    module
  simp only [h1, Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul]

private theorem pd_pd_eq_zero {a : Space → ℝ} {z : Space} {c : ℝ} (h : a =ᶠ[𝓝 z] fun _ => c)
    (i j : Fin 3) : pd (pd a i) j z = 0 := by
  have h2 : pd a i =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [Filter.Eventually.eventually_nhds h] with y hy
    show fderiv ℝ a y (unitVector i) = 0
    rw [(show a =ᶠ[𝓝 y] fun _ => c from hy).fderiv_eq]
    simp
  show fderiv ℝ (pd a i) z (unitVector j) = 0
  rw [h2.fderiv_eq]
  simp

private theorem pd_scale {f : Space → ℝ} (hf : Differentiable ℝ f) (c r : ℝ) (i : Fin 3) :
    pd (fun y => c * f (r • y)) i = fun y => c * r * pd f i (r • y) := by
  funext y
  have h1 : HasFDerivAt (fun y : Space => r • y) (r • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_smul r
  have h2 : HasFDerivAt (fun y => c * f (r • y))
      (c • ((fderiv ℝ f (r • y)).comp (r • ContinuousLinearMap.id ℝ Space))) y :=
    ((hf (r • y)).hasFDerivAt.comp y h1).const_mul c
  show fderiv ℝ (fun y => c * f (r • y)) y (unitVector i) = _
  rw [h2.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, pd]
  ring

private theorem cutoff_bounds : ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ y : Space,
    ‖fderiv ℝ (cutoff R) y‖ ≤ K / R ∧ |∑ i : Fin 3, pd (pd (cutoff R) i) i y| ≤ K / R ^ 2 := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_fderiv_cutoff_le
  have hb : ContDiff ℝ ∞ (unitBump : Space → ℝ) := unitBump.contDiff
  have hc : ∀ i : Fin 3, ∃ C, ∀ z, ‖pd (pd (unitBump : Space → ℝ) i) i z‖ ≤ C := fun i =>
    Continuous.bounded_above_of_compact_support (contDiff_pd (contDiff_pd hb i) i).continuous
      (hasCompactSupport_pd (hasCompactSupport_pd unitBump.hasCompactSupport i) i)
  choose C hC using hc
  have hC0 : ∀ i, 0 ≤ C i := fun i => (norm_nonneg _).trans (hC i 0)
  have hS0 : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC0 i
  refine ⟨K₁ + ∑ i, C i, by positivity, fun R hR y => ⟨?_, ?_⟩⟩
  · exact (hK₁ R hR y).trans (div_le_div_of_nonneg_right (by linarith) hR.le)
  · have e1 : cutoff R = fun y => 1 * (unitBump : Space → ℝ) (R⁻¹ • y) := by
      funext y
      simp [cutoff]
    have hbd := differentiable_of_smooth hb
    have e2 : ∀ i, pd (pd (cutoff R) i) i = fun y => 1 * R⁻¹ * R⁻¹ * pd (pd (unitBump : Space → ℝ) i) i (R⁻¹ • y) := by
      intro i
      rw [e1, pd_scale hbd, pd_scale (differentiable_of_smooth (contDiff_pd hb i))]
    simp only [e2]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hR2 : K₁ / R ^ 2 + (∑ i, C i) / R ^ 2 = (K₁ + ∑ i, C i) / R ^ 2 := by ring
    rw [← hR2, Finset.sum_div]
    refine le_add_of_nonneg_of_le (by positivity) (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, one_mul, abs_mul, abs_inv, abs_of_pos hR, div_eq_mul_inv, mul_comm (C i),
      pow_two, mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hC i (R⁻¹ • y)) (by positivity)

private theorem annulus_le {f : Space → Space} (hf : Continuous f) (a : Space → ℝ) {M R : ℝ}
    (hM0 : 0 ≤ M) (hR : 0 < R) (hM : ∀ y, |a y| ≤ M) (hin : ∀ y, ‖y‖ < R → a y = 0)
    (hout : ∀ y, 2 * R < ‖y‖ → a y = 0) :
    eLpNorm (fun y => |a y| * ‖f y‖) 2 volume ≤
      ENNReal.ofReal (M * (2 * R)) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) *
        eLpNorm ({y : Space | R ≤ ‖y‖}.indicator f) 6 volume := by
  set B := Metric.closedBall (0 : Space) (2 * R) with hBdef
  set T := {y : Space | R ≤ ‖y‖}.indicator f with hTdef
  have hTm : AEStronglyMeasurable T volume :=
    hf.aestronglyMeasurable.indicator (measurableSet_le measurable_const continuous_norm.measurable)
  have hpt : ∀ y, ‖|a y| * ‖f y‖‖ ≤ B.indicator (M • fun y => ‖T y‖) y := by
    intro y
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases h' : ‖y‖ < R
      · rw [hin y h']
        simp only [abs_zero, zero_mul]
        positivity
      · have hT : T y = f y :=
          Set.indicator_of_mem (show y ∈ {y : Space | R ≤ ‖y‖} from not_lt.1 h') f
        rw [hT]
        exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy, hout y
        (lt_of_not_ge fun h => hy (mem_closedBall_zero_iff.2 h))]
      simp
  refine (eLpNorm_mono_real hpt).trans ?_
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  have hsm : AEStronglyMeasurable (M • fun y => ‖T y‖) (volume.restrict B) :=
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
  calc eLpNorm (M • fun y => ‖T y‖) 2 (volume.restrict B)
      ≤ eLpNorm (M • fun y => ‖T y‖) 6 (volume.restrict B) *
          (volume.restrict B) Set.univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hsm
    _ ≤ eLpNorm (M • fun y => ‖T y‖) 6 volume * volume B ^ (1 / 3 : ℝ) := by
        rw [Measure.restrict_apply_univ, hexp]
        gcongr
        exact Measure.restrict_le_self
    _ = ENNReal.ofReal M * eLpNorm T 6 volume *
          (ENNReal.ofReal (2 * R) * volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ)) := by
        rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_of_nonneg hM0, hvol]
    _ = _ := by
        rw [ENNReal.ofReal_mul hM0]
        ring

private theorem eLpNorm_two_eq {F : Space → ℝ} (hF : MemLp F 2 volume) :
    eLpNorm F 2 volume = ENNReal.ofReal (Real.sqrt (∫ y, F y ^ 2)) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
  have hfun : (fun y => ‖F y‖ ^ (2 : ℝ)) = fun y => F y ^ 2 := by
    funext y
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [h2, hfun, Real.sqrt_eq_rpow, one_div]

private theorem sqrt_sum_add_le (a b : Fin 3 → Space) :
    Real.sqrt (∑ i, ‖a i + b i‖ ^ 2) ≤ Real.sqrt (∑ i, ‖a i‖ ^ 2) + Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  have h := norm_add_le (WithLp.toLp 2 a : PiLp 2 (fun _ : Fin 3 => Space)) (WithLp.toLp 2 b)
  rw [← WithLp.toLp_add] at h
  simpa only [PiLp.norm_eq_of_L2, PiLp.toLp_apply, Pi.add_apply] using h


private theorem continuous_second_sum {g : Space → Space} (hg : ContDiff ℝ ∞ g) :
    Continuous (sumSecondPartialsAt g) := by
  have e : sumSecondPartialsAt g = fun x => ∑ i : Fin 3, pd (pd g i) i x := funext (sumSecondPartialsAt_eq hg)
  rw [e]
  exact continuous_finsetSum _ fun i _ => (contDiff_pd (contDiff_pd hg i) i).continuous

private theorem smooth_bound {u : Space → Space} (hu : ContDiff ℝ ∞ u) (h6 : MemLp u 6 volume)
    (hA : Integrable (fun y => ∑ i : Fin 3, ‖pd u i y‖ ^ 2))
    (hB : Integrable (fun y => ‖sumSecondPartialsAt u y‖ ^ 2)) (x : Space) :
    ‖u x‖ ^ 2 ≤ (1 / (2 * Real.pi)) * Real.sqrt (∫ y, ∑ i : Fin 3, ‖pd u i y‖ ^ 2) *
      Real.sqrt (∫ y, ‖sumSecondPartialsAt u y‖ ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := cutoff_bounds
  set V : ℝ≥0∞ := volume (Metric.ball (0 : Space) 1) ^ (1 / 3 : ℝ) with hV
  have hVt : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  set D : ℝ≥0∞ := ENNReal.ofReal (2 * K) * V with hD
  have hDt : D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt
  set T : ℕ → ℝ≥0∞ := fun n => eLpNorm ({y : Space | (n : ℝ) + 1 ≤ ‖y‖}.indicator u) 6 volume
    with hT
  have hTlim : Tendsto T atTop (𝓝 0) := tail_tendsto h6
  have hTt : ∀ n, T n ≠ ⊤ := fun n =>
    (lt_of_le_of_lt (eLpNorm_indicator_le _) h6.eLpNorm_lt_top).ne
  set p : Space → ℝ := fun y => Real.sqrt (∑ i : Fin 3, ‖pd u i y‖ ^ 2) with hp
  have hpc : Continuous p := Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    ((contDiff_pd hu i).continuous.norm.pow 2))
  have hpsq : ∀ y, p y ^ 2 = ∑ i : Fin 3, ‖pd u i y‖ ^ 2 := fun y =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  have hp2 : MemLp p 2 volume := (memLp_two_iff_integrable_sq_norm hpc.aestronglyMeasurable).2
    (hA.congr (ae_of_all _ fun y => by
      show _ = ‖p y‖ ^ 2
      rw [Real.norm_eq_abs, sq_abs, hpsq]))
  have hpE : eLpNorm p 2 volume =
      ENNReal.ofReal (Real.sqrt (∫ y, ∑ i : Fin 3, ‖pd u i y‖ ^ 2)) := by
    rw [eLpNorm_two_eq hp2]
    simp only [hpsq]
  set l : Space → ℝ := fun y => ‖sumSecondPartialsAt u y‖ with hl
  have hlc : Continuous l := (continuous_second_sum hu).norm
  have hl2 : MemLp l 2 volume := (memLp_two_iff_integrable_sq_norm hlc.aestronglyMeasurable).2
    (hB.congr (ae_of_all _ fun y => by
      show _ = ‖l y‖ ^ 2
      rw [Real.norm_of_nonneg (norm_nonneg _)]))
  have hlE : eLpNorm l 2 volume = ENNReal.ofReal (Real.sqrt (∫ y, ‖sumSecondPartialsAt u y‖ ^ 2)) :=
    eLpNorm_two_eq hl2
  have hEPt : eLpNorm p 2 volume ≠ ⊤ := hp2.eLpNorm_lt_top.ne
  have hELt : eLpNorm l 2 volume ≠ ⊤ := hl2.eLpNorm_lt_top.ne
  set EP := eLpNorm p 2 volume with hEP
  set EL := eLpNorm l 2 volume with hEL
  have hstep : ∀ n : ℕ, ‖x‖ ≤ (n : ℝ) + 1 → ENNReal.ofReal (‖u x‖ ^ 2) ≤
      ENNReal.ofReal (1 / (2 * Real.pi)) * (EP + 2 * (D * T n)) *
        (EL + ENNReal.ofReal (6 * K / ((n : ℝ) + 1)) * EP + D * T n) := by
    intro n hxn
    set R : ℝ := (n : ℝ) + 1 with hRdef
    have hR : 0 < R := by rw [hRdef]; positivity
    have hR1 : 1 ≤ R := by
      rw [hRdef]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    set χ := cutoff R with hχ
    have hχs : ContDiff ℝ ∞ χ := cutoff_contDiff R
    set w : Space → Space := fun y => χ y • u y with hw
    have hws : ContDiff ℝ ∞ w := hχs.smul hu
    have hwc : HasCompactSupport w :=
      HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * R)) fun y hy => by
        simp only [hw, hχ, cutoff_eq_zero hR
          (le_of_lt (lt_of_not_ge fun h => hy (mem_closedBall_zero_iff.2 h))), zero_smul]
    have hsup := supBound_test_field w hws hwc x
    have hwx : w x = u x := by simp only [hw, hχ, cutoff_eq_one hR hxn, one_smul]
    rw [hwx] at hsup
    have hpdχ : ∀ i y, |pd χ i y| ≤ ‖fderiv ℝ χ y‖ := fun i y => by
      have h := (fderiv ℝ χ y).le_opNorm (unitVector i)
      rw [norm_unitVector, mul_one, Real.norm_eq_abs] at h
      exact h
    have hpu : ∀ i y, ‖pd u i y‖ ≤ p y := fun i y =>
      (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum
        (f := fun j => ‖pd u j y‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)))
    set P : Space → ℝ := fun y => Real.sqrt (∑ i : Fin 3, ‖pd w i y‖ ^ 2) with hP
    set q : Space → ℝ := fun y => |‖fderiv ℝ χ y‖| * ‖u y‖ with hq
    have hPc : Continuous P := Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
      ((contDiff_pd hws i).continuous.norm.pow 2))
    have hqc : Continuous q := ((hχs.continuous_fderiv (by simp)).norm.abs).mul hu.continuous.norm
    have hPle : ∀ y, P y ≤ p y + 2 * q y := by
      intro y
      have e : ∀ i, pd w i y = χ y • pd u i y + pd χ i y • u y := fun i => by
        rw [hw, pd_smul (differentiable_of_smooth hχs) (differentiable_of_smooth hu)]
        exact add_comm _ _
      have h1 := sqrt_sum_add_le (fun i => χ y • pd u i y) (fun i => pd χ i y • u y)
      simp only [← e] at h1
      refine h1.trans (add_le_add ?_ ?_)
      · refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_smul, Real.norm_of_nonneg (cutoff_nonneg R y)]
        exact pow_le_pow_left₀ (mul_nonneg (cutoff_nonneg R y) (norm_nonneg _))
          (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one R y)) 2
      · have hi : ∀ i, ‖pd χ i y • u y‖ ^ 2 ≤ q y ^ 2 := fun i => by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          rw [norm_smul, Real.norm_eq_abs]
          simp only [hq, abs_norm]
          exact mul_le_mul_of_nonneg_right (hpdχ i y) (norm_nonneg _)
        calc Real.sqrt (∑ i : Fin 3, ‖pd χ i y • u y‖ ^ 2) ≤ Real.sqrt ((2 * q y) ^ 2) := by
              refine Real.sqrt_le_sqrt ?_
              calc ∑ i : Fin 3, ‖pd χ i y • u y‖ ^ 2 ≤ ∑ i : Fin 3, q y ^ 2 :=
                    Finset.sum_le_sum fun i _ => hi i
                _ = 3 * q y ^ 2 := by simp
                _ ≤ (2 * q y) ^ 2 := by nlinarith [sq_nonneg (q y)]
          _ = 2 * q y := Real.sqrt_sq (by positivity)
    have hqb : eLpNorm q 2 volume ≤ D * T n := by
      have h := annulus_le hu.continuous (fun y => ‖fderiv ℝ χ y‖) (M := K / R) (by positivity) hR
        (fun y => by rw [abs_norm]; exact (hK R hR y).1)
        (fun y hy => by simp only [hχ, fderiv_cutoff_eq_zero_of_lt hR hy, norm_zero])
        (fun y hy => by simp only [hχ, fderiv_cutoff_eq_zero_of_gt hR hy, norm_zero])
      have e : K / R * (2 * R) = 2 * K := by field_simp
      rw [e] at h
      exact h
    have hPb : eLpNorm P 2 volume ≤ EP + 2 * (D * T n) := by
      calc eLpNorm P 2 volume ≤ eLpNorm (fun y => p y + 2 * q y) 2 volume :=
            eLpNorm_mono_real fun y => by
              rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
              exact hPle y
        _ ≤ EP + eLpNorm (fun y => 2 * q y) 2 volume :=
            eLpNorm_add_le hpc.aestronglyMeasurable (hqc.const_mul 2).aestronglyMeasurable
              (by norm_num)
        _ ≤ EP + 2 * (D * T n) := by
            have e : eLpNorm (fun y => 2 * q y) 2 volume = 2 * eLpNorm q 2 volume := by
              rw [show (fun y => 2 * q y) = (2 : ℝ) • q from rfl, eLpNorm_const_smul,
                Real.enorm_of_nonneg (by norm_num), ENNReal.ofReal_ofNat]
            rw [e]
            gcongr
    have hP2 : MemLp P 2 volume := ⟨hPc.aestronglyMeasurable, lt_of_le_of_lt hPb
      (ENNReal.add_lt_top.2 ⟨hEPt.lt_top, ENNReal.mul_lt_top (by norm_num)
        (ENNReal.mul_lt_top hDt.lt_top (hTt n).lt_top)⟩)⟩
    have hPE : eLpNorm P 2 volume = ENNReal.ofReal
        (Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ w y (unitVector i)‖ ^ 2)) := by
      rw [eLpNorm_two_eq hP2]
      congr 2
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
    set s : Space → ℝ := fun y => ∑ i : Fin 3, pd (pd χ i) i y with hs
    set L : Space → ℝ := fun y => ‖sumSecondPartialsAt w y‖ with hL
    set r : Space → ℝ := fun y => |s y| * ‖u y‖ with hr
    have hsc : Continuous s :=
      continuous_finsetSum _ fun i _ => (contDiff_pd (contDiff_pd hχs i) i).continuous
    have hrc : Continuous r := hsc.abs.mul hu.continuous.norm
    have hLc : Continuous L := (continuous_second_sum hws).norm
    have hLle : ∀ y, L y ≤ l y + 6 * K / R * p y + r y := by
      intro y
      show ‖sumSecondPartialsAt (fun y => χ y • u y) y‖ ≤ _
      rw [second_sum_smul hχs hu y]
      have h1 : ‖(∑ i : Fin 3, pd (pd χ i) i y) • u y‖ = r y := by
        rw [norm_smul, Real.norm_eq_abs]
      have h3 : ‖χ y • sumSecondPartialsAt u y‖ ≤ l y := by
        rw [norm_smul, Real.norm_of_nonneg (cutoff_nonneg R y)]
        exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one R y)
      have h2 : ‖(2 : ℝ) • ∑ i : Fin 3, pd χ i y • pd u i y‖ ≤ 6 * K / R * p y := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have hb : ‖∑ i : Fin 3, pd χ i y • pd u i y‖ ≤ ∑ i : Fin 3, K / R * p y :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul ((hpdχ i y).trans (hK R hR y).1) (hpu i y) (norm_nonneg _)
              (by positivity))
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat] at hb
        have e : 6 * K / R * p y = 2 * (3 * (K / R * p y)) := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left hb (by norm_num)
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      rw [h1]
      linarith
    have hrb : eLpNorm r 2 volume ≤ D * T n := by
      have h := annulus_le hu.continuous s (M := K / R ^ 2) (by positivity) hR
        (fun y => (hK R hR y).2)
        (fun y hy => by
          have hc : χ =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
            filter_upwards [Metric.isOpen_ball.mem_nhds
              (show y ∈ Metric.ball (0 : Space) R by simpa using hy)] with z hz
            exact cutoff_eq_one hR (mem_ball_zero_iff.1 hz).le
          exact Finset.sum_eq_zero fun i _ => pd_pd_eq_zero hc i i)
        (fun y hy => by
          have hc : χ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
            filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
            exact cutoff_eq_zero hR (le_of_lt hz)
          exact Finset.sum_eq_zero fun i _ => pd_pd_eq_zero hc i i)
      refine h.trans ?_
      have e : K / R ^ 2 * (2 * R) ≤ 2 * K := by
        have e1 : K / R ^ 2 * (2 * R) = 2 * K / R := by field_simp
        rw [e1]
        exact div_le_self (by positivity) hR1
      exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal e) le_rfl) le_rfl
    have hLb : eLpNorm L 2 volume ≤ EL + ENNReal.ofReal (6 * K / R) * EP + D * T n := by
      calc eLpNorm L 2 volume ≤ eLpNorm (fun y => l y + 6 * K / R * p y + r y) 2 volume :=
            eLpNorm_mono_real fun y => by
              rw [Real.norm_of_nonneg (norm_nonneg _)]
              exact hLle y
        _ ≤ eLpNorm (fun y => l y + 6 * K / R * p y) 2 volume + eLpNorm r 2 volume :=
            eLpNorm_add_le (hlc.add (hpc.const_mul _)).aestronglyMeasurable
              hrc.aestronglyMeasurable (by norm_num)
        _ ≤ EL + eLpNorm (fun y => 6 * K / R * p y) 2 volume + eLpNorm r 2 volume := by
            gcongr
            exact eLpNorm_add_le hlc.aestronglyMeasurable (hpc.const_mul _).aestronglyMeasurable
              (by norm_num)
        _ ≤ EL + ENNReal.ofReal (6 * K / R) * EP + D * T n := by
            have e : eLpNorm (fun y => 6 * K / R * p y) 2 volume = ENNReal.ofReal (6 * K / R) * EP := by
              rw [show (fun y => 6 * K / R * p y) = (6 * K / R) • p from rfl, eLpNorm_const_smul,
                Real.enorm_of_nonneg (by positivity)]
            rw [e]
            gcongr
    have hL2 : MemLp L 2 volume := ⟨hLc.aestronglyMeasurable, lt_of_le_of_lt hLb
      (ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hELt.lt_top,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEPt.lt_top⟩,
        ENNReal.mul_lt_top hDt.lt_top (hTt n).lt_top⟩)⟩
    have hLE : eLpNorm L 2 volume =
        ENNReal.ofReal (Real.sqrt (∫ y, ‖sumSecondPartialsAt w y‖ ^ 2)) := eLpNorm_two_eq hL2
    calc ENNReal.ofReal (‖u x‖ ^ 2) ≤ ENNReal.ofReal ((1 / (2 * Real.pi)) *
          Real.sqrt (∫ y, ∑ i : Fin 3, ‖fderiv ℝ w y (unitVector i)‖ ^ 2) *
          Real.sqrt (∫ y, ‖sumSecondPartialsAt w y‖ ^ 2)) := ENNReal.ofReal_le_ofReal hsup
      _ = ENNReal.ofReal (1 / (2 * Real.pi)) * eLpNorm P 2 volume * eLpNorm L 2 volume := by
          rw [hPE, hLE, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by gcongr
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (2 * Real.pi)) * (EP + 2 * (D * T n)) *
      (EL + ENNReal.ofReal (6 * K / ((n : ℝ) + 1)) * EP + D * T n)) atTop
      (𝓝 (ENNReal.ofReal (1 / (2 * Real.pi)) * EP * EL)) := by
    have hDT : Tendsto (fun n : ℕ => D * T n) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hTlim (Or.inr hDt)
    have h1 : Tendsto (fun n : ℕ => EP + 2 * (D * T n)) atTop (𝓝 EP) := by
      simpa using tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hDT (Or.inr (by norm_num)))
    have hK6 : Tendsto (fun n : ℕ => ENNReal.ofReal (6 * K / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => 6 * K / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      simpa using ENNReal.tendsto_ofReal h
    have h2 : Tendsto (fun n : ℕ => EL + ENNReal.ofReal (6 * K / ((n : ℝ) + 1)) * EP + D * T n) atTop
        (𝓝 EL) := by
      simpa using (tendsto_const_nhds.add (ENNReal.Tendsto.mul_const hK6 (Or.inr hEPt))).add hDT
    exact ENNReal.Tendsto.mul (ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top))
      (Or.inr hELt) h2 (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEPt))
  have hfin : ENNReal.ofReal (‖u x‖ ^ 2) ≤ ENNReal.ofReal (1 / (2 * Real.pi)) * EP * EL := by
    refine ge_of_tendsto hlim ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact hstep n (by linarith)
  rw [hpE, hlE, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfin
  exact hfin

end FracInternal.SupNormBound

namespace CellCert.Reduction

open SteadyCert FracInternal.SupNormBound
open Breakdown.Freq.Internal.EmbedNegSsp

theorem supNorm : SupNormStatement := by
  intro m v G H hf
  have hloc : LocallyIntegrable v volume := hf.velocity_six.locallyIntegrable (by norm_num)
  have hGm : ∀ i, AEStronglyMeasurable (fun y => G y (unitVector i)) volume := fun i =>
    (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
      hf.measurable_gradient
  have hGle : ∀ i y, ‖G y (unitVector i)‖ ^ 2 ≤ entrySq (G y) := fun i y =>
    Finset.single_le_sum (f := fun j => ‖G y (unitVector j)‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  have hGloc : ∀ i, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i =>
    ((memLp_two_iff_integrable_sq_norm (hGm i)).2 (hf.gradient_two.mono' ((hGm i).norm.pow 2)
      (ae_of_all _ fun y => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hGle i y))).locallyIntegrable (by norm_num)
  set S : Space → ℝ := fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2
    with hS
  have hSi : Integrable S := hf.second_two
  have hHm : ∀ j i, AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector i)) volume :=
    fun j i => (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
      ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous.comp_aestronglyMeasurable
        hf.measurable_second)
  have hHle : ∀ j i y, ‖H y (unitVector j) (unitVector i)‖ ^ 2 ≤ S y := fun j i y =>
    (Finset.single_le_sum (f := fun l => ‖H y (unitVector j) (unitVector l)‖ ^ 2)
      (fun l _ => by positivity) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun k => ∑ l : Fin 3, ‖H y (unitVector k) (unitVector l)‖ ^ 2)
        (fun k _ => Finset.sum_nonneg fun l _ => by positivity) (Finset.mem_univ j))
  have hHloc : ∀ j i, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume :=
    fun j i => ((memLp_two_iff_integrable_sq_norm (hHm j i)).2 (hSi.mono' ((hHm j i).norm.pow 2)
      (ae_of_all _ fun y => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact hHle j i y))).locallyIntegrable (by norm_num)
  set tr : Space → Space := fun y => secondTrace (H y) with htr
  have htrm : AEStronglyMeasurable tr volume := by
    have e : tr = fun y => ∑ i : Fin 3, H y (unitVector i) (unitVector i) := rfl
    rw [e]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => hHm i i
  have htr2 : Integrable (fun y => ‖tr y‖ ^ 2) := by
    refine (hSi.const_mul 3).mono' (htrm.norm.pow 2) (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : ‖tr y‖ ≤ ∑ i : Fin 3, ‖H y (unitVector i) (unitVector i)‖ := norm_sum_le _ _
    have h2 : ∑ i : Fin 3, ‖H y (unitVector i) (unitVector i)‖ ^ 2 ≤ S y :=
      Finset.sum_le_sum fun i _ => Finset.single_le_sum
        (f := fun l => ‖H y (unitVector i) (unitVector l)‖ ^ 2) (fun l _ => by positivity)
        (Finset.mem_univ i)
    have h3 : (∑ i : Fin 3, ‖H y (unitVector i) (unitVector i)‖) ^ 2 ≤
        3 * ∑ i : Fin 3, ‖H y (unitVector i) (unitVector i)‖ ^ 2 := by
      simp only [Fin.sum_univ_three]
      nlinarith [sq_nonneg (‖H y (unitVector 0) (unitVector 0)‖ - ‖H y (unitVector 1) (unitVector 1)‖),
        sq_nonneg (‖H y (unitVector 0) (unitVector 0)‖ - ‖H y (unitVector 2) (unitVector 2)‖),
        sq_nonneg (‖H y (unitVector 1) (unitVector 1)‖ - ‖H y (unitVector 2) (unitVector 2)‖)]
    calc ‖tr y‖ ^ 2 ≤ (∑ i : Fin 3, ‖H y (unitVector i) (unitVector i)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ 3 * ∑ i : Fin 3, ‖H y (unitVector i) (unitVector i)‖ ^ 2 := h3
      _ ≤ 3 * S y := mul_le_mul_of_nonneg_left h2 (by norm_num)
  let φ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]
      linarith⟩
  set vn : ℕ → Space → Space := fun n =>
    (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v with hvn
  have hρi : ∀ n, Integrable ((φ n).normed volume) := fun n => (φ n).integrable_normed
  have hwc : ∀ n, ContDiff ℝ ∞ (vn n) :=
    fun n => ((φ n).hasCompactSupport_normed).contDiff_convolution_left _ (φ n).contDiff_normed hloc
  have hgi : Integrable (fun y => ‖v y‖ ^ 6) :=
    (memLp_six_iff hf.measurable_velocity).1 hf.velocity_six
  have hw6 : ∀ n, MemLp (vn n) 6 volume := by
    intro n
    have hm : AEStronglyMeasurable (vn n) volume := (hwc n).continuous.aestronglyMeasurable
    refine (memLp_six_iff hm).2 ?_
    exact ((hρi n).integrable_convolution _ hgi).mono' (hm.norm.pow 6) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact normPow_conv_le (φ n) v _ hgi 6 (by norm_num) (fun z => le_rfl) y)
  have hpd : ∀ n i, pd (vn n) i =
      (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => G y (unitVector i)) :=
    fun n i => funext fun y =>
      mollify_fderiv_apply (φ n) v (fun j y => G y (unitVector j)) hloc hf.weak_gradient y i
  have hssp : ∀ n y, sumSecondPartialsAt (vn n) y =
      ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] tr) y := by
    intro n y
    rw [sumSecondPartialsAt_eq (hwc n)]
    have e : ∀ i, pd (pd (vn n) i) i y = ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun z => H z (unitVector i) (unitVector i))) y := fun i => by
      rw [hpd n i]
      exact mollify_fderiv_apply (φ n) (fun z => G z (unitVector i))
        (fun j z => H z (unitVector j) (unitVector i)) (hGloc i)
        (fun ψ hψ j => hf.weak_second ψ hψ i j) y i
    simp only [e]
    exact conv_sum_eq (φ n) (fun i z => H z (unitVector i) (unitVector i)) (fun i => hHloc i i) y
  have hEpt : ∀ n y, ∑ i : Fin 3, ‖pd (vn n) i y‖ ^ 2 ≤
      ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => entrySq (G z)) y := by
    intro n y
    simp only [hpd n]
    exact (Finset.sum_le_sum fun j _ => normPow_conv_le (φ n) (fun z => G z (unitVector j)) _
      hf.gradient_two 2 (by norm_num) (hGle j) y).trans
      (conv_sum_le (φ n) (fun j z => G z (unitVector j)) _ hf.gradient_two (fun z => le_rfl) y)
  have hSGi : ∀ n, Integrable ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun z => entrySq (G z)) := fun n => (hρi n).integrable_convolution _ hf.gradient_two
  have hEi : ∀ n, Integrable (fun y => ∑ i : Fin 3, ‖pd (vn n) i y‖ ^ 2) := fun n =>
    (hSGi n).mono' (continuous_finsetSum _ fun i _ =>
      ((contDiff_pd (hwc n) i).continuous.norm.pow 2)).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
        exact hEpt n y)
  have hEle : ∀ n, ∫ y, ∑ i : Fin 3, ‖pd (vn n) i y‖ ^ 2 ≤ ∫ z, entrySq (G z) := by
    intro n
    refine (integral_mono (hEi n) (hSGi n) (hEpt n)).trans_eq ?_
    rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hρi n) hf.gradient_two]
    simp [ContDiffBump.integral_normed]
  have hLpt : ∀ n y, ‖sumSecondPartialsAt (vn n) y‖ ^ 2 ≤
      ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖tr z‖ ^ 2) y := by
    intro n y
    rw [hssp n y]
    exact normPow_conv_le (φ n) tr _ htr2 2 (by norm_num) (fun z => le_rfl) y
  have hSTi : ∀ n, Integrable ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun z => ‖tr z‖ ^ 2) := fun n => (hρi n).integrable_convolution _ htr2
  have hLi : ∀ n, Integrable (fun y => ‖sumSecondPartialsAt (vn n) y‖ ^ 2) := fun n =>
    (hSTi n).mono' ((continuous_second_sum (hwc n)).norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hLpt n y)
  have hLle : ∀ n, ∫ y, ‖sumSecondPartialsAt (vn n) y‖ ^ 2 ≤ ∫ z, ‖tr z‖ ^ 2 := by
    intro n
    refine (integral_mono (hLi n) (hSTi n) (hLpt n)).trans_eq ?_
    rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hρi n) htr2]
    simp [ContDiffBump.integral_normed]
  have hbound : ∀ n y, ‖vn n y‖ ^ 2 ≤ (1 / (2 * Real.pi)) * Real.sqrt (∫ z, entrySq (G z)) *
      Real.sqrt (∫ z, ‖tr z‖ ^ 2) := by
    intro n y
    refine (smooth_bound (hwc n) (hw6 n) (hEi n) (hLi n) y).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hEle n)) (by positivity))
      (Real.sqrt_le_sqrt (hLle n)) (Real.sqrt_nonneg _) (by positivity)
  have hae : ∀ᵐ y ∂volume, Tendsto (fun n => vn n y) atTop (𝓝 (v y)) := by
    refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := φ) (K := 2) ?_ ?_ hloc
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · refine Eventually.of_forall fun n => le_of_eq ?_
      show 1 / ((n : ℝ) + 1) = 2 * (1 / (2 * ((n : ℝ) + 1)))
      field_simp
  filter_upwards [hae] with y hy
  exact le_of_tendsto' ((hy.norm).pow 2) fun n => hbound n y

end CellCert.Reduction

end Breakdown
