import Breakdown.FracCert.StQuadratic
import Breakdown.FreqTr.GradSixDecay

open scoped ContDiff ENNReal NNReal
open MeasureTheory Filter Topology
open scoped Convolution

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace QuadraticSquareInternal

open Breakdown.Freq.Internal.GradSixDecay

private theorem normPow_conv_le (φ : ContDiffBump (0 : Space)) (f : Space → Space)
    (k : ℕ) (hk : 1 ≤ k) (hI : Integrable (fun z => ‖f z‖ ^ k)) (y : Space) :
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
    have hIt : Integrable (fun t => ‖f (y - t)‖ ^ k) := hI.comp_sub_left y
    have hgi : Integrable (fun t => ‖f (y - t)‖ ^ k) μ := by
      rw [hμ, integrable_withDensity_iff_integrable_smul hdm]
      refine (hIt.const_mul C).mono' ?_ (ae_of_all _ fun t => ?_)
      · exact (hdm.coe_nnreal_real.aestronglyMeasurable).smul hIt.aestronglyMeasurable
      · simp only [hd, NNReal.smul_def, Real.coe_toNNReal _ (hρ0 t), smul_eq_mul, norm_mul,
          Real.norm_eq_abs, abs_of_nonneg (hρ0 t), abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖f (y - t)‖ ^ k)]
        have h1 : ρ t ≤ C := by simpa [Real.norm_eq_abs, abs_of_nonneg (hρ0 t)] using hC t
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hconv : ConvexOn ℝ Set.univ (fun x : Space => ‖x‖ ^ k) :=
      (convexOn_norm convex_univ).pow (fun x _ => norm_nonneg x) k
    exact hconv.map_integral_le ((continuous_norm.pow k).continuousOn) isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) hfi hgi
  · rw [integral_undef hfi, norm_zero, zero_pow (by omega)]
    exact integral_nonneg fun t => by positivity

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

private theorem cutoff_six {f : Space → Space} (hf : ContDiff ℝ ∞ f) {K R : ℝ} (hK0 : 0 ≤ K)
    (hR : 0 < R) (hK : ∀ y, ‖fderiv ℝ (cutoff R) y‖ ≤ K / R) :
    eLpNorm (cutoff R • f) 6 volume ≤
      (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞) *
        (eLpNorm (fderiv ℝ f) 2 volume + ENNReal.ofReal (K / R) * eLpNorm f 2 volume) := by
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
    _ ≤ eLpNorm (fderiv ℝ f) 2 volume + ENNReal.ofReal (K / R) * eLpNorm f 2 volume := by
        rw [eLpNorm_norm]
        refine add_le_add le_rfl ?_
        calc eLpNorm (fun y => ‖fderiv ℝ (cutoff R) y‖ * ‖f y‖) 2 volume
            ≤ eLpNorm ((K / R) • fun y => ‖f y‖) 2 volume := eLpNorm_mono_real fun y => by
              simp only [Pi.smul_apply, smul_eq_mul]
              rw [Real.norm_of_nonneg (by positivity)]
              exact mul_le_mul_of_nonneg_right (hK y) (norm_nonneg _)
          _ = ENNReal.ofReal (K / R) * eLpNorm f 2 volume := by
              rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_of_nonneg (by positivity)]

private theorem smooth_six {f : Space → Space} (hf : ContDiff ℝ ∞ f) (h2 : eLpNorm f 2 volume ≠ ⊤) :
    eLpNorm f 6 volume ≤
      (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume := by
  obtain ⟨K, hK0, hK⟩ := exists_fderiv_cutoff_le
  have hR : ∀ n : ℕ, 0 < (n : ℝ) + 1 := fun n => by positivity
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
  have h1 : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (K / ((n : ℝ) + 1)) * eLpNorm f 2 volume) atTop
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr h2)
  have hT := ENNReal.Tendsto.const_mul
    (tendsto_const_nhds (x := eLpNorm (fderiv ℝ f) 2 volume) |>.add h0)
    (Or.inr ENNReal.coe_ne_top)
    (a := (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞))
  rw [add_zero] at hT
  rw [← hT.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n =>
    cutoff_six hf hK0 (hR n) (hK _ (hR n)))

private theorem six_of_weak (g : Space → Space) (c : Fin 3 → Space → Space)
    (hg2 : MemLp g 2 volume) (hc : ∀ j, Integrable (fun y => ‖c j y‖ ^ 2))
    (hw : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∀ j : Fin 3,
      ∫ y, (fderiv ℝ ψ y (unitVector j)) • g y = -∫ y, ψ y • c j y) :
    MemLp g 6 volume := by
  have hloc : LocallyIntegrable g volume := hg2.locallyIntegrable (by norm_num)
  have hgi : Integrable (fun y => ‖g y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hg2.1).1 hg2
  let φ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]
      linarith⟩
  have hρi : ∀ n, Integrable ((φ n).normed volume) := fun n => (φ n).integrable_normed
  have hwc : ∀ n, ContDiff ℝ ∞ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
    fun n => ((φ n).hasCompactSupport_normed).contDiff_convolution_left _ (φ n).contDiff_normed hloc
  have hw2 : ∀ n, MemLp ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 2 volume := by
    intro n
    have hm : AEStronglyMeasurable ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) volume :=
      (hwc n).continuous.aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    exact ((hρi n).integrable_convolution _ hgi).mono' (hm.norm.pow 2) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact normPow_conv_le (φ n) g 2 (by norm_num) hgi y)
  have hEpt : ∀ n y, ∑ i : Fin 3,
      ‖fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y (unitVector i)‖ ^ 2 ≤
      ∑ j : Fin 3, ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun z => ‖c j z‖ ^ 2) y := by
    intro n y
    simp only [mollify_fderiv_apply (φ n) g c hloc hw y]
    exact Finset.sum_le_sum fun j _ => normPow_conv_le (φ n) _ 2 (by norm_num) (hc j) y
  have hSi : ∀ n, Integrable (fun y => ∑ j : Fin 3, ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun z => ‖c j z‖ ^ 2) y) := fun n =>
    integrable_finsetSum _ fun j _ => (hρi n).integrable_convolution _ (hc j)
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
      ∫ y, ∑ j : Fin 3, ‖c j y‖ ^ 2 := by
    intro n
    refine (integral_mono (hEi n) (hSi n) (hEpt n)).trans_eq ?_
    rw [integral_finsetSum _ fun j _ => (hρi n).integrable_convolution _ (hc j)]
    rw [integral_finsetSum _ fun j _ => hc j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hρi n) (hc j)]
    simp [ContDiffBump.integral_normed]
  set S := (SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : NNReal) : ℝ) : ℝ≥0∞) with hSdef
  set B := S * ENNReal.ofReal (3 * Real.sqrt (∫ y, ∑ j : Fin 3, ‖c j y‖ ^ 2)) with hB
  have hbound : ∀ n, eLpNorm ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 6 volume ≤ B :=
    fun n => (smooth_six (hwc n) (hw2 n).eLpNorm_ne_top).trans (mul_le_mul_right
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
  have hle : eLpNorm g 6 volume ≤ B :=
    hlim.trans ((Filter.liminf_le_liminf (Eventually.of_forall hbound)).trans (le_of_eq (liminf_const B)))
  exact ⟨hg2.1, lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)⟩

private theorem sq_mul_sq_le {a b : ℝ} (ha : 0 ≤ a) :
    a ^ 2 * b ^ 2 ≤ a ^ 2 + a ^ 6 + b ^ 6 := by
  have h6a : 0 ≤ a ^ 6 := by positivity
  have h6b : 0 ≤ b ^ 6 := by positivity
  have h2a : 0 ≤ a ^ 2 := by positivity
  rcases le_total (b ^ 2) a with h | h
  · have h1 : a ^ 2 * b ^ 2 ≤ a ^ 2 * a := mul_le_mul_of_nonneg_left h h2a
    rcases le_total a 1 with h' | h'
    · have : a ^ 2 * a ≤ a ^ 2 * 1 := mul_le_mul_of_nonneg_left h' h2a
      linarith
    · have : a ^ 2 * a ≤ a ^ 6 := by
        have e : a ^ 2 * a = a ^ 3 := by ring
        rw [e]
        exact pow_le_pow_right₀ h' (by norm_num)
      linarith
  · have h1 : a ^ 2 ≤ (b ^ 2) ^ 2 := pow_le_pow_left₀ ha h 2
    have h2 : a ^ 2 * b ^ 2 ≤ (b ^ 2) ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
    have e : (b ^ 2) ^ 2 * b ^ 2 = b ^ 6 := by ring
    linarith

end QuadraticSquareInternal

open QuadraticSquareInternal

theorem quadraticSquareIntegrable : QuadraticSquareIntegrableStatement := by
  intro m v G H hf
  have hcolm : ∀ j : Fin 3, AEStronglyMeasurable (fun y => G y (unitVector j)) volume := fun j =>
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable
      hf.measurable_gradient
  have hcol2 : ∀ j : Fin 3, MemLp (fun y => G y (unitVector j)) 2 volume := by
    intro j
    refine (memLp_two_iff_integrable_sq_norm (hcolm j)).2 ?_
    refine hf.gradient_two.mono' ((hcolm j).norm.pow 2) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ j)
  have hHc : ∀ k j : Fin 3, Integrable (fun y => ‖H y (unitVector k) (unitVector j)‖ ^ 2) := by
    intro k j
    have hm : AEStronglyMeasurable (fun y => H y (unitVector k) (unitVector j)) volume :=
      ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
        (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector k)).continuous).comp_aestronglyMeasurable
        hf.measurable_second
    refine hf.second_two.mono' (hm.norm.pow 2) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖H y (unitVector k) (unitVector j)‖ ^ 2
        ≤ ∑ j' : Fin 3, ‖H y (unitVector k) (unitVector j')‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖H y (unitVector k) (unitVector j')‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i : Fin 3, ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ k)
  have hcol6 : ∀ j : Fin 3, MemLp (fun y => G y (unitVector j)) 6 volume := fun j =>
    six_of_weak _ (fun k y => H y (unitVector k) (unitVector j)) (hcol2 j) (fun k => hHc k j)
      (fun ψ hψ k => hf.weak_second ψ hψ j k)
  have hi2 : ∀ j : Fin 3, Integrable (fun y => ‖G y (unitVector j)‖ ^ 2) := fun j =>
    (memLp_two_iff_integrable_sq_norm (hcol2 j).1).1 (hcol2 j)
  have hi6 : ∀ j : Fin 3, Integrable (fun y => ‖G y (unitVector j)‖ ^ 6) := fun j => by
    have h : MemLp (fun y => G y (unitVector j)) ((6 : ℕ) : ℝ≥0∞) volume := by exact_mod_cast hcol6 j
    exact h.integrable_norm_pow (by norm_num)
  have hv6 : Integrable (fun y => ‖v y‖ ^ 6) := by
    have h : MemLp v ((6 : ℕ) : ℝ≥0∞) volume := by exact_mod_cast hf.velocity_six
    exact h.integrable_norm_pow (by norm_num)
  have hm : AEStronglyMeasurable (fun y => G y (v y)) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hf.measurable_gradient.prodMk hf.measurable_velocity)
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have hdom : Integrable (fun y => 9 * ∑ i : Fin 3,
      (‖G y (unitVector i)‖ ^ 2 + ‖G y (unitVector i)‖ ^ 6 + ‖v y‖ ^ 6)) :=
    (integrable_finsetSum _ fun i _ => ((hi2 i).add (hi6 i)).add hv6).const_mul 9
  refine hdom.mono' (hm.norm.pow 2) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  set s := ∑ i : Fin 3, ‖G y (unitVector i)‖ ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => by positivity
  have h1 : ‖G y (v y)‖ ≤ 3 * Real.sqrt s * ‖v y‖ :=
    ((G y).le_opNorm (v y)).trans (mul_le_mul_of_nonneg_right (Breakdown.Freq.Internal.GradSixDecay.opNorm_le_three_mul (G y)) (norm_nonneg _))
  have h2 : ‖G y (v y)‖ ^ 2 ≤ 9 * (s * ‖v y‖ ^ 2) := by
    calc ‖G y (v y)‖ ^ 2 ≤ (3 * Real.sqrt s * ‖v y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = 9 * (s * ‖v y‖ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hs0]
        ring
  refine h2.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  rw [hs, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => sq_mul_sq_le (norm_nonneg _)

end SteadyCert

end Breakdown
