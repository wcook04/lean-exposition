import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FracCert.InverseSquare

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal NNReal Convolution

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace MollifySecondApproxInternal

def kernelBump (n : ℕ) : ContDiffBump (0 : Space) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]
    linarith⟩

theorem kernelBump_rOut : Tendsto (fun n => (kernelBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem kernelBump_rOut_le (n : ℕ) : (kernelBump n).rOut ≤ 1 := by
  show 1 / ((n : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem normPow_conv_le (φ : ContDiffBump (0 : Space)) (f : Space → Space)
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

theorem conv_sq_integral_le (φ : ContDiffBump (0 : Space)) (f : Space → Space)
    (hfl : LocallyIntegrable f volume) (hI : Integrable (fun z => ‖f z‖ ^ 2)) :
    Integrable (fun y => ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ 2) ∧
    ∫ y, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ 2 ≤ ∫ y, ‖f y‖ ^ 2 := by
  have hρi : Integrable (φ.normed volume) := φ.integrable_normed
  have hc : Integrable (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖f z‖ ^ 2) :=
    hρi.integrable_convolution _ hI
  have hm : AEStronglyMeasurable (fun y => ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ 2)
      volume :=
    ((φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hfl
        (n := 0)).continuous.norm.pow 2).aestronglyMeasurable
  have hb : ∀ y, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ 2 ≤
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖f z‖ ^ 2) y :=
    fun y => normPow_conv_le φ f 2 (by norm_num) hI y
  have hi := hc.mono' hm (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb y)
  refine ⟨hi, (integral_mono hi hc hb).trans_eq ?_⟩
  rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hρi hI]
  simp [ContDiffBump.integral_normed]


theorem conv_sq_tendsto (f : Space → Space) (hfm : AEStronglyMeasurable f volume)
    (hI : Integrable (fun z => ‖f z‖ ^ 2)) :
    Tendsto (fun n => ∫ y, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y - f y‖ ^ 2)
      atTop (𝓝 0) := by
  have hf2 : MemLp f 2 volume := (memLp_two_iff_integrable_sq_norm hfm).2 hI
  have hfl : LocallyIntegrable f volume := hf2.locallyIntegrable (by norm_num)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ0 : 0 < ε / 20 := by positivity
  have hf2' : MemLp f (ENNReal.ofReal 2) volume := by simpa using hf2
  obtain ⟨g, hgc, hgε, hgcont, hg2⟩ := hf2'.exists_hasCompactSupport_integral_rpow_sub_le two_pos hδ0
  have hgε' : ∫ x, ‖f x - g x‖ ^ 2 ≤ ε / 20 := by simpa [Real.rpow_two] using hgε
  have hg2' : MemLp g 2 volume := by simpa using hg2
  have hgl : LocallyIntegrable g volume := hgcont.locallyIntegrable
  have hfg : Integrable (fun x => ‖f x - g x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (hfm.sub hgcont.aestronglyMeasurable)).1 (hf2.sub hg2')
  obtain ⟨M, hM⟩ := hgcont.bounded_above_of_compact_support hgc
  have hK : IsCompact (Metric.cthickening 1 (tsupport g)) := hgc.cthickening
  have hKm : MeasurableSet (Metric.cthickening 1 (tsupport g)) := hK.measurableSet
  have cb : ∀ n x, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x‖ ≤ 2 * M ∧
      (x ∉ Metric.cthickening 1 (tsupport g) →
        ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x = 0) := by
    intro n x
    constructor
    · have h := (kernelBump n).dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := 2 * M)
        hgcont.aestronglyMeasurable (fun t _ => (dist_le_norm_add_norm _ _).trans (by linarith [hM t, hM x]))
      rwa [dist_eq_norm] at h
    · intro hx
      have hz : ∀ t, dist x t < 1 → g t = 0 := by
        intro t ht
        refine image_eq_zero_of_notMem_tsupport fun hm => hx ?_
        exact Metric.mem_cthickening_of_dist_le x t 1 _ hm ht.le
      have h := (kernelBump n).dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := 0)
        hgcont.aestronglyMeasurable (fun t ht => by
          rw [hz t ((dist_comm x t ▸ Metric.mem_ball.1 ht).trans_le (kernelBump_rOut_le n)), hz x (by simp)]
          simp)
      rw [dist_le_zero] at h
      rw [h, sub_self]
  have hcc : ∀ n, Continuous ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := fun n =>
    ((kernelBump n).hasCompactSupport_normed.contDiff_convolution_left _ (kernelBump n).contDiff_normed hgl
      (n := 0)).continuous
  have hBm : ∀ n, AEStronglyMeasurable (fun y =>
      ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2) volume := fun n =>
    (((hcc n).sub hgcont).norm.pow 2).aestronglyMeasurable
  have hFi : Integrable (fun y => (Metric.cthickening 1 (tsupport g)).indicator (fun _ => (2 * M) ^ 2) y) :=
    (continuousOn_const.integrableOn_compact hK).integrable_indicator hKm
  have hBb : ∀ n, ∀ᵐ y ∂volume,
      ‖‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2‖ ≤
        (Metric.cthickening 1 (tsupport g)).indicator (fun _ => (2 * M) ^ 2) y := fun n =>
    ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      by_cases hy : y ∈ Metric.cthickening 1 (tsupport g)
      · rw [Set.indicator_of_mem hy]
        exact pow_le_pow_left₀ (norm_nonneg _) (cb n y).1 2
      · rw [Set.indicator_of_notMem hy, (cb n y).2 hy, norm_zero]
        norm_num
  have hBi : ∀ n, Integrable (fun y =>
      ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2) := fun n =>
    hFi.mono' (hBm n) (hBb n)
  have hT : Tendsto (fun n => ∫ y,
      ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) _ hBm hFi hBb
      (ae_of_all _ fun y => by
        have := (((ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) kernelBump_rOut hgcont y).sub_const
          (g y)).norm).pow 2
        simpa using this)
    simpa using h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hT.eventually (Iic_mem_nhds hδ0))
  refine ⟨N, fun n hn => ?_⟩
  have hB := hN n hn
  simp only [Set.mem_Iic] at hB
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => by positivity)]
  have hex1 : ConvolutionExists ((kernelBump n).normed volume) (fun x => f x - g x)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    (kernelBump n).hasCompactSupport_normed.convolutionExists_left _ (kernelBump n).continuous_normed
      (hfl.sub hgl)
  have hex2 : ConvolutionExists ((kernelBump n).normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    (kernelBump n).hasCompactSupport_normed.convolutionExists_left _ (kernelBump n).continuous_normed hgl
  have hsplit : ∀ y, ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y - f y =
      ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) y +
        (((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y) + (g y - f y) := by
    intro y
    have h := (hex1 y).distrib_add (hex2 y)
    have e : ((fun x => f x - g x) + g) = f := by
      funext x
      simp
    rw [e] at h
    rw [h]
    abel
  obtain ⟨hAi, hAle⟩ := conv_sq_integral_le (kernelBump n) (fun x => f x - g x) (hfl.sub hgl) hfg
  have hCi : Integrable (fun y => ‖g y - f y‖ ^ 2) := by
    refine hfg.congr (ae_of_all _ fun y => ?_)
    simp only [norm_sub_rev]
  have hsum : Integrable (fun y =>
      3 * (‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) y‖ ^ 2 +
        ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2 +
          ‖g y - f y‖ ^ 2)) :=
    ((hAi.add (hBi n)).add hCi).const_mul 3
  have hle : ∀ y, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y - f y‖ ^ 2 ≤
      3 * (‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) y‖ ^ 2 +
        ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2 +
          ‖g y - f y‖ ^ 2) := by
    intro y
    rw [hsplit y]
    have h1 := norm_add₃_le (a := ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun x => f x - g x) y) (b := ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y)
      (c := g y - f y)
    have h0 := norm_nonneg (((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) y
      + (((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y) + (g y - f y))
    nlinarith [norm_nonneg (((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) y),
      norm_nonneg (((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y),
      norm_nonneg (g y - f y),
      sq_nonneg (‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) y‖ -
        ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖),
      sq_nonneg (‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) y‖ -
        ‖g y - f y‖),
      sq_nonneg (‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ - ‖g y - f y‖)]
  have hCle : ∫ y, ‖g y - f y‖ ^ 2 ≤ ε / 20 := by
    have e : (fun y => ‖g y - f y‖ ^ 2) = fun y => ‖f y - g y‖ ^ 2 := by
      funext y
      rw [norm_sub_rev]
    rw [e]
    exact hgε'
  calc ∫ y, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y - f y‖ ^ 2
      ≤ ∫ y, 3 * (‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) y‖ ^ 2 +
        ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2 +
          ‖g y - f y‖ ^ 2) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity) hsum (ae_of_all _ hle)
    _ = 3 * ((∫ y, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) y‖ ^ 2)
        + (∫ y, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2)
        + ∫ y, ‖g y - f y‖ ^ 2) := by
        rw [integral_const_mul]
        congr 1
        have h1 := integral_add (hAi.add (hBi n)) hCi
        have h2 := integral_add hAi (hBi n)
        simp only [Pi.add_apply] at h1 h2
        rw [h1, h2]
    _ < ε := by
        have : ∫ y, ‖f y - g y‖ ^ 2 ≤ ε / 20 := hgε'
        linarith

theorem mollify_fderiv_apply' (φ : ContDiffBump (0 : Space)) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (hloc : LocallyIntegrable v volume) (hw : IsWeakGradientOf v G)
    (y : Space) (j : Fin 3) :
    fderiv ℝ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y (unitVector j) =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector j)) y := by
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

theorem diff_sq_integrable (φ : ContDiffBump (0 : Space)) (f : Space → Space)
    (hfm : AEStronglyMeasurable f volume) (hI : Integrable (fun z => ‖f z‖ ^ 2)) :
    Integrable (fun y => ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y - f y‖ ^ 2) := by
  have hf2 : MemLp f 2 volume := (memLp_two_iff_integrable_sq_norm hfm).2 hI
  have hfl : LocallyIntegrable f volume := hf2.locallyIntegrable (by norm_num)
  have hc : Continuous (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) :=
    (φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hfl (n := 0)).continuous
  have hA := (conv_sq_integral_le φ f hfl hI).1
  have hc2 : MemLp (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 hA
  exact (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable.sub hfm)).1 (hc2.sub hf2)

end MollifySecondApproxInternal

def MollifySecondApproxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H → ∀ ε : ℝ, 0 < ε →
    ∃ w : Space → Space, ContDiff ℝ ∞ w ∧ MemLp w 6 volume ∧
      Integrable (fun y => entrySq (fderiv ℝ w y)) ∧
      Integrable (fun y => CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ w) y)) ∧
      Integrable (fun y => entrySq (fderiv ℝ w y - G y)) ∧ ∫ y, entrySq (fderiv ℝ w y - G y) ≤ ε ∧
      Integrable (fun y => CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ w) y - H y)) ∧
      ∫ y, CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ w) y - H y) ≤ ε

open MollifySecondApproxInternal in
theorem mollifySecondApprox : MollifySecondApproxStatement := by
  intro m v G H hv ε hε
  have hvl : LocallyIntegrable v volume := hv.velocity_six.locallyIntegrable (by norm_num)
  have hGm : ∀ j : Fin 3, AEStronglyMeasurable (fun z => G z (unitVector j)) volume := fun j =>
    hv.measurable_gradient.apply_continuousLinearMap _
  have hGi : ∀ j : Fin 3, Integrable (fun z => ‖G z (unitVector j)‖ ^ 2) := fun j =>
    hv.gradient_two.mono' ((hGm j).norm.pow 2) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Finset.single_le_sum (f := fun i => ‖G z (unitVector i)‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j))
  have hGl : ∀ j : Fin 3, LocallyIntegrable (fun z => G z (unitVector j)) volume := fun j =>
    ((memLp_two_iff_integrable_sq_norm (hGm j)).2 (hGi j)).locallyIntegrable (by norm_num)
  have hHm : ∀ a b : Fin 3, AEStronglyMeasurable (fun z => H z (unitVector a) (unitVector b)) volume :=
    fun a b => (hv.measurable_second.apply_continuousLinearMap _).apply_continuousLinearMap _
  have hHi : ∀ a b : Fin 3, Integrable (fun z => ‖H z (unitVector a) (unitVector b)‖ ^ 2) := fun a b =>
    hv.second_two.mono' ((hHm a b).norm.pow 2) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖H z (unitVector a) (unitVector b)‖ ^ 2 ≤ ∑ j : Fin 3, ‖H z (unitVector a) (unitVector j)‖ ^ 2 :=
            Finset.single_le_sum (f := fun j => ‖H z (unitVector a) (unitVector j)‖ ^ 2)
              (fun j _ => by positivity) (Finset.mem_univ b)
        _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖H z (unitVector i) (unitVector j)‖ ^ 2 :=
            Finset.single_le_sum (f := fun i => ∑ j : Fin 3, ‖H z (unitVector i) (unitVector j)‖ ^ 2)
              (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ a))
  have hHl : ∀ a b : Fin 3, LocallyIntegrable (fun z => H z (unitVector a) (unitVector b)) volume := fun a b =>
    ((memLp_two_iff_integrable_sq_norm (hHm a b)).2 (hHi a b)).locallyIntegrable (by norm_num)
  have hwG : ∀ b : Fin 3, IsWeakGradientOf (fun z => G z (unitVector b)) (fun z => (H z).flip (unitVector b)) := by
    intro b φ hφ j
    have := hv.weak_second φ hφ b j
    simpa [ContinuousLinearMap.flip_apply] using this
  set w : ℕ → Space → Space := fun n => ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) with hw_def
  have hwc : ∀ n, ContDiff ℝ ∞ (w n) := fun n =>
    ((kernelBump n).hasCompactSupport_normed).contDiff_convolution_left _ (kernelBump n).contDiff_normed hvl
  have D1 : ∀ n y j, fderiv ℝ (w n) y (unitVector j) = ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector j)) y :=
    fun n y j => mollify_fderiv_apply' _ v G hvl hv.weak_gradient y j
  have D2 : ∀ n y a b, fderiv ℝ (fderiv ℝ (w n)) y (unitVector a) (unitVector b) =
      ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => H z (unitVector a) (unitVector b)) y := by
    intro n y a b
    have hd : DifferentiableAt ℝ (fun z => fderiv ℝ (w n) z) y :=
      ((contDiff_infty_iff_fderiv.1 (hwc n)).2.differentiable (by simp)) y
    have e1 : fderiv ℝ (fderiv ℝ (w n)) y (unitVector a) (unitVector b) =
        fderiv ℝ (fun z => fderiv ℝ (w n) z (unitVector b)) y (unitVector a) := by
      rw [fderiv_clm_apply hd (differentiableAt_const _)]
      simp
    have e2 : (fun z => fderiv ℝ (w n) z (unitVector b)) = ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector b)) :=
      funext fun z => D1 n z b
    rw [e1, e2, mollify_fderiv_apply' _ _ _ (hGl b) (hwG b) y a]
    simp [ContinuousLinearMap.flip_apply]
  have E1 : ∀ n y, entrySq (fderiv ℝ (w n) y - G y) =
      ∑ j : Fin 3, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector j)) y - G y (unitVector j)‖ ^ 2 := by
    intro n y
    simp only [entrySq, ContinuousLinearMap.sub_apply, D1]
  have E2 : ∀ n y, CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (w n)) y - H y) =
      ∑ a : Fin 3, ∑ b : Fin 3, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => H z (unitVector a) (unitVector b)) y -
        H y (unitVector a) (unitVector b)‖ ^ 2 := by
    intro n y
    simp only [CellCert.fullSecondSq, ContinuousLinearMap.sub_apply, D2]
  have I1 : ∀ n, Integrable (fun y => entrySq (fderiv ℝ (w n) y - G y)) := by
    intro n
    simp only [E1]
    exact integrable_finsetSum _ fun j _ => diff_sq_integrable _ _ (hGm j) (hGi j)
  have I2 : ∀ n, Integrable (fun y => CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (w n)) y - H y)) := by
    intro n
    simp only [E2]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      diff_sq_integrable _ _ (hHm a b) (hHi a b)
  have T1 : Tendsto (fun n => ∫ y, entrySq (fderiv ℝ (w n) y - G y)) atTop (𝓝 0) := by
    have e : (fun n => ∫ y, entrySq (fderiv ℝ (w n) y - G y)) = fun n => ∑ j : Fin 3,
        ∫ y, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector j)) y - G y (unitVector j)‖ ^ 2 := by
      funext n
      simp only [E1]
      exact integral_finsetSum _ fun j _ => diff_sq_integrable _ _ (hGm j) (hGi j)
    rw [e]
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => conv_sq_tendsto _ (hGm j) (hGi j)
    simpa using this
  have T2 : Tendsto (fun n => ∫ y, CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (w n)) y - H y)) atTop (𝓝 0) := by
    have e : (fun n => ∫ y, CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (w n)) y - H y)) = fun n =>
        ∑ a : Fin 3, ∑ b : Fin 3, ∫ y, ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => H z (unitVector a) (unitVector b)) y -
          H y (unitVector a) (unitVector b)‖ ^ 2 := by
      funext n
      simp only [E2]
      rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
        diff_sq_integrable _ _ (hHm a b) (hHi a b)]
      exact Finset.sum_congr rfl fun a _ => integral_finsetSum _ fun b _ => diff_sq_integrable _ _ (hHm a b) (hHi a b)
    rw [e]
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun a _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun b _ => conv_sq_tendsto _ (hHm a b) (hHi a b)
    simpa using this
  obtain ⟨n, hn1, hn2⟩ := ((T1.eventually (gt_mem_nhds hε)).and (T2.eventually (gt_mem_nhds hε))).exists
  have h6' : MemLp v ((6 : ℕ) : ℝ≥0∞) volume := by exact_mod_cast hv.velocity_six
  have hI6 : Integrable (fun z => ‖v z‖ ^ 6) := h6'.integrable_norm_pow (by norm_num)
  have hm : AEStronglyMeasurable (w n) volume := (hwc n).continuous.aestronglyMeasurable
  have hi : Integrable (fun y => ‖w n y‖ ^ 6) :=
    (((kernelBump n).integrable_normed).integrable_convolution _ hI6).mono' (hm.norm.pow 6)
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact normPow_conv_le (kernelBump n) v 6 (by norm_num) hI6 y)
  have h6w : MemLp (w n) 6 volume := by
    refine (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).1 ?_
    simpa using hi
  have hE : Integrable (fun y => entrySq (fderiv ℝ (w n) y)) := by
    simp only [entrySq, D1]
    exact integrable_finsetSum _ fun j _ => (conv_sq_integral_le _ _ (hGl j) (hGi j)).1
  have hS : Integrable (fun y => CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (w n)) y)) := by
    simp only [CellCert.fullSecondSq, D2]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (conv_sq_integral_le _ _ (hHl a b) (hHi a b)).1
  exact ⟨w n, hwc n, h6w, hE, hS, I1 n, hn1.le, I2 n, hn2.le⟩

end Reduction

end CellCert

end Breakdown
