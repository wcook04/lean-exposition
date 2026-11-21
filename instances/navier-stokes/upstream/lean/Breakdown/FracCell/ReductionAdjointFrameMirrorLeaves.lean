import Breakdown.FracCell.StWeightedInverseSquare
import Breakdown.Uniqueness.CutoffBounds

open scoped Convolution

open scoped ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace FracInternal

namespace FrameMirrorLeaves

open SteadyCert

def TestGradientApproxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H →
    ∃ u : ℕ → Space → Space, (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n)) ∧
      Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (u n) y - G y))) atTop (𝓝 0) ∧
      ∀ R : ℝ, Tendsto (fun n => ∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖u n y - v y‖ ^ 2)) atTop (𝓝 0)

def GradientMirrorStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H → ∀ᵐ y ∂volume, ∀ w : Space, G (mirror y) (mirror w) = mirror (G y w)


def SmoothL2ApproxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H →
    ∃ w : ℕ → Space → Space,
      (∀ n, ContDiff ℝ ∞ (w n) ∧ MemLp (w n) 6 volume ∧ Integrable (fun y => entrySq (fderiv ℝ (w n) y))) ∧
      Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y))) atTop (𝓝 0) ∧
      ∀ R : ℝ, Tendsto (fun n => ∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖w n y - v y‖ ^ 2)) atTop (𝓝 0)

def CutoffGradientStatement : Prop :=
  ∀ w : Space → Space, ContDiff ℝ ∞ w → MemLp w 6 volume → Integrable (fun y => entrySq (fderiv ℝ w y)) →
    Tendsto (fun R : ℝ => ∫⁻ y, ENNReal.ofReal
      (entrySq (fderiv ℝ (fun z => radialCutoff R z • w z) y - fderiv ℝ w y))) atTop (𝓝 0)

private theorem entrySq_nonneg_aux (A : Space →L[ℝ] Space) : 0 ≤ entrySq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem entrySq_add_le (A B : Space →L[ℝ] Space) : entrySq (A + B) ≤ 2 * entrySq A + 2 * entrySq B := by
  unfold entrySq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ContinuousLinearMap.add_apply]
  have h := norm_add_le (A (unitVector i)) (B (unitVector i))
  have h0 := norm_nonneg (A (unitVector i) + B (unitVector i))
  nlinarith [norm_nonneg (A (unitVector i)), norm_nonneg (B (unitVector i)),
    sq_nonneg (‖A (unitVector i)‖ - ‖B (unitVector i)‖)]

private theorem entrySq_cont' : Continuous entrySq := by
  unfold entrySq
  fun_prop

theorem testGradientApprox_of (hS : SmoothL2ApproxStatement) (hC : CutoffGradientStatement) :
    TestGradientApproxStatement := by
  intro m v G H hv
  obtain ⟨w, hw, hgrad, hball⟩ := hS m v G H hv
  have hR : ∀ n : ℕ, ∃ R : ℝ, (n : ℝ) + 1 ≤ R ∧
      ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (fun z => radialCutoff R z • w n z) y - fderiv ℝ (w n) y)) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    have h := (hC (w n) (hw n).1 (hw n).2.1 (hw n).2.2).eventually
      (Iic_mem_nhds (ENNReal.ofReal_pos.2 (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)))
    exact ((eventually_ge_atTop ((n : ℝ) + 1)).and h).exists
  choose R hR1 hR2 using hR
  have hRpos : ∀ n, 0 < R n := fun n => lt_of_lt_of_le (by positivity) (hR1 n)
  refine ⟨fun n z => radialCutoff (R n) z • w n z, fun n => ⟨(contDiff_radialCutoff (hRpos n)).smul (hw n).1,
    (hasCompactSupport_radialCutoff (hRpos n)).smul_right⟩, ?_, fun ρ => ?_⟩
  · have hmeas : ∀ n, AEMeasurable (fun y => 2 * ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y))) volume := by
      intro n
      have hc : Continuous (fderiv ℝ (w n)) := (hw n).1.continuous_fderiv (by simp)
      exact ((entrySq_cont'.comp_aestronglyMeasurable
        (hc.aestronglyMeasurable.sub hv.measurable_gradient)).aemeasurable.ennreal_ofReal).const_mul 2
    have hbd : ∀ n, ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y - G y)) ≤
        2 * ENNReal.ofReal (1 / ((n : ℝ) + 1)) + 2 * ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y)) := by
      intro n
      calc _ ≤ ∫⁻ y, (2 * ENNReal.ofReal (entrySq (fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y -
              fderiv ℝ (w n) y)) + 2 * ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y))) := by
            refine lintegral_mono fun y => ?_
            have e : fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y - G y =
                (fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y - fderiv ℝ (w n) y) + (fderiv ℝ (w n) y - G y) := by
              abel
            rw [e]
            refine (ENNReal.ofReal_le_ofReal (entrySq_add_le _ _)).trans (le_of_eq ?_)
            have a1 := entrySq_nonneg_aux (fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y - fderiv ℝ (w n) y)
            have a2 := entrySq_nonneg_aux (fderiv ℝ (w n) y - G y)
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        _ = 2 * (∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y -
              fderiv ℝ (w n) y))) + 2 * ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - G y)) := by
            rw [lintegral_add_right' _ (hmeas n), lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
        _ ≤ _ := by
            gcongr
            exact hR2 n
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat)
      rwa [ENNReal.ofReal_zero] at this
    have h2 := (ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.ofNat_ne_top (n := 2)))).add
      (ENNReal.Tendsto.const_mul hgrad (Or.inr (ENNReal.ofNat_ne_top (n := 2))))
    rw [mul_zero, add_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => bot_le) hbd
  · refine (hball ρ).congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ρ
    filter_upwards [eventually_ge_atTop N] with n hn
    refine setLIntegral_congr_fun measurableSet_ball (fun y hy => ?_)
    have hy' : ‖y‖ ≤ R n := by
      have h1 : ‖y‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hy
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith [hR1 n]
    simp [radialCutoff_eq_one (hRpos n) hy']

private theorem conv_pow_le (φ : ContDiffBump (0 : Space)) (f : Space → Space)
    (k : ℕ) (hk : 1 ≤ k) (hI : Integrable (fun z => ‖f z‖ ^ k))
    (y : Space) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ k ≤
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖f z‖ ^ k) y := by
  set ρ : Space → ℝ := φ.normed volume with hρ
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => φ.nonneg_normed t
  have hρc : Continuous ρ := φ.continuous_normed
  set d : Space → NNReal := fun t => (ρ t).toNNReal with hd
  have hdm : Measurable d := hρc.measurable.real_toNNReal
  set μ : Measure Space := volume.withDensity (fun t => (d t : ENNReal)) with hμ
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


private theorem conv_fderiv_apply (φ : ContDiffBump (0 : Space)) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (h6 : MemLp v 6 volume) (hw : IsWeakGradientOf v G) (y : Space) (j : Fin 3) :
    fderiv ℝ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y (unitVector j) =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector j)) y := by
  have hloc : LocallyIntegrable v volume := h6.locallyIntegrable (by norm_num)
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


def MollifierL2Statement : Prop :=
  ∀ φ : ℕ → ContDiffBump (0 : Space), Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) →
    ∀ f : Space → Space, MemLp f 2 volume →
      Tendsto (fun n => ∫⁻ y, ENNReal.ofReal
        (‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y - f y‖ ^ 2)) atTop (𝓝 0)

private def bump (n : ℕ) : ContDiffBump (0 : Space) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]
    linarith⟩

private theorem conv_local (n : ℕ) (v : Space → Space) (R : ℝ) {y : Space} (hy : y ∈ Metric.ball (0 : Space) R) :
    ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y =
      ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (Metric.ball (0 : Space) (R + 1)).indicator v) y := by
  rw [convolution_def, convolution_def]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  by_cases ht : (bump n).normed volume t = 0
  · simp [ht]
  · have hts : t ∈ Metric.ball (0 : Space) (bump n).rOut := by
      rw [← (bump n).support_normed_eq (μ := volume)]
      exact ht
    have hr : (bump n).rOut ≤ 1 := by
      show 1 / ((n : ℝ) + 1) ≤ 1
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hmem : y - t ∈ Metric.ball (0 : Space) (R + 1) := by
      rw [Metric.mem_ball, dist_zero_right] at hy hts ⊢
      calc ‖y - t‖ ≤ ‖y‖ + ‖t‖ := norm_sub_le y t
        _ < R + 1 := by linarith
    simp only [Set.indicator_of_mem hmem]

theorem smoothL2Approx_of (hL : MollifierL2Statement) : SmoothL2ApproxStatement := by
  intro m v G H hv
  have h6 := hv.velocity_six
  have hloc : LocallyIntegrable v volume := h6.locallyIntegrable (by norm_num)
  have hGm : ∀ j : Fin 3, AEStronglyMeasurable (fun y => G y (unitVector j)) volume := fun j =>
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hv.measurable_gradient
  have hGc : ∀ j : Fin 3, Integrable (fun z => ‖G z (unitVector j)‖ ^ 2) := fun j =>
    hv.gradient_two.mono' ((hGm j).norm.pow 2) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [entrySq]
      exact Finset.single_le_sum (f := fun i => ‖G z (unitVector i)‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j))
  have hGj : ∀ j : Fin 3, MemLp (fun y => G y (unitVector j)) 2 volume := fun j =>
    (memLp_two_iff_integrable_sq_norm (hGm j)).2 (hGc j)
  have h6' : MemLp v ((6 : ℕ) : ENNReal) volume := by exact_mod_cast h6
  have hI6 : Integrable (fun z => ‖v z‖ ^ 6) := h6'.integrable_norm_pow (by norm_num)
  have hrout : Tendsto (fun n => (bump n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hρi : ∀ n, Integrable ((bump n).normed volume) := fun n => (bump n).integrable_normed
  have hwc : ∀ n, ContDiff ℝ ∞ ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) :=
    fun n => ((bump n).hasCompactSupport_normed).contDiff_convolution_left _ (bump n).contDiff_normed hloc
  have hEpt : ∀ n y, entrySq (fderiv ℝ ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y) ≤
      ∑ j : Fin 3, ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun z => ‖G z (unitVector j)‖ ^ 2) y := by
    intro n y
    simp only [entrySq, conv_fderiv_apply (bump n) v G h6 hv.weak_gradient y]
    exact Finset.sum_le_sum fun j _ => conv_pow_le (bump n) _ 2 (by norm_num) (hGc j) y
  have hSi : ∀ n, Integrable (fun y => ∑ j : Fin 3, ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun z => ‖G z (unitVector j)‖ ^ 2) y) := fun n =>
    integrable_finsetSum _ fun j _ => (hρi n).integrable_convolution _ (hGc j)
  have hEc : ∀ n, Continuous (fun y =>
      entrySq (fderiv ℝ ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y)) := by
    intro n
    simp only [entrySq]
    exact continuous_finsetSum _ fun i _ =>
      ((((hwc n).continuous_fderiv (by simp)).clm_apply continuous_const).norm).pow 2
  refine ⟨fun n => (bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v, fun n => ⟨hwc n, ?_, ?_⟩, ?_, ?_⟩
  · have hm : AEStronglyMeasurable ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) volume :=
      (hwc n).continuous.aestronglyMeasurable
    have hi : Integrable (fun y => ‖((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y‖ ^ 6) :=
      ((hρi n).integrable_convolution _ hI6).mono' (hm.norm.pow 6) (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact conv_pow_le (bump n) v 6 (by norm_num) hI6 y)
    refine (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).1 ?_
    simpa using hi
  · exact (hSi n).mono' (hEc n).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
      exact hEpt n y)
  · have hcol : ∀ j : Fin 3, Tendsto (fun n => ∫⁻ y, ENNReal.ofReal
        (‖((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector j)) y -
          G y (unitVector j)‖ ^ 2)) atTop (𝓝 0) := fun j => hL bump hrout _ (hGj j)
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => hcol j
    simp only [Finset.sum_const_zero] at hsum
    refine hsum.congr fun n => ?_
    have hmj : ∀ j : Fin 3, AEMeasurable (fun y => ENNReal.ofReal
        (‖((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector j)) y -
          G y (unitVector j)‖ ^ 2)) volume := by
      intro j
      have hcc : Continuous ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun z => G z (unitVector j)) :=
        ((bump n).hasCompactSupport_normed).continuous_convolution_left _ (bump n).continuous_normed
          ((hGj j).locallyIntegrable (by norm_num))
      exact ((hcc.aestronglyMeasurable.sub (hGm j)).norm.pow 2).aemeasurable.ennreal_ofReal
    rw [← lintegral_finsetSum' _ fun j _ => hmj j]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
    congr 1
    simp only [entrySq, ContinuousLinearMap.sub_apply, conv_fderiv_apply (bump n) v G h6 hv.weak_gradient y]
  · intro R
    have hf : MemLp ((Metric.ball (0 : Space) (R + 1)).indicator v) 2 volume := by
      have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Space) (R + 1))) :=
        isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
      rw [memLp_indicator_iff_restrict measurableSet_ball]
      exact (h6.restrict _).mono_exponent (by norm_num)
    have ht := hL bump hrout _ hf
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) fun n => ?_
    refine le_trans (le_of_eq (setLIntegral_congr_fun measurableSet_ball fun y hy => ?_))
      (setLIntegral_le_lintegral _ _)
    have hy1 : y ∈ Metric.ball (0 : Space) (R + 1) := by
      rw [Metric.mem_ball, dist_zero_right] at hy ⊢
      linarith
    beta_reduce
    rw [conv_local n v R hy, Set.indicator_of_mem hy1]


private theorem conv_l2_le (φ : ContDiffBump (0 : Space)) (h : Space → Space) (hI : Integrable (fun z => ‖h z‖ ^ 2)) :
    ∫⁻ y, ENNReal.ofReal (‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) y‖ ^ 2) ≤
      ∫⁻ y, ENNReal.ofReal (‖h y‖ ^ 2) := by
  have hci : Integrable (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖h z‖ ^ 2) :=
    φ.integrable_normed.integrable_convolution _ hI
  have hnn : ∀ y, 0 ≤ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖h z‖ ^ 2) y := by
    intro y
    rw [convolution_def]
    exact integral_nonneg fun t => by
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      exact mul_nonneg (φ.nonneg_normed t) (by positivity)
  calc _ ≤ ∫⁻ y, ENNReal.ofReal ((φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖h z‖ ^ 2) y) :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (conv_pow_le φ h 2 (by norm_num) hI y)
    _ = ENNReal.ofReal (∫ y, (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖h z‖ ^ 2) y) :=
        (ofReal_integral_eq_lintegral_ofReal hci (ae_of_all _ hnn)).symm
    _ = ENNReal.ofReal (∫ y, ‖h y‖ ^ 2) := by
        rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) φ.integrable_normed hI]
        simp [ContDiffBump.integral_normed]
    _ = _ := ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun y => by positivity)

private theorem conv_compact_tendsto (φ : ℕ → ContDiffBump (0 : Space)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (g : Space → Space) (hg : Continuous g) (hgs : HasCompactSupport g) :
    Tendsto (fun n => ∫⁻ y, ENNReal.ofReal
      (‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgs
  obtain ⟨A, hA⟩ := hgs.isCompact.isBounded.subset_closedBall 0
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hcont : ∀ n, Continuous ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := fun n =>
    ((φ n).hasCompactSupport_normed).continuous_convolution_left _ (φ n).continuous_normed (hg.locallyIntegrable (μ := volume))
  have hbd : ∀ n y, ‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y‖ ≤ C := by
    intro n y
    rw [convolution_def]
    refine (norm_integral_le_of_norm_le ((φ n).integrable_normed.mul_const C) (ae_of_all _ fun t => ?_)).trans_eq ?_
    · simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg ((φ n).nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left (hC _) ((φ n).nonneg_normed t)
    · rw [integral_mul_const, ContDiffBump.integral_normed, one_mul]
  have hgz : ∀ z, A < ‖z‖ → g z = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport fun hm => ?_
    have := hA hm
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hzero : ∀ n, (φ n).rOut ≤ 1 → ∀ y, A + 1 < ‖y‖ →
      ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y = 0 := by
    intro n hn y hy
    rw [convolution_def]
    have : (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) ((φ n).normed volume t) (g (y - t))) = fun _ => 0 := by
      funext t
      by_cases ht : (φ n).normed volume t = 0
      · simp [ht]
      · have hts : t ∈ Metric.ball (0 : Space) (φ n).rOut := by
          rw [← (φ n).support_normed_eq (μ := volume)]
          exact ht
        rw [Metric.mem_ball, dist_zero_right] at hts
        have : A < ‖y - t‖ := by
          have := norm_sub_norm_le y t
          linarith
        simp [hgz _ this]
    rw [this, integral_zero]
  set B : Space → ENNReal := (Metric.closedBall (0 : Space) (A + 1)).indicator fun _ => ENNReal.ofReal ((2 * C) ^ 2)
  have hBfin : ∫⁻ y, B y ≠ ⊤ := by
    rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  have hev : ∀ᶠ n in atTop, (φ n).rOut ≤ 1 := hφ.eventually (ge_mem_nhds one_pos)
  have := tendsto_lintegral_filter_of_dominated_convergence (l := atTop) (f := fun _ => 0)
    (F := fun n y => ENNReal.ofReal (‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2)) B
    (Eventually.of_forall fun n => by
      have hc : Continuous (fun y => ‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2) :=
        ((hcont n).sub hg).norm.pow 2
      exact hc.measurable.ennreal_ofReal)
    (hev.mono fun n hn => ae_of_all _ fun y => by
      by_cases hy : ‖y‖ ≤ A + 1
      · have hm : y ∈ Metric.closedBall (0 : Space) (A + 1) := by simpa using hy
        simp only [B, Set.indicator_of_mem hm]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := norm_sub_le (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y) (g y)
        have h2 := hbd n y
        have h3 := hC y
        have h4 := norm_nonneg (((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y)
        nlinarith
      · rw [not_le] at hy
        rw [hzero n hn y hy, hgz y (by linarith)]
        simp)
    hBfin
    (ae_of_all _ fun y => by
      have h1 : Tendsto (fun n => ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y)
          atTop (𝓝 0) := by
        have := (ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hg y).sub (tendsto_const_nhds (x := g y))
        rwa [sub_self] at this
      have h2 : Tendsto (fun n => ‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y - g y‖ ^ 2)
          atTop (𝓝 0) := by
        have := h1.norm.pow 2
        simpa using this
      have h3 := ENNReal.tendsto_ofReal h2
      rwa [ENNReal.ofReal_zero] at h3)
  simpa using this

theorem mollifierL2 : MollifierL2Statement := by
  intro φ hφ f hf
  have hfm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun _ => by rw [hεt]; exact le_top
  set δ : ℝ := ε.toReal / 12 with hδ
  have hδ0 : 0 < δ := by
    have := ENNReal.toReal_pos hε.ne' hεt
    positivity
  have hf' : MemLp f (ENNReal.ofReal 2) volume := by simpa using hf
  obtain ⟨g, hgs, hgI, hgc, hgm⟩ := hf'.exists_hasCompactSupport_integral_rpow_sub_le two_pos hδ0
  have hgm2 : MemLp g 2 volume := by simpa using hgm
  have hfg2 : MemLp (fun z => f z - g z) 2 volume := hf.sub hgm2
  have hIfg : Integrable (fun z => ‖f z - g z‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfg2.aestronglyMeasurable).1 hfg2
  have hfg : ∫⁻ y, ENNReal.ofReal (‖f y - g y‖ ^ 2) ≤ ENNReal.ofReal δ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hIfg (ae_of_all _ fun y => by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) hgI)
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    norm_num
  have hgf : ∫⁻ y, ENNReal.ofReal (‖g y - f y‖ ^ 2) ≤ ENNReal.ofReal δ := by
    simpa only [norm_sub_rev] using hfg
  have hyo : ∀ n, ∫⁻ y, ENNReal.ofReal
      (‖((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => f z - g z) y‖ ^ 2) ≤
      ENNReal.ofReal δ := fun n => (conv_l2_le (φ n) _ hIfg).trans hfg
  have hC := (ENNReal.tendsto_nhds_zero.1 (conv_compact_tendsto φ hφ g hgc hgs)) (ENNReal.ofReal δ)
    (ENNReal.ofReal_pos.2 hδ0)
  have hlocfg : LocallyIntegrable (fun z => f z - g z) volume := hfg2.locallyIntegrable (by norm_num)
  filter_upwards [hC] with n hn
  set T1 : Space → Space := (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => f z - g z
  set T2 : Space → Space := (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  have hT1c : Continuous T1 :=
    ((φ n).hasCompactSupport_normed).continuous_convolution_left _ (φ n).continuous_normed hlocfg
  have hT2c : Continuous T2 :=
    ((φ n).hasCompactSupport_normed).continuous_convolution_left _ (φ n).continuous_normed (hgc.locallyIntegrable (μ := volume))
  have hsplit : ∀ y, ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y - f y =
      T1 y + (T2 y - g y) + (g y - f y) := by
    intro y
    have e : f = (fun z => f z - g z) + g := by
      funext z
      simp
    have hd := ConvolutionExistsAt.distrib_add
      (((φ n).hasCompactSupport_normed).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ n).continuous_normed (μ := volume)) hlocfg y)
      (((φ n).hasCompactSupport_normed).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ n).continuous_normed (μ := volume)) (hgc.locallyIntegrable (μ := volume)) y)
    rw [← e] at hd
    rw [hd]
    abel
  have hsq : ∀ a b c : Space, ‖a + b + c‖ ^ 2 ≤ 3 * ‖a‖ ^ 2 + 3 * ‖b‖ ^ 2 + 3 * ‖c‖ ^ 2 := by
    intro a b c
    have h1 := norm_add₃_le (a := a) (b := b) (c := c)
    have h0 := norm_nonneg (a + b + c)
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c, sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖),
      sq_nonneg (‖a‖ - ‖c‖)]
  have hm1 : AEMeasurable (fun y => 3 * ENNReal.ofReal (‖T1 y‖ ^ 2)) volume :=
    ((ENNReal.continuous_ofReal.comp (hT1c.norm.pow 2)).measurable.const_mul 3).aemeasurable
  have hm2 : AEMeasurable (fun y => 3 * ENNReal.ofReal (‖T1 y‖ ^ 2) + 3 * ENNReal.ofReal (‖T2 y - g y‖ ^ 2)) volume :=
    (((ENNReal.continuous_ofReal.comp (hT1c.norm.pow 2)).measurable.const_mul 3).add
      ((ENNReal.continuous_ofReal.comp ((hT2c.sub hgc).norm.pow 2)).measurable.const_mul 3)).aemeasurable
  calc _ ≤ ∫⁻ y, (3 * ENNReal.ofReal (‖T1 y‖ ^ 2) + 3 * ENNReal.ofReal (‖T2 y - g y‖ ^ 2) +
        3 * ENNReal.ofReal (‖g y - f y‖ ^ 2)) := by
        refine lintegral_mono fun y => ?_
        rw [hsplit y]
        refine (ENNReal.ofReal_le_ofReal (hsq _ _ _)).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]
    _ = 3 * (∫⁻ y, ENNReal.ofReal (‖T1 y‖ ^ 2)) + 3 * (∫⁻ y, ENNReal.ofReal (‖T2 y - g y‖ ^ 2)) +
        3 * ∫⁻ y, ENNReal.ofReal (‖g y - f y‖ ^ 2) := by
        rw [lintegral_add_left' hm2, lintegral_add_left' hm1, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    _ ≤ 3 * ENNReal.ofReal δ + 3 * ENNReal.ofReal δ + 3 * ENNReal.ofReal δ := by
        gcongr
        exact hyo n
    _ ≤ ε := by
        have e9 : 3 * ENNReal.ofReal δ + 3 * ENNReal.ofReal δ + 3 * ENNReal.ofReal δ = ENNReal.ofReal (9 * δ) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num
          ring
        rw [e9, ← ENNReal.ofReal_toReal hεt]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hδ]
        have := ENNReal.toReal_nonneg (a := ε)
        linarith

theorem smoothL2Approx : SmoothL2ApproxStatement :=
  smoothL2Approx_of mollifierL2


private theorem fderiv_cutoff_ne {R : ℝ} (hR : 0 < R) {y : Space} (h : fderiv ℝ (radialCutoff R) y ≠ 0) :
    R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R := by
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    apply h
    have he : radialCutoff R =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show y ∈ Metric.ball (0 : Space) R by simpa using hlt)]
        with z hz
      exact radialCutoff_eq_one hR (le_of_lt (by simpa using hz))
    rw [he.fderiv_eq]
    simp
  · by_contra hlt
    rw [not_le] at hlt
    apply h
    have hopen : IsOpen {z : Space | 2 * R < ‖z‖} := isOpen_lt continuous_const continuous_norm
    have he : radialCutoff R =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hlt] with z hz
      exact radialCutoff_eq_zero hR (le_of_lt hz)
    rw [he.fderiv_eq]
    simp

private theorem sq_le_six {a M : ℝ} (hM : 0 < M) : a ^ 2 ≤ a ^ 6 / M ^ 2 + M := by
  rcases le_or_gt (a ^ 2) M with h | h
  · have : 0 ≤ a ^ 6 / M ^ 2 := by positivity
    linarith
  · have h1 : M ^ 2 ≤ (a ^ 2) ^ 2 := pow_le_pow_left₀ hM.le h.le 2
    have h2 : a ^ 2 * M ^ 2 ≤ a ^ 6 := by
      have : a ^ 6 = a ^ 2 * (a ^ 2) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : a ^ 2 ≤ a ^ 6 / M ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      exact h2
    linarith

private theorem cutoff_term_integrable (w : Space → Space) (hw : Continuous w) {R : ℝ} (hR : 0 < R) :
    Integrable (fun y => ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2) := by
  have hcc : ContDiff ℝ ∞ (radialCutoff R) := contDiff_radialCutoff hR
  refine Continuous.integrable_of_hasCompactSupport
    (((hcc.continuous_fderiv (by simp)).norm.pow 2).mul (hw.norm.pow 2)) ?_
  exact ((hasCompactSupport_radialCutoff hR).fderiv (𝕜 := ℝ)).mono fun y hy h0 => hy (by simp [h0])

private theorem cutoff_tail (w : Space → Space) (hw : Continuous w) (h6 : MemLp w 6 volume) :
    Tendsto (fun R : ℝ => ∫ y, ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have h6' : MemLp w ((6 : ℕ) : ENNReal) volume := by exact_mod_cast h6
  have hI : Integrable (fun y => ‖w y‖ ^ 6) := h6'.integrable_norm_pow (by norm_num)
  set tail : ℝ → ℝ := fun R => ∫ y, {z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6) y with htail
  have hmeasS : ∀ R : ℝ, MeasurableSet {z : Space | R ≤ ‖z‖} := fun R =>
    measurableSet_le measurable_const measurable_norm
  have htl : Tendsto tail atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun R : ℝ => {z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6)) (f := fun _ => (0 : ℝ))
      (fun y => ‖w y‖ ^ 6)
      (Eventually.of_forall fun R => hI.aestronglyMeasurable.indicator (hmeasS R))
      (Eventually.of_forall fun R => ae_of_all _ fun y => by
        refine (norm_indicator_le_norm_self _ _).trans ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)])
      hI
      (ae_of_all _ fun y => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop ‖y‖] with R hR
        have : y ∉ {z : Space | R ≤ ‖z‖} := by simpa using hR
        rw [Set.indicator_of_notMem this])
    simpa using this
  set V : ℝ := (volume : Measure Space).real (Metric.ball 0 1) with hV
  have hvol : ∀ R : ℝ, 0 < R → (volume : Measure Space).real (Metric.closedBall 0 (2 * R)) = (2 * R) ^ 3 * V := by
    intro R hR
    rw [measureReal_def, Measure.addHaar_closedBall volume 0 (by positivity), finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hV, measureReal_def]
  have hVpos : 0 ≤ V := measureReal_nonneg
  have hc0 : 0 ≤ c := by
    have := (norm_nonneg _).trans (hc 1 one_pos 0)
    simpa using this
  have hbound : ∀ κ : ℝ, 0 < κ → ∀ R : ℝ, 0 < R →
      ∫ y, ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2 ≤ c ^ 2 * tail R / κ ^ 2 + 8 * c ^ 2 * V * κ := by
    intro κ hκ R hR
    set M : ℝ := κ / R with hM
    have hM0 : 0 < M := by positivity
    have hT := cutoff_term_integrable w hw hR
    have hI1 : Integrable ({z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6)) :=
      hI.indicator (hmeasS R)
    have hI2 : Integrable ((Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => M)) :=
      (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
        (integrableOn_const (measure_closedBall_lt_top).ne)
    have hpt : ∀ y, ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2 ≤
        (c / R) ^ 2 * ({z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6) y / M ^ 2 +
          (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => M) y) := by
      intro y
      by_cases h0 : fderiv ℝ (radialCutoff R) y = 0
      · rw [h0, norm_zero]
        have h1 : 0 ≤ {z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6) y :=
          Set.indicator_nonneg (fun _ _ => by positivity) _
        have h2 : 0 ≤ (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => M) y :=
          Set.indicator_nonneg (fun _ _ => hM0.le) _
        have : 0 ≤ (c / R) ^ 2 * ({z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6) y / M ^ 2 +
          (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => M) y) := by positivity
        simpa using this
      · obtain ⟨hy1, hy2⟩ := fderiv_cutoff_ne hR h0
        have hm1 : y ∈ {z : Space | R ≤ ‖z‖} := hy1
        have hm2 : y ∈ Metric.closedBall (0 : Space) (2 * R) := by simpa using hy2
        rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
        have hd : ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 ≤ (c / R) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hc R hR y) 2
        have hs : ‖w y‖ ^ 2 ≤ ‖w y‖ ^ 6 / M ^ 2 + M := sq_le_six hM0
        exact mul_le_mul hd hs (by positivity) (by positivity)
    have hmono : ∫ y, ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2 ≤
        ∫ y, (c / R) ^ 2 * ({z : Space | R ≤ ‖z‖}.indicator (fun z => ‖w z‖ ^ 6) y / M ^ 2 +
          (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => M) y) :=
      integral_mono hT ((hI1.div_const (M ^ 2)).add hI2 |>.const_mul ((c / R) ^ 2)) hpt
    rw [integral_const_mul, integral_add (hI1.div_const (M ^ 2)) hI2, integral_div,
      integral_indicator_const _ Metric.isClosed_closedBall.measurableSet, hvol R hR, smul_eq_mul] at hmono
    refine hmono.trans_eq ?_
    simp only [htail, hM]
    field_simp
    ring
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun R => lt_of_lt_of_le ha ?_, fun ε hε => ?_⟩
  · exact integral_nonneg fun y => by positivity
  · set κ : ℝ := ε / (16 * (c ^ 2 * V + 1)) with hκ
    have hκ0 : 0 < κ := by positivity
    have hκs : 8 * c ^ 2 * V * κ < ε / 2 := by
      rw [hκ]
      have hpos : 0 < 16 * (c ^ 2 * V + 1) := by positivity
      rw [show 8 * c ^ 2 * V * (ε / (16 * (c ^ 2 * V + 1))) = ε * (8 * (c ^ 2 * V)) / (16 * (c ^ 2 * V + 1)) by ring,
        div_lt_iff₀ hpos]
      nlinarith [mul_nonneg hc0 hc0, mul_nonneg (mul_nonneg hc0 hc0) hVpos]
    have hev : ∀ᶠ R in atTop, c ^ 2 * tail R / κ ^ 2 < ε / 2 := by
      have : Tendsto (fun R => c ^ 2 * tail R / κ ^ 2) atTop (𝓝 (c ^ 2 * 0 / κ ^ 2)) :=
        (htl.const_mul (c ^ 2)).div_const (κ ^ 2)
      rw [mul_zero, zero_div] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hev, eventually_gt_atTop 0] with R hR hR0
    have := hbound κ hκ0 R hR0
    linarith

private theorem cutoff_pointwise {w : Space → Space} (hw : ContDiff ℝ ∞ w) {R : ℝ} (hR : 0 < R) (y : Space) :
    entrySq (fderiv ℝ (fun z => radialCutoff R z • w z) y - fderiv ℝ w y) ≤
      2 * ((1 - radialCutoff R y) ^ 2 * entrySq (fderiv ℝ w y)) +
        6 * (‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2) := by
  have hcd : DifferentiableAt ℝ (radialCutoff R) y := ((contDiff_radialCutoff hR).differentiable (by simp)) y
  have hwd : DifferentiableAt ℝ w y := (hw.differentiable (by simp)) y
  rw [show (fun z => radialCutoff R z • w z) = radialCutoff R • w from rfl, fderiv_smul hcd hwd]
  have e : radialCutoff R y • fderiv ℝ w y + (fderiv ℝ (radialCutoff R) y).smulRight (w y) - fderiv ℝ w y =
      (radialCutoff R y - 1) • fderiv ℝ w y + (fderiv ℝ (radialCutoff R) y).smulRight (w y) := by
    rw [sub_smul, one_smul]
    abel
  rw [e]
  refine (entrySq_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
  · congr 1
    unfold entrySq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  · have hu : ∀ i : Fin 3, ‖unitVector i‖ = 1 := fun i => by simp [unitVector]
    unfold entrySq
    have hi : ∀ i : Fin 3, ‖(fderiv ℝ (radialCutoff R) y).smulRight (w y) (unitVector i)‖ ^ 2 ≤
        ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2 := by
      intro i
      rw [ContinuousLinearMap.smulRight_apply, norm_smul, mul_pow]
      gcongr
      simpa [hu i] using (fderiv ℝ (radialCutoff R) y).le_opNorm (unitVector i)
    have hs := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hi i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    push_cast at hs
    linarith

theorem cutoffGradient : CutoffGradientStatement := by
  intro w hw h6 hE
  have hc : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by simp)
  have hEn : ∀ y, 0 ≤ entrySq (fderiv ℝ w y) := fun y => entrySq_nonneg_aux _
  set F : ℝ → Space → ENNReal := fun R y => ENNReal.ofReal (2 * ((1 - radialCutoff R y) ^ 2 * entrySq (fderiv ℝ w y)))
    with hF
  have hFm : ∀ R, 0 < R → Measurable (F R) := by
    intro R hR
    exact (ENNReal.continuous_ofReal.comp (continuous_const.mul
      (((continuous_const.sub (contDiff_radialCutoff hR).continuous).pow 2).mul (entrySq_cont'.comp hc)))).measurable
  have hA : Tendsto (fun R => ∫⁻ y, F R y) atTop (𝓝 0) := by
    have hfin : ∫⁻ y, ENNReal.ofReal (2 * entrySq (fderiv ℝ w y)) ≠ ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hE.const_mul 2) (ae_of_all _ fun y => by
        have := hEn y
        positivity)]
      exact ENNReal.ofReal_ne_top
    have := tendsto_lintegral_filter_of_dominated_convergence (l := atTop) (F := F) (f := fun _ => 0)
      (fun y => ENNReal.ofReal (2 * entrySq (fderiv ℝ w y)))
      ((eventually_gt_atTop 0).mono fun R hR => hFm R hR)
      (Eventually.of_forall fun R => ae_of_all _ fun y => by
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 := radialCutoff_nonneg R y
        have h1 := radialCutoff_le_one R y
        have h2 : (1 - radialCutoff R y) ^ 2 ≤ 1 := by nlinarith
        have := hEn y
        nlinarith)
      hfin
      (ae_of_all _ fun y => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (max ‖y‖ 1)] with R hR
        have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hR)
        simp [hF, radialCutoff_eq_one hR0 (le_trans (le_max_left _ _) hR)])
    simpa using this
  have hB : Tendsto (fun R => ∫⁻ y, ENNReal.ofReal (6 * (‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun R => ENNReal.ofReal (6 * ∫ y, ‖fderiv ℝ (radialCutoff R) y‖ ^ 2 * ‖w y‖ ^ 2))
        atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal ((cutoff_tail w hw.continuous h6).const_mul 6)
      rwa [mul_zero, ENNReal.ofReal_zero] at this
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
      ((cutoff_term_integrable w hw.continuous hR).const_mul 6) (ae_of_all _ fun y => by positivity)]
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [← lintegral_add_left (hFm R hR)]
  refine lintegral_mono fun y => ?_
  rw [hF, ← ENNReal.ofReal_add (by have := hEn y; positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (cutoff_pointwise hw hR y)

theorem testGradientApprox : TestGradientApproxStatement :=
  testGradientApprox_of smoothL2Approx cutoffGradient


private theorem mm (y : Space) : mirror (mirror y) = y := by
  ext i
  fin_cases i <;> simp [mirror]

private theorem nm (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, mirror]

private def mLin : Space →ₗ[ℝ] Space where
  toFun := mirror
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mirror] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [mirror]

private def mIso : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv ⟨mLin, nm⟩ rfl

private def mCL : Space →L[ℝ] Space := mIso.toContinuousLinearEquiv.toContinuousLinearMap

private theorem mIso_apply (y : Space) : mIso y = mirror y := rfl

private theorem mCL_apply (y : Space) : mCL y = mirror y := rfl

private def sgn (j : Fin 3) : ℝ := if j = 2 then -1 else 1

private theorem mirror_unit (j : Fin 3) : mirror (unitVector j) = sgn j • unitVector j := by
  fin_cases j <;> ext i <;> fin_cases i <;> simp [mirror, unitVector, sgn]

private theorem sgn_sq (j : Fin 3) : sgn j * sgn j = 1 := by
  fin_cases j <;> simp [sgn]

private theorem mirror_smul' (c : ℝ) (x : Space) : mirror (c • x) = c • mirror x := mIso.map_smul c x

private theorem vec_eq (w : Space) : w = ∑ i : Fin 3, w i • unitVector i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w]
  simp [unitVector, EuclideanSpace.basisFun_apply]

private theorem integral_mirror {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (g : Space → A) :
    ∫ x, g (mIso x) = ∫ y, g y :=
  mIso.measurePreserving.integral_comp' (f := mIso.toMeasurableEquiv) g

private theorem integral_mIso (f : Space → Space) : ∫ x, mIso (f x) = mIso (∫ x, f x) :=
  mIso.toLinearIsometry.integral_comp_comm f

theorem gradientMirror : GradientMirrorStatement := by
  intro m v G H hv
  have hvm : ∀ᵐ y ∂volume, v (mirror y) = mirror (v y) := hv.symmetric.2
  have hGj : ∀ j : Fin 3, MemLp (fun y => G y (unitVector j)) 2 volume := by
    intro j
    have hm : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
      (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hv.measurable_gradient
    refine (memLp_two_iff_integrable_sq_norm hm).2
      (hv.gradient_two.mono' (hm.norm.pow 2) (ae_of_all _ fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ j)
  have hcol : ∀ j : Fin 3, ∀ᵐ y ∂volume,
      G y (unitVector j) = sgn j • mirror (G (mirror y) (unitVector j)) := by
    intro j
    have hL1 : LocallyIntegrable (fun y => G y (unitVector j)) volume := (hGj j).locallyIntegrable (by norm_num)
    have hL2 : LocallyIntegrable (fun y => sgn j • mirror (G (mirror y) (unitVector j))) volume := by
      have h1 : MemLp (fun y => mCL (G (mIso y) (unitVector j))) 2 volume :=
        mCL.comp_memLp' ((hGj j).comp_measurePreserving mIso.measurePreserving)
      exact (h1.const_smul (sgn j)).locallyIntegrable (by norm_num)
    refine ae_eq_of_integral_contDiff_smul_eq hL1 hL2 fun φ hφ hφs => ?_
    set e : Space := unitVector j with he
    set ψ : Space → ℝ := fun x => φ (mirror x) with hψ
    have hψt : IsTestScalar ψ := ⟨hφ.comp mCL.contDiff, hφs.comp_homeomorph mIso.toHomeomorph⟩
    have hψd : ∀ x, fderiv ℝ ψ x e = sgn j * fderiv ℝ φ (mirror x) e := by
      intro x
      have h1 : HasFDerivAt ψ ((fderiv ℝ φ (mCL x)).comp mCL) x :=
        ((hφ.differentiable (by simp)) (mCL x)).hasFDerivAt.comp x mCL.hasFDerivAt
      rw [h1.fderiv, ContinuousLinearMap.comp_apply, mCL_apply, mCL_apply, mirror_unit, map_smul, smul_eq_mul]
    have hw1 := hv.weak_gradient φ ⟨hφ, hφs⟩ j
    have hw2 := hv.weak_gradient ψ hψt j
    rw [← he] at hw1 hw2
    have hL : ∫ y, φ y • G y e = -∫ y, fderiv ℝ φ y e • v y := by
      rw [hw1, neg_neg]
    rw [hL]
    calc -∫ y, fderiv ℝ φ y e • v y
        = -∫ x, fderiv ℝ φ (mIso x) e • v (mIso x) := by
          rw [integral_mirror (fun y => fderiv ℝ φ y e • v y)]
      _ = -∫ x, fderiv ℝ φ (mirror x) e • mIso (v x) := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [hvm] with x hx
          rw [mIso_apply, hx]
          rfl
      _ = mIso (-∫ x, fderiv ℝ φ (mirror x) e • v x) := by
          rw [map_neg, ← integral_mIso]
          simp only [map_smul]
      _ = mIso (sgn j • -∫ x, fderiv ℝ ψ x e • v x) := by
          congr 1
          simp_rw [hψd, mul_smul, integral_smul, smul_neg, smul_smul, sgn_sq, one_smul]
      _ = mIso (sgn j • ∫ x, ψ x • G x e) := by
          rw [hw2, neg_neg]
      _ = mIso (∫ x, (sgn j * φ (mIso (mIso x))) • G (mIso x) e) := by
          congr 1
          have h3 := integral_mirror (fun y => (sgn j * φ (mIso y)) • G y e)
          rw [h3, ← integral_smul]
          congr 1
          funext x
          rw [mul_smul]
          rfl
      _ = ∫ x, mIso ((sgn j * φ (mIso (mIso x))) • G (mIso x) e) :=
          (integral_mIso _).symm
      _ = ∫ y, φ y • (sgn j • mirror (G (mirror y) e)) := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp only [mIso_apply, mm]
          rw [mirror_smul', smul_smul, mul_comm]
  filter_upwards [ae_all_iff.2 hcol] with y hy w
  have hb : ∀ j : Fin 3, G (mirror y) (mirror (unitVector j)) = mirror (G y (unitVector j)) := by
    intro j
    rw [hy j, mirror_unit, map_smul, mirror_smul', mm]
  show G (mirror y) (mIso w) = mIso (G y w)
  rw [vec_eq w]
  simp only [map_sum, map_smul, mIso_apply, hb]

end FrameMirrorLeaves

end FracInternal

end Breakdown
