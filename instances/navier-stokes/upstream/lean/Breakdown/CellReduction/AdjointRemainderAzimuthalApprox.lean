import Breakdown.CellReduction.AdjointRemainderAzimuthalParts
import Breakdown.FracCell.ReductionAdjointFrameMirrorLeaves
import Breakdown.FracCell.ReductionAdjointMollifySecondApprox

open scoped ENNReal ContDiff Convolution
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

namespace WeakClassApprox.Internal

open SteadyCert CellCert.Reduction.MollifySecondApproxInternal FracInternal.FrameMirrorLeaves

theorem weakGradientOf_of_weakGradient {V : Space → Space} {D : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient V D) : IsWeakGradientOf V D := by
  intro φ hφ j
  rw [h.2.2 φ hφ j, neg_neg]

theorem entrySq_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ entrySq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem entrySq_continuous : Continuous entrySq := by
  unfold entrySq
  fun_prop

theorem entrySq_add_le' (A B : Space →L[ℝ] Space) : entrySq (A + B) ≤ 2 * entrySq A + 2 * entrySq B := by
  unfold entrySq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ContinuousLinearMap.add_apply]
  have h := norm_add_le (A (unitVector i)) (B (unitVector i))
  have h0 := norm_nonneg (A (unitVector i) + B (unitVector i))
  nlinarith [norm_nonneg (A (unitVector i)), norm_nonneg (B (unitVector i)),
    sq_nonneg (‖A (unitVector i)‖ - ‖B (unitVector i)‖)]

theorem conv_eq_on_ball (n : ℕ) (v : Space → Space) (R : ℝ) {y : Space} (hy : y ∈ Metric.ball (0 : Space) R) :
    ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) y =
      ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (Metric.ball (0 : Space) (R + 1)).indicator v) y := by
  rw [convolution_def, convolution_def]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  by_cases ht : (kernelBump n).normed volume t = 0
  · simp [ht]
  · have hts : t ∈ Metric.ball (0 : Space) (kernelBump n).rOut := by
      rw [← (kernelBump n).support_normed_eq (μ := volume)]
      exact ht
    have hr := kernelBump_rOut_le n
    have hmem : y - t ∈ Metric.ball (0 : Space) (R + 1) := by
      rw [Metric.mem_ball, dist_zero_right] at hy hts ⊢
      calc ‖y - t‖ ≤ ‖y‖ + ‖t‖ := norm_sub_le y t
        _ < R + 1 := by linarith
    simp only [Set.indicator_of_mem hmem]

theorem smoothStep (V : Space → Space) (D : Space → (Space →L[ℝ] Space))
    (hD : AEStronglyMeasurable D volume) (hw : IsWeakGradientOf V D)
    (h6 : MemLp V 6 volume) (hE : Integrable (fun y => entrySq (D y))) :
    ∃ w : ℕ → Space → Space,
      (∀ n, ContDiff ℝ ∞ (w n) ∧ MemLp (w n) 6 volume ∧ Integrable (fun y => entrySq (fderiv ℝ (w n) y))) ∧
      Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - D y))) atTop (𝓝 0) ∧
      ∀ R : ℝ, Tendsto (fun n => ∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖w n y - V y‖ ^ 2))
        atTop (𝓝 0) := by
  have hloc : LocallyIntegrable V volume := h6.locallyIntegrable (by norm_num)
  have hGm : ∀ j : Fin 3, AEStronglyMeasurable (fun y => D y (unitVector j)) volume := fun j =>
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hD
  have hGc : ∀ j : Fin 3, Integrable (fun z => ‖D z (unitVector j)‖ ^ 2) := fun j =>
    hE.mono' ((hGm j).norm.pow 2) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [entrySq]
      exact Finset.single_le_sum (f := fun i => ‖D z (unitVector i)‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j))
  have hGj : ∀ j : Fin 3, MemLp (fun y => D y (unitVector j)) 2 volume := fun j =>
    (memLp_two_iff_integrable_sq_norm (hGm j)).2 (hGc j)
  have h6' : MemLp V ((6 : ℕ) : ENNReal) volume := by exact_mod_cast h6
  have hI6 : Integrable (fun z => ‖V z‖ ^ 6) := h6'.integrable_norm_pow (by norm_num)
  have hρi : ∀ n, Integrable ((kernelBump n).normed volume) := fun n => (kernelBump n).integrable_normed
  have hwc : ∀ n, ContDiff ℝ ∞ ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) :=
    fun n => ((kernelBump n).hasCompactSupport_normed).contDiff_convolution_left _ (kernelBump n).contDiff_normed hloc
  have hEpt : ∀ n y, entrySq (fderiv ℝ ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) y) ≤
      ∑ j : Fin 3, ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun z => ‖D z (unitVector j)‖ ^ 2) y := by
    intro n y
    simp only [entrySq, mollify_fderiv_apply' (kernelBump n) V D hloc hw y]
    exact Finset.sum_le_sum fun j _ => normPow_conv_le (kernelBump n) _ 2 (by norm_num) (hGc j) y
  have hSi : ∀ n, Integrable (fun y => ∑ j : Fin 3, ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun z => ‖D z (unitVector j)‖ ^ 2) y) := fun n =>
    integrable_finsetSum _ fun j _ => (hρi n).integrable_convolution _ (hGc j)
  have hEc : ∀ n, Continuous (fun y =>
      entrySq (fderiv ℝ ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) y)) := fun n =>
    entrySq_continuous.comp ((hwc n).continuous_fderiv (by simp))
  refine ⟨fun n => (kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V,
    fun n => ⟨hwc n, ?_, ?_⟩, ?_, ?_⟩
  · have hm : AEStronglyMeasurable ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) volume :=
      (hwc n).continuous.aestronglyMeasurable
    have hi : Integrable (fun y => ‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V) y‖ ^ 6) :=
      ((hρi n).integrable_convolution _ hI6).mono' (hm.norm.pow 6) (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact normPow_conv_le (kernelBump n) V 6 (by norm_num) hI6 y)
    refine (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).1 ?_
    simpa using hi
  · exact (hSi n).mono' (hEc n).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
      exact hEpt n y)
  · have hcol : ∀ j : Fin 3, Tendsto (fun n => ∫⁻ y, ENNReal.ofReal
        (‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => D z (unitVector j)) y -
          D y (unitVector j)‖ ^ 2)) atTop (𝓝 0) := fun j => mollifierL2 kernelBump kernelBump_rOut _ (hGj j)
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => hcol j
    simp only [Finset.sum_const_zero] at hsum
    refine hsum.congr fun n => ?_
    have hmj : ∀ j : Fin 3, AEMeasurable (fun y => ENNReal.ofReal
        (‖((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => D z (unitVector j)) y -
          D y (unitVector j)‖ ^ 2)) volume := by
      intro j
      have hcc : Continuous ((kernelBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun z => D z (unitVector j)) :=
        ((kernelBump n).hasCompactSupport_normed).continuous_convolution_left _ (kernelBump n).continuous_normed
          ((hGj j).locallyIntegrable (by norm_num))
      exact ((hcc.aestronglyMeasurable.sub (hGm j)).norm.pow 2).aemeasurable.ennreal_ofReal
    rw [← lintegral_finsetSum' _ fun j _ => hmj j]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
    congr 1
    simp only [entrySq, ContinuousLinearMap.sub_apply, mollify_fderiv_apply' (kernelBump n) V D hloc hw y]
  · intro R
    have hf : MemLp ((Metric.ball (0 : Space) (R + 1)).indicator V) 2 volume := by
      have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Space) (R + 1))) :=
        isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
      rw [memLp_indicator_iff_restrict measurableSet_ball]
      exact (h6.restrict _).mono_exponent (by norm_num)
    have ht := mollifierL2 kernelBump kernelBump_rOut _ hf
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) fun n => ?_
    refine le_trans (le_of_eq (setLIntegral_congr_fun measurableSet_ball fun y hy => ?_))
      (setLIntegral_le_lintegral _ _)
    have hy1 : y ∈ Metric.ball (0 : Space) (R + 1) := by
      rw [Metric.mem_ball, dist_zero_right] at hy ⊢
      linarith
    beta_reduce
    rw [conv_eq_on_ball n V R hy, Set.indicator_of_mem hy1]

theorem cutStep (V : Space → Space) (D : Space → (Space →L[ℝ] Space))
    (hD : AEStronglyMeasurable D volume) (w : ℕ → Space → Space)
    (hw : ∀ n, ContDiff ℝ ∞ (w n) ∧ MemLp (w n) 6 volume ∧ Integrable (fun y => entrySq (fderiv ℝ (w n) y)))
    (hgrad : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - D y))) atTop (𝓝 0))
    (hball : ∀ R : ℝ, Tendsto (fun n => ∫⁻ y in Metric.ball (0 : Space) R, ENNReal.ofReal (‖w n y - V y‖ ^ 2))
        atTop (𝓝 0)) :
    ∃ u : ℕ → Space → Space, (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n)) ∧
      Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (u n) y - D y))) atTop (𝓝 0) ∧
      ∀ R : ℝ, Tendsto (fun n => ∫⁻ y in Metric.ball (0 : Space) R,
        ENNReal.ofReal (‖u n y - V y‖ ^ 2)) atTop (𝓝 0) := by
  have hR : ∀ n : ℕ, ∃ R : ℝ, (n : ℝ) + 1 ≤ R ∧
      ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (fun z => radialCutoff R z • w n z) y - fderiv ℝ (w n) y)) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    have h := (cutoffGradient (w n) (hw n).1 (hw n).2.1 (hw n).2.2).eventually
      (Iic_mem_nhds (ENNReal.ofReal_pos.2 (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)))
    exact ((eventually_ge_atTop ((n : ℝ) + 1)).and h).exists
  choose R hR1 hR2 using hR
  have hRpos : ∀ n, 0 < R n := fun n => lt_of_lt_of_le (by positivity) (hR1 n)
  refine ⟨fun n z => radialCutoff (R n) z • w n z, fun n => ⟨(contDiff_radialCutoff (hRpos n)).smul (hw n).1,
    (hasCompactSupport_radialCutoff (hRpos n)).smul_right⟩, ?_, fun ρ => ?_⟩
  · have hmeas : ∀ n, AEMeasurable (fun y => 2 * ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - D y))) volume := by
      intro n
      have hc : Continuous (fderiv ℝ (w n)) := (hw n).1.continuous_fderiv (by simp)
      exact ((entrySq_continuous.comp_aestronglyMeasurable
        (hc.aestronglyMeasurable.sub hD)).aemeasurable.ennreal_ofReal).const_mul 2
    have hbd : ∀ n, ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y - D y)) ≤
        2 * ENNReal.ofReal (1 / ((n : ℝ) + 1)) + 2 * ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - D y)) := by
      intro n
      calc _ ≤ ∫⁻ y, (2 * ENNReal.ofReal (entrySq (fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y -
              fderiv ℝ (w n) y)) + 2 * ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - D y))) := by
            refine lintegral_mono fun y => ?_
            have e : fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y - D y =
                (fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y - fderiv ℝ (w n) y) + (fderiv ℝ (w n) y - D y) := by
              abel
            rw [e]
            refine (ENNReal.ofReal_le_ofReal (entrySq_add_le' _ _)).trans (le_of_eq ?_)
            have a1 := entrySq_nonneg' (fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y - fderiv ℝ (w n) y)
            have a2 := entrySq_nonneg' (fderiv ℝ (w n) y - D y)
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        _ = 2 * (∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (fun z => radialCutoff (R n) z • w n z) y -
              fderiv ℝ (w n) y))) + 2 * ∫⁻ y, ENNReal.ofReal (entrySq (fderiv ℝ (w n) y - D y)) := by
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

end WeakClassApprox.Internal

open SteadyCert WeakClassApprox.Internal in
theorem weakClassApprox : WeakClassApproxHolds := by
  intro V D hV hD hw h6 hE
  have hI6 : Integrable (fun y => ‖V y‖ ^ 6) :=
    ⟨(hV.norm.pow 6), (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => by positivity)).2 h6⟩
  have hM6 : MemLp V 6 volume := by
    refine (integrable_norm_rpow_iff hV (by norm_num) (by norm_num)).1 ?_
    simpa using hI6
  have hEi : Integrable (fun y => entrySq (D y)) :=
    ⟨entrySq_continuous.comp_aestronglyMeasurable hD,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => entrySq_nonneg' (D y))).2 hE⟩
  obtain ⟨w, hwp, hgrad, hball⟩ := smoothStep V D hD (weakGradientOf_of_weakGradient hw) hM6 hEi
  exact cutStep V D hD w hwp hgrad hball

end AzimuthalParts

end AdjointDefect

end Breakdown
