import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal NNReal Convolution
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal.WeakFieldMollify

theorem integrable_of_lintegral_lt {F : Space → ℝ} (hm : AEStronglyMeasurable F volume)
    (h0 : ∀ y, 0 ≤ F y) (h : (∫⁻ y, ENNReal.ofReal (F y)) < ⊤) : Integrable F :=
  ⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)).2 h⟩

theorem kernel_pow_le (φ : ContDiffBump (0 : Space)) (f : Space → Space) (k : ℕ) (hk : 1 ≤ k)
    (hf : Integrable (fun z => ‖f z‖ ^ k)) (y : Space) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ k ≤
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => ‖f z‖ ^ k) y := by
  have hρ0 : ∀ t, 0 ≤ φ.normed volume t := φ.nonneg_normed
  have hm : Measurable (fun t => (φ.normed volume t).toNNReal) :=
    φ.continuous_normed.measurable.real_toNNReal
  let μ : Measure Space := volume.withDensity (fun t => ((φ.normed volume t).toNNReal : ℝ≥0∞))
  have hμ : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    simp only [μ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    change ∫⁻ t, ENNReal.ofReal (φ.normed volume t) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal (φ.integrable_normed (μ := volume)) (ae_of_all _ hρ0),
      φ.integral_normed (μ := volume), ENNReal.ofReal_one]
  have hvec : ∀ g : Space → Space, ∫ t, g t ∂μ = ∫ t, φ.normed volume t • g t := by
    intro g
    rw [integral_withDensity_eq_integral_smul hm]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hρ0 t)]
  have hsc : ∀ g : Space → ℝ, ∫ t, g t ∂μ = ∫ t, φ.normed volume t • g t := by
    intro g
    rw [integral_withDensity_eq_integral_smul hm]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hρ0 t)]
  rw [convolution_def, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [← hvec (fun t => f (y - t)), ← hsc (fun t => ‖f (y - t)‖ ^ k)]
  by_cases hi : Integrable (fun t => f (y - t)) μ
  · have hex := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left (μ := volume)
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hf.locallyIntegrable y
    have hpi : Integrable (fun t => ‖f (y - t)‖ ^ k) μ := by
      refine (integrable_withDensity_iff_integrable_smul hm).2 ?_
      refine hex.integrable.congr (ae_of_all _ fun t => ?_)
      simp only [ContinuousLinearMap.lsmul_apply, NNReal.smul_def, Real.coe_toNNReal _ (hρ0 t)]
    exact ((convexOn_norm convex_univ).pow (fun x _ => norm_nonneg x) k).map_integral_le
      (continuous_norm.pow k).continuousOn isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hi hpi
  · rw [integral_undef hi, norm_zero, zero_pow (by omega)]
    exact integral_nonneg fun t => by positivity

theorem kernel_pow_integral (φ : ContDiffBump (0 : Space)) (f : Space → Space) (k : ℕ) (hk : 1 ≤ k)
    (hfl : LocallyIntegrable f volume) (hf : Integrable (fun z => ‖f z‖ ^ k)) :
    Integrable (fun y => ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ k) ∧
      (∫ y, ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ k) ≤
        ∫ y, ‖f y‖ ^ k := by
  have hI : Integrable (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      fun z => ‖f z‖ ^ k) := φ.integrable_normed.integrable_convolution _ hf
  have hc : Continuous (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) :=
    (φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ.contDiff_normed (n := 0)) hfl).continuous
  have hle := kernel_pow_le φ f k hk hf
  have hJ : Integrable (fun y => ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y‖ ^ k) :=
    hI.mono' (hc.norm.pow k).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle y)
  refine ⟨hJ, (integral_mono hJ hI hle).trans_eq ?_⟩
  rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) φ.integrable_normed hf]
  simp [ContDiffBump.integral_normed]

theorem fderiv_kernel_apply (φ : ContDiffBump (0 : Space)) (f : Space → Space)
    (g : Space → (Space →L[ℝ] Space)) (hfg : IsWeakGradient f g) (y : Space) (i : Fin 3) :
    fderiv ℝ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) y (unitVector i) =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => g z (unitVector i)) y := by
  have hc : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hs : ContDiff ℝ ∞ (φ.normed volume) := φ.contDiff_normed
  rw [(hc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hs.of_le (by simp))
    hfg.1 y).fderiv]
  have hex := (hc.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).precompL Space)
    (hs.continuous_fderiv (by simp)) hfg.1 y
  rw [convolution_eq_swap, ContinuousLinearMap.integral_apply hex.integrable_swap,
    convolution_eq_swap]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  have hψ : IsTestFunction (fun s => φ.normed volume (y - s)) :=
    ⟨hs.comp (contDiff_const.sub contDiff_id), hc.comp_homeomorph (Homeomorph.subLeft y)⟩
  have hd : ∀ s, fderiv ℝ (fun s => φ.normed volume (y - s)) s (unitVector i) =
      -fderiv ℝ (φ.normed volume) (y - s) (unitVector i) := by
    intro s
    have h1 : HasFDerivAt (φ.normed volume) (fderiv ℝ (φ.normed volume) (y - s)) (y - s) :=
      ((hs.differentiable (by simp)) (y - s)).hasFDerivAt
    have h2 : HasFDerivAt (fun s => φ.normed volume (y - s))
        ((fderiv ℝ (φ.normed volume) (y - s)).comp (-ContinuousLinearMap.id ℝ Space)) s :=
      h1.comp s ((hasFDerivAt_id s).const_sub y)
    rw [h2.fderiv]
    simp
  have hw := hfg.2.2 _ hψ i
  simp only [hd, neg_smul, integral_neg, neg_neg] at hw
  exact hw.symm

theorem second_diag_eq (u : Space → Space) (hu : ContDiff ℝ ∞ u) (y : Space) (i : Fin 3) :
    iteratedFDeriv ℝ 2 u y ![unitVector i, unitVector i] =
      fderiv ℝ (fun z => fderiv ℝ u z (unitVector i)) y (unitVector i) := by
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ u) y :=
    ((contDiff_infty_iff_fderiv.1 hu).2.differentiable (by simp)) y
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

end Internal.WeakFieldMollify

open Internal.WeakFieldMollify

theorem weakFieldMollify (w : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (hG : IsWeakGradient w G)
    (hH : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j))
      (fun y => (H y).flip (unitVector j)))
    (hw : (∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6)) < ⊤)
    (hGs : (∫⁻ y, ENNReal.ofReal (matSq (G y))) < ⊤)
    (hHs : (∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H y)‖ ^ 2)) < ⊤) :
    ∃ u : ℕ → Space → Space,
      (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, MemLp (u n) 6 volume) ∧
      (∀ n, Integrable (fun y => matSq (fderiv ℝ (u n) y))) ∧
      (∀ n, Integrable (fun y => ‖sumSecondPartialsAt (u n) y‖ ^ 2)) ∧
      (∀ n, (∫ y, matSq (fderiv ℝ (u n) y)) ≤ ∫ y, matSq (G y)) ∧
      (∀ n, (∫ y, ‖sumSecondPartialsAt (u n) y‖ ^ 2) ≤ ∫ y, ‖secondDerivTrace (H y)‖ ^ 2) ∧
      ∀ᵐ y, Tendsto (fun n => u n y) atTop (𝓝 (w y)) := by
  have hwl : LocallyIntegrable w volume := hG.1
  have hGl : ∀ i : Fin 3, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i => (hH i).1
  have hDl : ∀ i : Fin 3, LocallyIntegrable (fun y => H y (unitVector i) (unitVector i)) volume :=
    fun i x => by
      have h := (ContinuousLinearMap.apply ℝ Space (unitVector i)).integrableAtFilter_comp ((hH i).2.1 x)
      simpa [Function.comp_def] using h
  have hTl : LocallyIntegrable (fun y => secondDerivTrace (H y)) volume := by
    have e : (fun y => secondDerivTrace (H y)) =
        fun y => ∑ i ∈ Finset.univ, H y (unitVector i) (unitVector i) := rfl
    rw [e]
    exact locallyIntegrable_finsetSum Finset.univ fun i _ => hDl i
  have hw6 : Integrable (fun y => ‖w y‖ ^ 6) :=
    integrable_of_lintegral_lt (hwl.aestronglyMeasurable.norm.pow 6) (fun y => by positivity) hw
  have hG2 : ∀ i : Fin 3, Integrable (fun y => ‖G y (unitVector i)‖ ^ 2) := by
    intro i
    refine integrable_of_lintegral_lt ((hGl i).aestronglyMeasurable.norm.pow 2) (fun y => by positivity)
      (lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_) hGs)
    exact Finset.single_le_sum (f := fun j => ‖G y (unitVector j)‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  have hT2 : Integrable (fun y => ‖secondDerivTrace (H y)‖ ^ 2) :=
    integrable_of_lintegral_lt (hTl.aestronglyMeasurable.norm.pow 2) (fun y => by positivity) hHs
  let φ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / ((n : ℝ) + 1) / 2, 1 / ((n : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith⟩
  let u : ℕ → Space → Space := fun n =>
    (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w
  have hu : ∀ n, ContDiff ℝ ∞ (u n) := fun n =>
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed hwl
  have hfd : ∀ n i, (fun y => fderiv ℝ (u n) y (unitVector i)) =
      (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => G z (unitVector i) :=
    fun n i => funext fun y => fderiv_kernel_apply (φ n) w G hG y i
  have hlap : ∀ n, sumSecondPartialsAt (u n) =
      (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => secondDerivTrace (H z) := by
    intro n
    funext y
    have e : ∀ i, iteratedFDeriv ℝ 2 (u n) y ![unitVector i, unitVector i] =
        ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          fun z => H z (unitVector i) (unitVector i)) y := by
      intro i
      rw [second_diag_eq (u n) (hu n) y i, hfd n i,
        fderiv_kernel_apply (φ n) _ _ (hH i) y i]
      simp only [ContinuousLinearMap.flip_apply]
    have hex : ∀ i, Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) ((φ n).normed volume t)
        (H (y - t) (unitVector i) (unitVector i))) := fun i =>
      (((φ n).hasCompactSupport_normed (μ := volume)).convolutionExists_left (μ := volume)
        (ContinuousLinearMap.lsmul ℝ ℝ) ((φ n).continuous_normed (μ := volume)) (hDl i) y).integrable
    simp only [sumSecondPartialsAt, e, convolution_def]
    rw [← integral_finsetSum _ fun i _ => hex i]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp [secondDerivTrace]
  refine ⟨u, hu, fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · have h := (kernel_pow_integral (φ n) w 6 (by norm_num) hwl hw6).1
    rw [← integrable_norm_rpow_iff (hu n).continuous.aestronglyMeasurable (by norm_num) (by norm_num)]
    have h6 : ((6 : ℝ≥0∞).toReal) = ((6 : ℕ) : ℝ) := by norm_num
    simp_rw [h6, Real.rpow_natCast]
    exact h
  · have e : (fun y => matSq (fderiv ℝ (u n) y)) =
        fun y => ∑ i : Fin 3, ‖fderiv ℝ (u n) y (unitVector i)‖ ^ 2 := rfl
    rw [e]
    refine integrable_finsetSum _ fun i _ => ?_
    have h := (kernel_pow_integral (φ n) _ 2 (by norm_num) (hGl i) (hG2 i)).1
    rw [← hfd n i] at h
    exact h
  · rw [hlap n]
    exact (kernel_pow_integral (φ n) _ 2 (by norm_num) hTl hT2).1
  · have e : (fun y => matSq (fderiv ℝ (u n) y)) =
        fun y => ∑ i : Fin 3, ‖fderiv ℝ (u n) y (unitVector i)‖ ^ 2 := rfl
    have e2 : (fun y => matSq (G y)) = fun y => ∑ i : Fin 3, ‖G y (unitVector i)‖ ^ 2 := rfl
    have hk : ∀ i : Fin 3, Integrable (fun y => ‖fderiv ℝ (u n) y (unitVector i)‖ ^ 2) ∧
        (∫ y, ‖fderiv ℝ (u n) y (unitVector i)‖ ^ 2) ≤ ∫ y, ‖G y (unitVector i)‖ ^ 2 := by
      intro i
      have h := kernel_pow_integral (φ n) _ 2 (by norm_num) (hGl i) (hG2 i)
      rw [← hfd n i] at h
      exact h
    rw [e, e2, integral_finsetSum _ fun i _ => (hk i).1, integral_finsetSum _ fun i _ => hG2 i]
    exact Finset.sum_le_sum fun i _ => (hk i).2
  · rw [hlap n]
    exact (kernel_pow_integral (φ n) _ 2 (by norm_num) hTl hT2).2
  · refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := φ) (K := 2) ?_ ?_ hwl
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Eventually.of_forall fun n => le_of_eq (by
        show 1 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1) / 2)
        ring)

end CertReduction

end Breakdown
