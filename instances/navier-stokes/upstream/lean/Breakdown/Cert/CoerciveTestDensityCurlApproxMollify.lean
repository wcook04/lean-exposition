import Breakdown.Cert.CoerciveTestDensityCurlApproxBase

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.Coercive

namespace Internal.CurlGraphMollify

open Internal.TestDensityProof

private theorem exists_curl_clm : ∃ Λ : (Space →L[ℝ] Space) →L[ℝ] Space, ∀ A, Λ A = curlVec A := by
  refine ⟨∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
    ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Space (unitVector j))).smulRight
        (alternatingSymbol i j l • unitVector i), fun A => ?_⟩
  simp only [curlVec, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.apply_apply, smul_smul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]
  rfl

private theorem exists_div_clm : ∃ Λ : (Space →L[ℝ] Space) →L[ℝ] ℝ, ∀ A,
    Λ A = ∑ i : Fin 3, A (unitVector i) i := by
  refine ⟨∑ i : Fin 3, (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Space (unitVector i)), fun A => ?_⟩
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.apply_apply]
  rfl

private theorem kern_contDiff (k : ℕ) : ContDiff ℝ ∞ (kern k) := (bump k).contDiff_normed

private theorem kern_hasCompactSupport (k : ℕ) : HasCompactSupport (kern k) := (bump k).hasCompactSupport_normed

private theorem kern_locallyIntegrable (k : ℕ) : LocallyIntegrable (kern k) volume :=
  (kern_contDiff k).continuous.locallyIntegrable

private theorem kern_eq_zero (k : ℕ) {t : Space} (ht : 1 ≤ ‖t‖) : kern k t = 0 := by
  have hs : t ∉ Function.support (kern k) := by
    unfold kern
    rw [(bump k).support_normed_eq, Metric.mem_ball, dist_zero_right, not_lt]
    refine le_trans ?_ ht
    show 1 / ((k : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  simpa using hs

private theorem moll_vanish (k : ℕ) {X : ℝ → Space → Space} {R : ℝ} (hR : ∀ σ y, R < ‖y‖ → X σ y = 0)
    (σ : ℝ) (y : Space) (hy : R + 1 < ‖y‖) : moll k X σ y = 0 := by
  unfold moll
  rw [convolution_def]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, Pi.zero_apply]
  by_cases ht : 1 ≤ ‖t‖
  · rw [kern_eq_zero k ht, zero_smul]
  · have : R < ‖y - t‖ := by
      have := norm_sub_norm_le y t
      linarith
    rw [hR σ (y - t) this, smul_zero]

private theorem slice_fderiv_eq {F : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (σ : ℝ) (y : Space) :
    fderiv ℝ (F σ) y = (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (σ, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => F z.1 z.2) (σ, y) :=
    (hF.differentiable (by simp)) _
  have h := hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)
  exact h.fderiv

private theorem continuous_slice_fderiv {F : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) := by
  have e : (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) = fun z =>
      (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact slice_fderiv_eq hF z.1 z.2
  rw [e]
  exact (hF.continuous_fderiv (by simp)).clm_comp continuous_const

private theorem continuous_slice_curl {F : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) :
    Continuous (fun z : ℝ × Space => curlVec (fderiv ℝ (F z.1) z.2)) := by
  obtain ⟨Λ, hΛ⟩ := exists_curl_clm
  simp_rw [← hΛ]
  exact Λ.continuous.comp (continuous_slice_fderiv hF)

theorem aestronglyMeasurable_curl_of_contDiff {F : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) :
    AEStronglyMeasurable (fun z : ℝ × Space => curlVec (fderiv ℝ (F z.1) z.2)) periodMeasure :=
  (continuous_slice_curl hF).aestronglyMeasurable

theorem isPeriodicTestField_moll (k : ℕ) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    IsPeriodicTestField (moll k ψ) := by
  obtain ⟨hs, hper, ⟨R, hR⟩, hdiv⟩ := hψ
  have hgs : ∀ p, ∀ x, p ∈ (univ : Set ℝ) → x ∉ Metric.closedBall (0 : Space) R → ψ p x = 0 := by
    intro p x _ hx
    refine hR p x ?_
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hsm : ContDiff ℝ ∞ (fun z : ℝ × Space => moll k ψ z.1 z.2) := by
    have h := contDiffOn_convolution_right_with_param (μ := volume) (n := ⊤)
      (ContinuousLinearMap.lsmul ℝ ℝ) (f := kern k) (g := ψ) (s := univ)
      isOpen_univ (isCompact_closedBall (0 : Space) R) hgs (kern_locallyIntegrable k)
      hs.contDiffOn
    rw [univ_prod_univ, contDiffOn_univ] at h
    exact h
  refine ⟨hsm, fun σ y => ?_, ⟨R + 1, moll_vanish k hR⟩, fun σ y => ?_⟩
  · unfold moll
    rw [show ψ (σ + 1) = ψ σ from funext (hper σ)]
  · have hc : ContDiff ℝ ∞ (ψ σ) := hs.comp (contDiff_prodMk_right σ)
    have hcs : HasCompactSupport (ψ σ) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun x hx => ?_
      exact hgs σ x (mem_univ _) hx
    have hd := hcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (kern_locallyIntegrable k) (hc.of_le (by simp)) y
    have hex := hcs.fderiv ℝ |>.convolutionExists_right
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompR Space) (kern_locallyIntegrable k)
      (hc.continuous_fderiv (by simp)) y
    obtain ⟨Λ, hΛ⟩ := exists_div_clm
    unfold divergenceAt moll
    rw [hd.fderiv, ← hΛ, convolution_def, ← Λ.integral_comp_comm hex]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    have h0 := hdiv σ (y - t)
    unfold divergenceAt at h0
    dsimp only
    rw [hΛ]
    simp only [ContinuousLinearMap.precompR, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.lsmul_apply,
      PiLp.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, h0, mul_zero]
    rfl

private theorem quasiMeasurePreserving_shear :
    Measure.QuasiMeasurePreserving (fun p : (ℝ × Space) × Space => (p.1.1, p.1.2 - p.2))
      (periodMeasure.prod (volume : Measure Space)) periodMeasure := by
  have hm : Measurable (fun p : (ℝ × Space) × Space => (p.1.1, p.1.2 - p.2)) := by fun_prop
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_⟩
  rw [Measure.map_apply hm hS, Measure.prod_apply_symm (hm hS)]
  refine (lintegral_congr (g := fun _ => 0) fun t => ?_).trans lintegral_zero
  have hT : MeasurePreserving (Prod.map (id : ℝ → ℝ) (fun y : Space => y - t)) periodMeasure
      periodMeasure := (MeasurePreserving.id _).prod (measurePreserving_sub_right volume t)
  have e := hT.measure_preimage hS.nullMeasurableSet
  rw [← h0, ← e]
  rfl

private theorem aestronglyMeasurable_conv_param {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {f : Space → E} (hf : Continuous f)
    (L : E →L[ℝ] Space →L[ℝ] F') {X : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) periodMeasure) :
    AEStronglyMeasurable (fun z : ℝ × Space => convolution f (X z.1) L volume z.2) periodMeasure := by
  have h1 : AEStronglyMeasurable (fun p : (ℝ × Space) × Space => X p.1.1 (p.1.2 - p.2))
      (periodMeasure.prod (volume : Measure Space)) :=
    hX.comp_quasiMeasurePreserving quasiMeasurePreserving_shear
  have h2 : AEStronglyMeasurable (fun p : (ℝ × Space) × Space => f p.2)
      (periodMeasure.prod (volume : Measure Space)) := (hf.comp continuous_snd).aestronglyMeasurable
  have h3 := L.continuous₂.comp_aestronglyMeasurable₂ h2 h1
  have h4 := h3.integral_prod_right'
  simp only [convolution_def]
  exact h4

theorem aestronglyMeasurable_moll (k : ℕ) {X : ℝ → Space → Space}
    (hX : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure) :
    AEStronglyMeasurable (fun z : ℝ × Space => moll k X z.1 z.2) periodMeasure :=
  aestronglyMeasurable_conv_param (kern_contDiff k).continuous (ContinuousLinearMap.lsmul ℝ ℝ) hX.1

private theorem slice_memLp' {X : ℝ → Space → Space}
    (hX : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure) :
    ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), MemLp (X σ) 2 volume := by
  have hi := (memLp_two_iff_integrable_sq_norm hX.1).1 hX
  filter_upwards [hX.1.prodMk_left, hi.prod_right_ae] with σ h1 h2
  exact (memLp_two_iff_integrable_sq_norm h1).2 h2

theorem aestronglyMeasurable_curl_moll (k : ℕ) {X : ℝ → Space → Space}
    (hX : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure) :
    AEStronglyMeasurable (fun z : ℝ × Space => curlVec (fderiv ℝ (moll k X z.1) z.2))
      periodMeasure := by
  obtain ⟨Λ, hΛ⟩ := exists_curl_clm
  have hm := aestronglyMeasurable_conv_param ((kern_contDiff k).continuous_fderiv (by simp))
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Space) hX.1
  refine (Λ.continuous.comp_aestronglyMeasurable hm).congr ?_
  have hs : ∀ᵐ z ∂periodMeasure, MemLp (X z.1) 2 volume :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst (slice_memLp' hX)
  filter_upwards [hs] with z hz
  have hd := (kern_hasCompactSupport k).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((kern_contDiff k).of_le (by simp))
    (hz.locallyIntegrable (by norm_num)) z.2
  unfold moll
  rw [hd.fderiv, hΛ]

private theorem moll_uniform {ψ : ℝ → Space → Space}
    (hc : Continuous (fun z : ℝ × Space => ψ z.1 z.2)) {R : ℝ} (hR : ∀ σ y, R < ‖y‖ → ψ σ y = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ σ ∈ Icc (0 : ℝ) 1, ∀ y, ‖moll k ψ σ y - ψ σ y‖ ≤ ε := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) (R + 1)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hc.continuousOn) ε hε
  have hev : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < min δ 1 := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h0.eventually (gt_mem_nhds (lt_min hδ one_pos))
  filter_upwards [hev] with k hk σ hσ y
  have hk1 : 1 / ((k : ℝ) + 1) < δ := lt_of_lt_of_le hk (min_le_left _ _)
  have hk2 : 1 / ((k : ℝ) + 1) < 1 := lt_of_lt_of_le hk (min_le_right _ _)
  rw [← dist_eq_norm]
  refine (bump k).dist_normed_convolution_le (μ := volume) (g := ψ σ)
    (hc.comp (Continuous.prodMk_right σ)).aestronglyMeasurable fun x hx => ?_
  have hxy : dist x y < 1 / ((k : ℝ) + 1) := hx
  by_cases h : ‖x‖ ≤ R + 1 ∧ ‖y‖ ≤ R + 1
  · refine (hU (σ, x) ⟨hσ, by simpa using h.1⟩ (σ, y) ⟨hσ, by simpa using h.2⟩ ?_).le
    rw [Prod.dist_eq, dist_self]
    exact max_lt hδ (lt_trans hxy hk1)
  · have hn : R < ‖x‖ ∧ R < ‖y‖ := by
      have t1 := norm_sub_norm_le x y
      have t2 := norm_sub_norm_le y x
      rw [← dist_eq_norm] at t1
      rw [← dist_eq_norm, dist_comm] at t2
      rw [not_and_or, not_le, not_le] at h
      rcases h with h | h
      · constructor <;> linarith
      · constructor <;> linarith
    show dist (ψ σ x) (ψ σ y) ≤ ε
    rw [hR σ x hn.1, hR σ y hn.2, dist_self]
    exact hε.le

private theorem moll_bound {ψ : ℝ → Space → Space}
    (hc : Continuous (fun z : ℝ × Space => ψ z.1 z.2)) {R : ℝ} (hR : ∀ σ y, R < ‖y‖ → ψ σ y = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, periodLIntegral (fun σ y => ‖moll k ψ σ y - ψ σ y‖ ^ 2) ≤
      ENNReal.ofReal (ε ^ 2) * volume (Metric.closedBall (0 : Space) (R + 1)) := by
  filter_upwards [moll_uniform hc hR hε] with k hk
  unfold periodLIntegral
  calc ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖moll k ψ σ y - ψ σ y‖ ^ 2)
      ≤ ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, (Metric.closedBall (0 : Space) (R + 1)).indicator
          (fun _ => ENNReal.ofReal (ε ^ 2)) y := by
        refine setLIntegral_mono' measurableSet_Icc fun σ hσ => lintegral_mono fun y => ?_
        by_cases hy : y ∈ Metric.closedBall (0 : Space) (R + 1)
        · rw [indicator_of_mem hy]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hk σ hσ y) 2)
        · rw [indicator_of_notMem hy]
          have hy' : R + 1 < ‖y‖ := by
            rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
            exact hy
          rw [moll_vanish k hR σ y hy', hR σ y (by linarith)]
          simp
    _ = ENNReal.ofReal (ε ^ 2) * volume (Metric.closedBall (0 : Space) (R + 1)) := by
        rw [lintegral_indicator_const measurableSet_closedBall, lintegral_const,
          Measure.restrict_apply_univ, Real.volume_Icc]
        simp

theorem moll_tendsto_of_continuous {ψ : ℝ → Space → Space}
    (hc : Continuous (fun z : ℝ × Space => ψ z.1 z.2)) (hR : ∃ R, ∀ σ y, R < ‖y‖ → ψ σ y = 0) :
    Tendsto (fun k => periodLIntegral (fun σ y => ‖moll k ψ σ y - ψ σ y‖ ^ 2)) atTop (nhds 0) := by
  obtain ⟨R, hR⟩ := hR
  set V := volume (Metric.closedBall (0 : Space) (R + 1))
  have hV : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hb : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / ((n : ℝ) + 1)) ^ 2) * V) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / ((n : ℝ) + 1)) ^ 2)) atTop (nhds 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := h0.pow 2
      simpa using ENNReal.tendsto_ofReal this
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hV)
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.1 hb) η hη).exists
  filter_upwards [moll_bound hc hR (ε := 1 / ((n : ℝ) + 1)) (by positivity)] with k hk
  exact hk.trans hn

private theorem precompR_lsmul_apply (a : ℝ) (B : Space →L[ℝ] Space) :
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompR Space a) B = a • B := by
  ext v i
  simp [ContinuousLinearMap.precompR]

private theorem curl_moll_eq {F : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) {R : ℝ}
    (hR : ∀ σ y, R < ‖y‖ → F σ y = 0) (k : ℕ) (σ : ℝ) (y : Space) :
    curlVec (fderiv ℝ (moll k F σ) y) = moll k (fun σ x => curlVec (fderiv ℝ (F σ) x)) σ y := by
  obtain ⟨Λ, hΛ⟩ := exists_curl_clm
  have hc : ContDiff ℝ 1 (F σ) := hF.comp (contDiff_prodMk_right σ)
  have hcs : HasCompactSupport (F σ) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun x hx => ?_
    refine hR σ x ?_
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hd := hcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (kern_locallyIntegrable k) hc y
  have hex := hcs.fderiv ℝ |>.convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompR Space) (kern_locallyIntegrable k)
    (hc.continuous_fderiv (by simp)) y
  unfold moll
  rw [hd.fderiv, ← hΛ, convolution_def, ← Λ.integral_comp_comm hex, convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [precompR_lsmul_apply, ← hΛ, map_smul, ContinuousLinearMap.lsmul_apply]

theorem curl_moll_tendsto {F : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (hR : ∃ R, ∀ σ y, R < ‖y‖ → F σ y = 0) :
    Tendsto (fun k => periodLIntegral (fun σ y =>
      ‖curlVec (fderiv ℝ (moll k F σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) atTop (nhds 0) := by
  obtain ⟨R, hR⟩ := hR
  have hv : ∀ σ y, R < ‖y‖ → curlVec (fderiv ℝ (F σ) y) = 0 := by
    intro σ y hy
    have hev : F σ =ᶠ[𝓝 y] fun _ => (0 : Space) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with x hx
      exact hR σ x hx
    rw [hev.fderiv_eq]
    obtain ⟨Λ, hΛ⟩ := exists_curl_clm
    rw [← hΛ]
    simp
  have h := moll_tendsto_of_continuous (continuous_slice_curl hF) ⟨R, hv⟩
  simpa only [curl_moll_eq hF hR] using h

end Internal.CurlGraphMollify

end Breakdown.Coercive
