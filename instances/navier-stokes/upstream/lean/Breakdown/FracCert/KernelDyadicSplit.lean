import Breakdown.FracCert.StKernel

open scoped ContDiff FourierTransform
open MeasureTheory Real

noncomputable section

namespace Breakdown.FracCert

private lemma cut_support {θ : Space → ℝ} (hθ : IsRingCutoff θ) {c : ℝ} (hc : 0 < c) (ξ : Space)
    (h : θ (c • ξ) ≠ 0) : 1 / 2 < c * ‖ξ‖ ∧ c * ‖ξ‖ < 2 := by
  have := hθ.2.2.1 _ h
  rwa [norm_smul, Real.norm_of_nonneg hc.le] at this

private lemma cut_zero {θ : Space → ℝ} (hθ : IsRingCutoff θ) : θ 0 = 0 := by
  by_contra h
  have := (hθ.2.2.1 _ h).1
  simp at this
  linarith

private lemma cut_smooth {σ : Space → ℂ} {d : ℝ} {θ : Space → ℝ} (hσ : IsHomogeneousSymbol σ d)
    (hθ : IsRingCutoff θ) {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ∞ (fun ξ => ((θ (c • ξ) : ℝ) : ℂ) * σ ξ) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst hξ
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    have hb : Metric.ball (0 : Space) (1 / (2 * c)) ∈ nhds (0 : Space) :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [hb] with y hy
    have hθy : θ (c • y) = 0 := by
      by_contra h
      have h1 := (cut_support hθ hc y h).1
      rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ (by positivity)] at hy
      nlinarith
    simp [hθy]
  · have h1 : ContDiffAt ℝ ∞ (fun y : Space => ((θ (c • y) : ℝ) : ℂ)) ξ :=
      (Complex.ofRealCLM.contDiff.comp (hθ.1.comp (contDiff_const_smul c))).contDiffAt
    have h2 : ContDiffAt ℝ ∞ σ ξ := hσ.1.contDiffAt (isOpen_ne.mem_nhds hξ)
    exact h1.mul h2

private lemma cut_compact {σ : Space → ℂ} {θ : Space → ℝ} (hθ : IsRingCutoff θ) {c : ℝ}
    (hc : 0 < c) : HasCompactSupport (fun ξ => ((θ (c • ξ) : ℝ) : ℂ) * σ ξ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 / c))
  intro ξ hξ
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hξ
  have : θ (c • ξ) = 0 := by
    by_contra h
    have h2 := (cut_support hθ hc ξ h).2
    rw [div_lt_iff₀ hc] at hξ
    nlinarith
  simp [this]

private lemma conv_eq {m : Space → ℂ} (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    {f F : Space → ℂ} (hF : IsTransformOf F f) (x : Space) :
    kernelConv (FourierTransform.fourierInv m) f x =
      FourierTransform.fourierInv (fun ξ => m ξ * F ξ) x := by
  have hs : ContDiff ℝ ∞ (fun ξ : Space => Complex.exp (((2 * π * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) * m ξ) := by
    refine ContDiff.mul ?_ hm
    have h1 : ContDiff ℝ ∞ (fun ξ : Space => inner ℝ ξ x) := contDiff_id.inner ℝ contDiff_const
    have h2 : ContDiff ℝ ∞ (fun ξ : Space => ((2 * π * inner ℝ ξ x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.mul h1)
    exact Complex.contDiff_exp.comp (h2.mul contDiff_const)
  have hc : HasCompactSupport (fun ξ : Space => Complex.exp (((2 * π * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) * m ξ) :=
    hmc.mul_left
  have key := hF.2 (hc.toSchwartzMap hs)
  have hco : ∀ ξ, (hc.toSchwartzMap hs) ξ = Complex.exp (((2 * π * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) * m ξ := fun _ => rfl
  have hφ : ∀ y, FourierTransform.fourier (⇑(hc.toSchwartzMap hs)) y =
      FourierTransform.fourierInv m (x - y) := by
    intro y
    rw [Real.fourier_eq, Real.fourierInv_eq]
    congr 1
    funext ξ
    rw [hco ξ]
    simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
    rw [← mul_assoc, ← Complex.exp_add, inner_sub_right]
    congr 2
    push_cast
    ring
  simp_rw [hφ] at key
  unfold kernelConv
  have hsub := integral_sub_left_eq_self
    (fun z => FourierTransform.fourierInv m z * f (x - z)) volume x
  simp only [sub_sub_cancel] at hsub
  rw [← hsub]
  rw [Real.fourierInv_eq]
  calc (∫ y, FourierTransform.fourierInv m (x - y) * f y)
      = ∫ y, f y * FourierTransform.fourierInv m (x - y) := by
        congr 1; funext y; ring
    _ = _ := key
    _ = _ := by
        congr 1; funext ξ
        rw [hco ξ]
        simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
        ring

private def scaledCut (θ : Space → ℝ) (l : ℤ) (ξ : Space) : ℝ := θ (((2 : ℝ) ^ (-(l : ℝ))) • ξ)

private lemma kernel_eq {σ : Space → ℂ} {d : ℝ} {θ : Space → ℝ} (hσ : IsHomogeneousSymbol σ d)
    (hθ : IsRingCutoff θ) (l : ℤ) :
    dyadicKernel σ θ d l =
      FourierTransform.fourierInv (fun ξ => ((θ (((2 : ℝ) ^ (-(l : ℝ))) • ξ) : ℝ) : ℂ) * σ ξ) := by
  funext z
  unfold dyadicKernel
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  set c : ℝ := (2 : ℝ) ^ (l : ℝ) with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hneg : (2 : ℝ) ^ (-(l : ℝ)) = c⁻¹ := Real.rpow_neg (by norm_num) _
  rw [hneg]
  have hcomp := Measure.integral_comp_smul volume
    (fun v : Space => 𝐞 (inner ℝ v (c • z)) • (((θ v : ℝ) : ℂ) * σ v)) c⁻¹
  have hpt : ∀ ξ : Space, 𝐞 (inner ℝ ξ z) • (((θ (c⁻¹ • ξ) : ℝ) : ℂ) * σ ξ) =
      ((c ^ d : ℝ) : ℂ) * (𝐞 (inner ℝ (c⁻¹ • ξ) (c • z)) •
        (((θ (c⁻¹ • ξ) : ℝ) : ℂ) * σ (c⁻¹ • ξ))) := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [cut_zero hθ]
    rw [hσ.2 c⁻¹ (inv_pos.2 hc) ξ hξ, real_inner_smul_left, real_inner_smul_right,
      ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, Real.inv_rpow hc.le]
    simp only [Circle.smul_def, smul_eq_mul]
    have : (c ^ d : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hc d).ne'
    have h' : ((c ^ d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this
    push_cast
    field_simp
  simp_rw [hpt]
  rw [integral_const_mul, hcomp, finrank_euclideanSpace_fin]
  have habs : |(c⁻¹ ^ 3)⁻¹| = c ^ 3 := by
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
  have hr : (2 : ℝ) ^ ((3 + d) * l) = c ^ d * c ^ 3 := by
    rw [hc_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  rw [habs, hr, Complex.real_smul]
  push_cast
  ring

private lemma moments_mul {G : Space → ℂ} (hG : HasMomentsInL1 G) {h : Space → ℝ}
    (hc : Continuous h) (h0 : ∀ ξ, 0 ≤ h ξ) (h1 : ∀ ξ, h ξ ≤ 1) :
    HasMomentsInL1 (fun ξ => (h ξ : ℂ) * G ξ) := by
  have hm : AEStronglyMeasurable (fun ξ => (h ξ : ℂ) * G ξ) volume :=
    (Complex.continuous_ofReal.comp hc).aestronglyMeasurable.mul hG.1
  refine ⟨hm, fun n => (hG.2 n).mono' ?_ (ae_of_all _ fun ξ => ?_)⟩
  · exact ((continuous_norm.pow n).aestronglyMeasurable).mul hm.norm
  · rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (h0 ξ)]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (h1 ξ)) (by positivity)

private lemma moments_neg {G : Space → ℂ} (hG : HasMomentsInL1 G) (n : ℕ) :
    Integrable (fun v : Space => ‖v‖ ^ n * ‖G (-v)‖) := by
  have := (hG.2 n).comp_neg
  simpa using this

private lemma meas_neg {G : Space → ℂ} (hG : HasMomentsInL1 G) :
    AEStronglyMeasurable (fun v : Space => G (-v)) volume :=
  hG.1.comp_measurePreserving (Measure.measurePreserving_neg volume)

private lemma smooth_inv {G : Space → ℂ} (hG : HasMomentsInL1 G) :
    ContDiff ℝ ∞ (FourierTransform.fourierInv G) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact Real.contDiff_fourier (N := ⊤) (fun n _ => moments_neg hG n)

private lemma iter_inv {G : Space → ℂ} (hG : HasMomentsInL1 G) (n : ℕ) (x : Space) :
    iteratedFDeriv ℝ n (FourierTransform.fourierInv G) x =
      ∫ v, 𝐞 (-inner ℝ v x) •
        VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun y => G (-y)) v n := by
  rw [Real.fourierInv_eq_fourier_comp_neg,
    Real.iteratedFDeriv_fourier (N := ⊤) (fun k _ => moments_neg hG k) (meas_neg hG) le_top,
    Real.fourier_eq]

private lemma psr_smul (h : Space → ℝ) (G : Space → ℂ) (v : Space) (n : ℕ) :
    VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun y => ((h (-y) : ℝ) : ℂ) * G (-y)) v n =
      ((h (-v) : ℝ) : ℂ) •
        VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun y => G (-y)) v n := by
  ext m
  simp only [VectorFourier.fourierPowSMulRight_apply, smul_apply,
    smul_eq_mul, Complex.real_smul]
  ring

theorem dyadicSplit : DyadicSplitStatement := by
  intro σ d β θ hd hβ hβ3 hσ hθ f F hf hF hG
  refine ⟨smooth_inv hG, fun n x => ?_⟩
  have hθc : Continuous θ := hθ.1.continuous
  have hw_c : ∀ l, Continuous (scaledCut θ l) := fun l => hθc.comp (continuous_const_smul _)
  have hw0 : ∀ l ξ, 0 ≤ scaledCut θ l ξ := fun l ξ => (hθ.2.1 _).1
  have hw1 : ∀ l ξ, scaledCut θ l ξ ≤ 1 := fun l ξ => (hθ.2.1 _).2
  have hsum : ∀ v : Space, v ≠ 0 → HasSum (fun l : ℤ => scaledCut θ l (-v)) 1 :=
    fun v hv => hθ.2.2.2 (-v) (neg_ne_zero.2 hv)
  have hpiece : ∀ l, kernelConv (dyadicKernel σ θ d l) f =
      FourierTransform.fourierInv (fun ξ => ((scaledCut θ l ξ : ℝ) : ℂ) * (σ ξ * F ξ)) := by
    intro l
    funext y
    have hc : (0 : ℝ) < (2 : ℝ) ^ (-(l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    rw [kernel_eq hσ hθ l, conv_eq (cut_smooth hσ hθ hc) (cut_compact hθ hc) hF y]
    have hfun : (fun ξ => ((θ (((2 : ℝ) ^ (-(l : ℝ))) • ξ) : ℝ) : ℂ) * σ ξ * F ξ) =
        fun ξ => ((scaledCut θ l ξ : ℝ) : ℂ) * (σ ξ * F ξ) := by
      funext ξ
      simp only [scaledCut]
      ring
    rw [hfun]
  have hGl : ∀ l, HasMomentsInL1 (fun ξ => ((scaledCut θ l ξ : ℝ) : ℂ) * (σ ξ * F ξ)) :=
    fun l => moments_mul hG (hw_c l) (hw0 l) (hw1 l)
  have h0ae : ∀ᵐ v ∂(volume : Measure Space), v ≠ 0 := by
    rw [ae_iff]
    simp
  set X : Space → _ := fun v =>
    VectorFourier.fourierPowSMulRight (innerSL ℝ) (fun y => σ (-y) * F (-y)) v n with hX
  have hXm : AEStronglyMeasurable X volume := (meas_neg hG).fourierPowSMulRight (innerSL ℝ) n
  have hXi : Integrable X :=
    VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ) (moments_neg hG n) (meas_neg hG)
  set Y : Space → _ := fun v =>
    Complex.exp (((2 * π * -inner ℝ v x : ℝ) : ℂ) * Complex.I) • X v with hY
  have hEc : Continuous (fun v : Space => Complex.exp (((2 * π * -inner ℝ v x : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hYm : AEStronglyMeasurable Y volume := hEc.aestronglyMeasurable.smul hXm
  have hYn : ∀ v, ‖Y v‖ = ‖X v‖ := by
    intro v
    simp only [hY, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have key : HasSum (fun l : ℤ => ∫ v, ((scaledCut θ l (-v) : ℝ) : ℂ) • Y v) (∫ v, Y v) := by
    refine hasSum_integral_of_dominated_convergence (fun l v => scaledCut θ l (-v) * ‖Y v‖)
      (fun l => ?_) (fun l => ae_of_all _ fun v => ?_) ?_ ?_ ?_
    · exact ((Complex.continuous_ofReal.comp ((hw_c l).comp continuous_neg)).aestronglyMeasurable).smul hYm
    · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hw0 _ _)]
    · filter_upwards [h0ae] with v hv
      exact ((hsum v hv).mul_right ‖Y v‖).summable
    · refine hXi.norm.congr ?_
      filter_upwards [h0ae] with v hv
      rw [tsum_mul_right, (hsum v hv).tsum_eq, one_mul, hYn]
    · filter_upwards [h0ae] with v hv
      have := (Complex.hasSum_ofReal.2 (hsum v hv)).smul_const (Y v)
      simpa using this
  convert key using 1
  · funext l
    rw [hpiece l, iter_inv (hGl l) n x]
    congr 1
    funext v
    have := psr_smul (scaledCut θ l) (fun ξ => σ ξ * F ξ) v n
    rw [this]
    simp only [hY, hX, Circle.smul_def, Real.fourierChar_apply]
    exact smul_comm _ _ _
  · rw [iter_inv hG n x]
    congr 1

end Breakdown.FracCert
