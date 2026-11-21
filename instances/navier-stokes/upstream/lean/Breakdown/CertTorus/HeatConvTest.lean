import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter
open scoped ContDiff FourierTransform

noncomputable section

namespace Breakdown.FarField

open Freq

namespace Internal.HeatConvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def gaussConv (τ : ℝ) (g : Space → E) (y : Space) : E := ∫ t, heatKernel τ (y - t) • g t

theorem heatConv_eq (τ : ℝ) (f : Space → Space) : heatConv τ f = gaussConv τ f := rfl

theorem continuous_heatKernel (τ : ℝ) : Continuous (heatKernel τ) := by
  unfold heatKernel
  fun_prop

theorem heatKernel_pos {τ : ℝ} (hτ : 0 < τ) (x : Space) : 0 < heatKernel τ x := by
  unfold heatKernel
  have : 0 < 4 * π * τ := by positivity
  exact mul_pos (Real.rpow_pos_of_pos this _) (Real.exp_pos _)

theorem gaussConv_eq_convolution (τ : ℝ) (g : Space → E) :
    gaussConv τ g = convolution (heatKernel τ) g (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext y
  rw [convolution_lsmul_swap]
  rfl

theorem contDiff_gaussConv {τ : ℝ} {g : Space → E} (hc : HasCompactSupport g) {n : ℕ∞}
    (hg : ContDiff ℝ n g) : ContDiff ℝ n (gaussConv τ g) := by
  rw [gaussConv_eq_convolution]
  exact hc.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (continuous_heatKernel τ).locallyIntegrable hg

theorem hasFDerivAt_gaussConv {τ : ℝ} {g : Space → E} (hc : HasCompactSupport g)
    (hg : ContDiff ℝ 1 g) (x : Space) :
    HasFDerivAt (gaussConv τ g) (gaussConv τ (fderiv ℝ g) x) x := by
  have h := hc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (continuous_heatKernel τ).locallyIntegrable hg x
  have e : convolution (heatKernel τ) (fderiv ℝ g)
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompR Space) volume x = gaussConv τ (fderiv ℝ g) x := by
    rw [convolution_eq_swap]
    rfl
  rw [e, ← gaussConv_eq_convolution] at h
  exact h

theorem integrable_smul {τ : ℝ} {g : Space → E} (hg : Continuous g) (hc : HasCompactSupport g)
    (y : Space) : Integrable (fun t => heatKernel τ (y - t) • g t) := by
  refine Continuous.integrable_of_hasCompactSupport
    (((continuous_heatKernel τ).comp (continuous_const.sub continuous_id)).smul hg) ?_
  exact HasCompactSupport.smul_left (f := fun t => heatKernel τ (y - t)) hc

theorem gaussConv_bound (hB : HeatKernelBounds) {τ : ℝ} (hτ : 0 < τ) {g : Space → E}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    ∃ K, 0 ≤ K ∧ ∀ y, ‖gaussConv τ g y‖ ≤ K / (1 + ‖y‖) ^ 2 := by
  obtain ⟨C, hC⟩ := hB
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set s := Real.sqrt τ with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hτ
  have hC0 : 0 ≤ C := by
    have h0 := (hC τ hτ 0).1
    have hp := heatKernel_pos hτ (0 : Space)
    have : 0 < C / (‖(0 : Space)‖ + s) ^ 3 := lt_of_lt_of_le hp h0
    rw [norm_zero, zero_add] at this
    exact (div_pos_iff_of_pos_right (by positivity)).1 this |>.le
  set B := 1 + (1 + |R|) / s with hB_def
  have hB0 : 0 < B := by positivity
  set A := C * B ^ 2 / s with hA_def
  have hA0 : 0 ≤ A := by positivity
  have hgi : Integrable (fun t => ‖g t‖) := (hg.integrable_of_hasCompactSupport hc).norm
  refine ⟨A * ∫ t, ‖g t‖, mul_nonneg hA0 (integral_nonneg fun t => norm_nonneg _), fun y => ?_⟩
  have hpt : ∀ t, ‖heatKernel τ (y - t) • g t‖ ≤ A / (1 + ‖y‖) ^ 2 * ‖g t‖ := by
    intro t
    by_cases ht : g t = 0
    · rw [ht, smul_zero, norm_zero, mul_zero]
    have htR : ‖t‖ ≤ R := by
      have := hR (subset_tsupport g ht)
      simpa using this
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (heatKernel_pos hτ _)]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    set u := ‖y - t‖ + s with hu_def
    have hu : s ≤ u := by simp [hu_def, norm_nonneg]
    have hu0 : 0 < u := lt_of_lt_of_le hs hu
    have hy : ‖y‖ ≤ ‖y - t‖ + R := by
      have := norm_le_norm_sub_add y t
      linarith
    have hyB : 1 + ‖y‖ ≤ B * u := by
      have h1 : (1 + |R|) / s * s ≤ (1 + |R|) / s * u :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      have h2 : (1 + |R|) / s * s = 1 + |R| := by field_simp
      have h3 : R ≤ |R| := le_abs_self R
      have h4 : ‖y - t‖ ≤ u := by simp [hu_def, hs.le]
      rw [hB_def]
      nlinarith
    have h1 := (hC τ hτ (y - t)).1
    calc heatKernel τ (y - t) ≤ C / u ^ 3 := h1
      _ ≤ C / (s * u ^ 2) := by
          apply div_le_div_of_nonneg_left hC0 (by positivity)
          have : s * u ^ 2 ≤ u * u ^ 2 := mul_le_mul_of_nonneg_right hu (by positivity)
          nlinarith
      _ = A / (B * u) ^ 2 := by
          rw [hA_def]
          field_simp
      _ ≤ A / (1 + ‖y‖) ^ 2 := by
          apply div_le_div_of_nonneg_left hA0 (by positivity)
          exact pow_le_pow_left₀ (by positivity) hyB 2
  calc ‖gaussConv τ g y‖ ≤ ∫ t, A / (1 + ‖y‖) ^ 2 * ‖g t‖ :=
        norm_integral_le_of_norm_le (hgi.const_mul _) (Eventually.of_forall hpt)
    _ = A * (∫ t, ‖g t‖) / (1 + ‖y‖) ^ 2 := by
        rw [integral_const_mul]
        ring

def traceCLM : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ Space (unitVector i))

theorem traceCLM_apply (A : Space →L[ℝ] Space) : traceCLM A = ∑ i : Fin 3, A (unitVector i) i := by
  simp [traceCLM]

theorem fderiv_gaussConv {τ : ℝ} {ψ : Space → Space} (hψ : IsTestField ψ) (x : Space) :
    fderiv ℝ (gaussConv τ ψ) x = gaussConv τ (fderiv ℝ ψ) x :=
  (hasFDerivAt_gaussConv hψ.2.1 (hψ.1.of_le (by simp)) x).fderiv

theorem isDecayField_heatConv (hB : HeatKernelBounds) {ψ : Space → Space} (hψ : IsTestField ψ)
    {τ : ℝ} (hτ : 0 < τ) : IsDecayField (heatConv τ ψ) := by
  rw [heatConv_eq]
  have hc1 : Continuous (fderiv ℝ ψ) := hψ.1.continuous_fderiv (by simp)
  have hcs1 : HasCompactSupport (fderiv ℝ ψ) := hψ.2.1.fderiv (𝕜 := ℝ)
  refine ⟨contDiff_gaussConv hψ.2.1 hψ.1, fun y => ?_, ?_⟩
  · have hi := integrable_smul (τ := τ) hc1 hcs1 y
    have e1 : divergenceAt (gaussConv τ ψ) y = traceCLM (fderiv ℝ (gaussConv τ ψ) y) := by
      rw [traceCLM_apply]
      rfl
    rw [e1, fderiv_gaussConv hψ, gaussConv, ← traceCLM.integral_comp_comm hi]
    have e2 : ∀ t, traceCLM (heatKernel τ (y - t) • fderiv ℝ ψ t) = 0 := by
      intro t
      rw [map_smul, traceCLM_apply]
      have := hψ.2.2 t
      unfold divergenceAt at this
      rw [this, smul_zero]
    simp [e2]
  · obtain ⟨K1, hK1, h1⟩ := gaussConv_bound hB hτ (τ := τ) hψ.1.continuous hψ.2.1
    obtain ⟨K2, hK2, h2⟩ := gaussConv_bound hB hτ (τ := τ) hc1 hcs1
    refine ⟨K1 + K2, fun y => ⟨?_, ?_⟩⟩
    · have hy : 1 ≤ 1 + ‖y‖ := by simp
      calc ‖gaussConv τ ψ y‖ ≤ K1 / (1 + ‖y‖) ^ 2 := h1 y
        _ ≤ K1 / (1 + ‖y‖) := by
            apply div_le_div_of_nonneg_left hK1 (by positivity)
            nlinarith
        _ ≤ (K1 + K2) / (1 + ‖y‖) := by
            apply div_le_div_of_nonneg_right (by linarith) (by positivity)
    · rw [fderiv_gaussConv hψ]
      calc ‖gaussConv τ (fderiv ℝ ψ) y‖ ≤ K2 / (1 + ‖y‖) ^ 2 := h2 y
        _ ≤ (K1 + K2) / (1 + ‖y‖) ^ 2 := by
            apply div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem continuous_partialField {ψ : Space → Space} (hψ : IsTestField ψ) (k : Fin 3) :
    Continuous (partialField ψ k) :=
  (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem hasCompactSupport_partialField {ψ : Space → Space} (hψ : IsTestField ψ) (k : Fin 3) :
    HasCompactSupport (partialField ψ k) := by
  have h := (hψ.2.1.fderiv (𝕜 := ℝ)).comp_left
    (g := fun A : Space →L[ℝ] Space => A (unitVector k)) rfl
  exact h

theorem partialField_heatConv {τ : ℝ} {ψ : Space → Space} (hψ : IsTestField ψ) (k : Fin 3) :
    partialField (heatConv τ ψ) k = heatConv τ (partialField ψ k) := by
  funext x
  have hi := integrable_smul (τ := τ) (hψ.1.continuous_fderiv (by simp)) (hψ.2.1.fderiv (𝕜 := ℝ)) x
  unfold partialField
  rw [heatConv_eq, fderiv_gaussConv hψ, gaussConv, ContinuousLinearMap.integral_apply hi]
  rfl

def heatKernelC (τ : ℝ) (x : Space) : ℂ := ((heatKernel τ x : ℝ) : ℂ)

theorem heatKernelC_eq {τ : ℝ} (x : Space) :
    heatKernelC τ x = (((4 * π * τ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-((1 / (4 * τ) : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  unfold heatKernelC heatKernel
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

theorem re_pos {τ : ℝ} (hτ : 0 < τ) : 0 < (((1 / (4 * τ) : ℝ) : ℂ)).re := by
  rw [Complex.ofReal_re]
  positivity

theorem integrable_heatKernelC {τ : ℝ} (hτ : 0 < τ) : Integrable (heatKernelC τ) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (re_pos hτ) 0 (0 : Space)).const_mul
    (((4 * π * τ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [heatKernelC_eq, zero_mul, add_zero]

theorem integrable_heatKernel {τ : ℝ} (hτ : 0 < τ) : Integrable (heatKernel τ) := by
  refine (integrable_heatKernelC hτ).norm.congr (Eventually.of_forall fun x => ?_)
  simp only [heatKernelC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (heatKernel_pos hτ x)]

theorem fourier_heatKernelC {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    𝓕 (heatKernelC τ) ξ = ((heatFactor τ ξ : ℝ) : ℂ) := by
  have hG := fourier_gaussian_innerProductSpace (re_pos hτ) ξ
  have e : heatKernelC τ = fun x => (((4 * π * τ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-((1 / (4 * τ) : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2) := funext heatKernelC_eq
  rw [e, Real.fourier_eq']
  rw [Real.fourier_eq'] at hG
  simp_rw [smul_eq_mul] at hG ⊢
  simp_rw [mul_left_comm _ (((4 * π * τ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)]
  rw [integral_const_mul, hG, finrank_euclideanSpace_fin]
  have e1 : (π : ℂ) / ((1 / (4 * τ) : ℝ) : ℂ) = ((4 * π * τ : ℝ) : ℂ) := by
    push_cast
    field_simp
  have e2 : ((3 : ℕ) : ℂ) / 2 = ((3 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hp : (0 : ℝ) < 4 * π * τ := by positivity
  rw [e1, e2, ← Complex.ofReal_cpow hp.le, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add hp, heatFactor, max_eq_left hτ.le, Complex.ofReal_exp]
  norm_num
  congr 1
  field_simp

theorem complexify_gaussConv {τ : ℝ} {g : Space → Space} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    (fun y => complexifyVec (gaussConv τ g y)) =
      convolution (heatKernelC τ) (fun y => complexifyVec (g y)) (ContinuousLinearMap.lsmul ℂ ℂ)
        volume := by
  funext y
  rw [convolution_lsmul_swap, gaussConv, ← complexifyVec.integral_comp_comm (integrable_smul hg hc y)]
  congr 1
  funext t
  ext i
  simp [complexifyVec, heatKernelC]

theorem fourier_gaussConv {τ : ℝ} (hτ : 0 < τ) {g : Space → Space} (hg : Continuous g)
    (hc : HasCompactSupport g) (ξ : Space) :
    𝓕 (fun y => complexifyVec (gaussConv τ g y)) ξ =
      heatFactor τ ξ • 𝓕 (fun y => complexifyVec (g y)) ξ := by
  have hgi : Integrable (fun y => complexifyVec (g y)) :=
    (complexifyVec.continuous.comp hg).integrable_of_hasCompactSupport (hc.comp_left (map_zero _))
  rw [complexify_gaussConv hg hc, Real.fourier_smul_convolution_eq (integrable_heatKernelC hτ) hgi,
    fourier_heatKernelC hτ]
  exact (Complex.coe_smul _ _).symm

theorem complexify_toLp {f : Space → Space} (hf : MemLp f 2 volume) :
    complexify (toLpOrZero 2 f) = toLpOrZero 2 (fun y => complexifyVec (f y)) := by
  have hm : MemLp (fun y => complexifyVec (f y)) 2 volume := complexifyVec.comp_memLp' hf
  have e : toLpOrZero 2 (fun y => complexifyVec (f y)) = hm.toLp _ := by
    unfold toLpOrZero
    rw [dif_pos hm]
  rw [e]
  apply Lp.ext
  filter_upwards [Breakdown.Freq.Internal.EmbedRot.ae_complexify f hf, hm.coeFn_toLp] with y e1 e2
  rw [e1, e2]

theorem fourierR_heatConv (hB : HeatKernelBounds) {τ : ℝ} (hτ : 0 < τ) {g : Space → Space}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    freqTrR (complexify (toLpOrZero 2 (heatConv τ g))) =
      heatL2 τ (freqTrR (complexify (toLpOrZero 2 g))) := by
  have hcont : Continuous (heatConv τ g) :=
    (contDiff_gaussConv (n := 0) hc (contDiff_zero.2 hg)).continuous
  have g1 : Integrable g := hg.integrable_of_hasCompactSupport hc
  have g2 : MemLp g 2 volume := hg.memLp_of_hasCompactSupport hc
  have h1 : Integrable (heatConv τ g) := by
    rw [heatConv_eq, gaussConv_eq_convolution]
    exact (integrable_heatKernel hτ).integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) g1
  obtain ⟨K, hK, hKb⟩ := gaussConv_bound hB hτ hg hc
  have hbd : ∀ y, ‖heatConv τ g y‖ ≤ K := fun y =>
    (hKb y).trans (div_le_self hK (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))))
  have h2 : MemLp (heatConv τ g) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
    refine (h1.norm.const_mul K).mono' (hcont.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_right (hbd y) (norm_nonneg _)
  have hG1 : MemLp (fun y => complexifyVec (heatConv τ g y)) 1 volume :=
    complexifyVec.comp_memLp' (memLp_one_iff_integrable.2 h1)
  have hG2 : MemLp (fun y => complexifyVec (heatConv τ g y)) 2 volume := complexifyVec.comp_memLp' h2
  have hg1 : MemLp (fun y => complexifyVec (g y)) 1 volume :=
    complexifyVec.comp_memLp' (memLp_one_iff_integrable.2 g1)
  have hg2 : MemLp (fun y => complexifyVec (g y)) 2 volume := complexifyVec.comp_memLp' g2
  rw [complexify_toLp h2, complexify_toLp g2]
  apply Lp.ext
  filter_upwards [freqTrL1L2.1 _ hG1 hG2,
    Breakdown.Freq.Internal.Heat.heat_ae fieldOpRealized_holds τ
      (freqTrR (toLpOrZero 2 (fun y => complexifyVec (g y)))),
    freqTrL1L2.1 _ hg1 hg2] with ξ e1 e2 e3
  change (freqTrL2 (toLpOrZero 2 (fun y => complexifyVec (heatConv τ g y))) : Space → CSpace) ξ = _
  rw [e1, e2]
  change _ = heatFactor τ ξ • (freqTrL2 (toLpOrZero 2 (fun y => complexifyVec (g y))) :
    Space → CSpace) ξ
  rw [e3, heatConv_eq, fourier_gaussConv hτ hg hc]

theorem ofGrad_heatConv (hB : HeatKernelBounds) {τ : ℝ} (hτ : 0 < τ) {ψ : Space → Space}
    (hψ : IsTestField ψ) : ofGrad (heatConv τ ψ) = heatL2 τ (ofGrad ψ) := by
  unfold ofGrad
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [partialField_heatConv hψ k, fourierR_heatConv hB hτ (continuous_partialField hψ k)
    (hasCompactSupport_partialField hψ k)]
  exact Breakdown.Freq.Internal.Heat.heat_comm fieldOpRealized_holds τ id _
    (Measure.QuasiMeasurePreserving.id volume) (fun _ => rfl) _

end Internal.HeatConvolution

open Internal.HeatConvolution in
theorem heatConvTest_of_heat : HeatKernelBounds → HeatKernelPartials → HeatConvTest := by
  intro hB _ ψ hψ τ hτ
  have hd := isDecayField_heatConv hB hψ hτ
  refine ⟨hd, ?_⟩
  have m1 : ofGrad ψ ∈ Sig :=
    embedMem_holds ψ (Breakdown.Freq.Internal.VelocityRotate.decay_of_test hψ)
  have m2 : ofGrad (heatConv τ ψ) ∈ Sig := embedMem_holds _ hd
  have e1 : ((embedX ψ : X) : L2C) = ofGrad ψ := by
    unfold embedX
    rw [dif_pos m1]
  have e2 : ((embedX (heatConv τ ψ) : X) : L2C) = ofGrad (heatConv τ ψ) := by
    unfold embedX
    rw [dif_pos m2]
  apply Subtype.ext
  rw [Breakdown.Freq.Internal.Heat.heatX_coe fieldOpRealized_holds, e1, e2, ofGrad_heatConv hB hτ hψ]

end Breakdown.FarField
