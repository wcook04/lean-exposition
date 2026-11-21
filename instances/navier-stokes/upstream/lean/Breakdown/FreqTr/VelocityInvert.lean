import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.VelocityInvert

open SchwartzMap FourierTransform

def cplxField (f : Space → Space) : Space → CSpace := fun x => complexifyVec (f x)

theorem cplxField_contDiff {f : Space → Space} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cplxField f) :=
  complexifyVec.contDiff.comp hf

theorem cplxField_hasCompactSupport {f : Space → Space} (hf : HasCompactSupport f) :
    HasCompactSupport (cplxField f) :=
  hf.comp_left (map_zero complexifyVec)

def cplxRapid {f : Space → Space} (h1 : ContDiff ℝ ∞ f) (h2 : HasCompactSupport f) :
    𝓢(Space, CSpace) :=
  (cplxField_hasCompactSupport h2).toSchwartzMap (cplxField_contDiff h1)

def thetaFun {θ : Space → Space} (h1 : ContDiff ℝ ∞ θ) (h2 : HasCompactSupport θ) :
    Space → CSpace :=
  fun ξ => (2 * π * ‖ξ‖)⁻¹ • (𝓕 (cplxRapid h1 h2)) ξ

theorem rapid_norm_bounded (f : 𝓢(Space, CSpace)) : ∃ C, 0 ≤ C ∧ ∀ ξ, ‖f ξ‖ ≤ C := by
  obtain ⟨C, hC⟩ := f.decay 0 0
  refine ⟨max C 0, le_max_right _ _, fun ξ => ?_⟩
  have := hC.2 ξ
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at this
  exact (this.trans (le_max_left _ _))

theorem memLp_thetaFun {θ : Space → Space} (h1 : ContDiff ℝ ∞ θ) (h2 : HasCompactSupport θ) :
    MemLp (thetaFun h1 h2) 2 volume := by
  set f := 𝓕 (cplxRapid h1 h2) with hf
  have hmeas : AEStronglyMeasurable (thetaFun h1 h2) volume := by
    unfold thetaFun
    exact (((continuous_const.mul continuous_norm).measurable.inv).aestronglyMeasurable).smul
      f.continuous.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  obtain ⟨C, hC0, hC⟩ := rapid_norm_bounded f
  have hnorm : ∀ ξ, ‖thetaFun h1 h2 ξ‖ = (2 * π * ‖ξ‖)⁻¹ * ‖f ξ‖ := by
    intro ξ
    simp only [thetaFun, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
  have hball : IntegrableOn (fun ξ => ‖thetaFun h1 h2 ξ‖ ^ 2) (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := (C / (2 * π)) ^ 2) (α := 2)
      (by simp) (by simp; norm_num) ?_
      (hmeas.norm.pow 2)
    refine Filter.Eventually.of_forall (fun ξ => ?_)
    rw [norm_pow, norm_norm, hnorm]
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp only [norm_zero, mul_zero, inv_zero, zero_mul]
      rw [Real.zero_rpow (by norm_num)]
      simp
    · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
      rw [Real.rpow_neg (norm_nonneg _)]
      have e : ((2 * π * ‖ξ‖)⁻¹ * ‖f ξ‖) ^ 2 = (‖f ξ‖ / (2 * π)) ^ 2 * (‖ξ‖ ^ (2 : ℝ))⁻¹ := by
        rw [Real.rpow_two]
        field_simp
      rw [e]
      gcongr
      exact hC ξ
  have hL2 : Integrable (fun ξ => ‖f ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).1 (f.memLp 2 volume)
  have hcompl : IntegrableOn (fun ξ => ‖thetaFun h1 h2 ξ‖ ^ 2) (Metric.ball 0 1)ᶜ volume := by
    refine Integrable.mono' ((hL2.const_mul ((2 * π)⁻¹ ^ 2)).integrableOn) (hmeas.norm.pow 2).restrict ?_
    refine (ae_restrict_iff' measurableSet_ball.compl).2 (Filter.Eventually.of_forall (fun ξ hξ => ?_))
    have h1ξ : 1 ≤ ‖ξ‖ := by simpa using hξ
    rw [norm_pow, norm_norm, hnorm, mul_pow]
    have hinv : (2 * π * ‖ξ‖)⁻¹ ≤ (2 * π)⁻¹ :=
      inv_anti₀ (by positivity) (le_mul_of_one_le_right (by positivity) h1ξ)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hinv 2) (by positivity)
  have := hball.union hcompl
  rwa [Set.union_compl_self, integrableOn_univ] at this

theorem l2Iso_inner_map (u v : L2C) : inner ℝ (freqTrL2 u) (freqTrL2 v) = inner ℝ u v := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

theorem l2Iso_realVec_inner (z : CSpace) (t : Space) :
    inner ℝ z (complexifyVec t) = inner ℝ (realVec z) t := by
  simp [realVec, complexifyVec, PiLp.inner_apply, Complex.inner, Complex.mul_re]

theorem l2Iso_toPhys_ae (b : L2C) :
    (toPhys b : Space → Space) =ᵐ[volume] fun x => realVec ((freqTrL2.symm b : L2C) x) := by
  exact ContinuousLinearMap.coeFn_compLpL realVec (freqTrInvR b)

theorem inner_freqTr_cplx (b : L2C) {θ : Space → Space} (h1 : ContDiff ℝ ∞ θ)
    (h2 : HasCompactSupport θ) :
    inner ℝ b ((𝓕 (cplxRapid h1 h2)).toLp 2) =
      ∫ x, inner ℝ ((toPhys b : Space → Space) x) (θ x) := by
  rw [← SchwartzMap.toLp_fourier_eq]
  have hb : b = freqTrL2 (freqTrL2.symm b) := (freqTrL2.apply_symm_apply b).symm
  conv_lhs => rw [hb]
  change inner ℝ _ (freqTrL2 ((cplxRapid h1 h2).toLp 2 volume)) = _
  rw [l2Iso_inner_map, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cplxRapid h1 h2).coeFn_toLp 2, l2Iso_toPhys_ae b] with x hx hy
  rw [hx, hy]
  exact l2Iso_realVec_inner _ _

theorem toPhys_freqTr_cplx {φ : Space → Space} (h1 : ContDiff ℝ ∞ φ) (h2 : HasCompactSupport φ) :
    (toPhys (freqTrL2 ((cplxRapid h1 h2).toLp 2)) : Space → Space) =ᵐ[volume] φ := by
  filter_upwards [l2Iso_toPhys_ae (freqTrL2 ((cplxRapid h1 h2).toLp 2)),
    (cplxRapid h1 h2).coeFn_toLp 2] with x hx hy
  rw [hx, LinearIsometryEquiv.symm_apply_apply, hy]
  ext i
  simp [cplxRapid, cplxField, realVec, complexifyVec]

theorem inner_thetaFun (a b : L2C)
    (hab : ∀ᵐ ξ ∂volume, (a : Space → CSpace) ξ = (2 * π * ‖ξ‖) • (b : Space → CSpace) ξ)
    {θ : Space → Space} (h1 : ContDiff ℝ ∞ θ) (h2 : HasCompactSupport θ) :
    inner ℝ a ((memLp_thetaFun h1 h2).toLp _) = inner ℝ b ((𝓕 (cplxRapid h1 h2)).toLp 2) := by
  rw [L2.inner_def, L2.inner_def]
  have hne : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
    exact measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := (volume : Measure Space)) 0)
  apply integral_congr_ae
  filter_upwards [hab, hne, (memLp_thetaFun h1 h2).coeFn_toLp,
    (𝓕 (cplxRapid h1 h2)).coeFn_toLp 2 volume] with ξ h1' h2' h3' h4'
  rw [h1', h3', h4']
  simp only [thetaFun]
  have hpos : (2 * π * ‖ξ‖) ≠ 0 := by
    have := norm_pos_iff.2 h2'
    positivity
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hpos, one_mul]

theorem ofgrad_decay {φ : Space → Space} (hφ : IsTestField φ) : IsDecayField φ := by
  refine ⟨hφ.1, hφ.2.2, ?_⟩
  have c1 : Continuous ((fun y : Space => 1 + ‖y‖) • φ) :=
    (continuous_const.add continuous_norm).smul hφ.1.continuous
  have s1 : HasCompactSupport ((fun y : Space => 1 + ‖y‖) • φ) := hφ.2.1.smul_left
  have c2 : Continuous ((fun y : Space => (1 + ‖y‖) ^ 2) • fderiv ℝ φ) :=
    ((continuous_const.add continuous_norm).pow 2).smul (hφ.1.continuous_fderiv (by simp))
  have s2 : HasCompactSupport ((fun y : Space => (1 + ‖y‖) ^ 2) • fderiv ℝ φ) :=
    (hφ.2.1.fderiv (𝕜 := ℝ)).smul_left
  obtain ⟨C1, hC1⟩ := c1.bounded_above_of_compact_support s1
  obtain ⟨C2, hC2⟩ := c2.bounded_above_of_compact_support s2
  refine ⟨max C1 C2, fun y => ⟨?_, ?_⟩⟩
  · have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
    rw [le_div_iff₀ hp]
    have := hC1 y
    rw [Pi.smul_apply', norm_smul, Real.norm_of_nonneg hp.le] at this
    nlinarith [le_max_left C1 C2, norm_nonneg (φ y)]
  · have hp : (0 : ℝ) < (1 + ‖y‖) ^ 2 := by positivity
    rw [le_div_iff₀ hp]
    have := hC2 y
    rw [Pi.smul_apply', norm_smul, Real.norm_of_nonneg hp.le] at this
    nlinarith [le_max_right C1 C2, norm_nonneg (fderiv ℝ φ y)]

theorem ofgrad_embed_eq (h4 : EmbedMem) {φ : Space → Space} (hφ : IsTestField φ) :
    ((embedX φ : X) : L2C) = ofGrad φ := by
  unfold embedX
  rw [dif_pos (h4 φ (ofgrad_decay hφ))]

theorem ofgrad_partial_eq {φ : Space → Space} (hφ : IsTestField φ) (k : Fin 3) :
    partialField φ k = ⇑(LineDeriv.lineDerivOp (unitVector k) (hφ.2.1.toSchwartzMap hφ.1)) := by
  funext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

theorem ofgrad_cplx_deriv {φ : Space → Space} (hφ : IsTestField φ) (k : Fin 3) :
    complexify (toLpOrZero 2 (partialField φ k)) =
      (LineDeriv.lineDerivOp (unitVector k) (cplxRapid hφ.1 hφ.2.1)).toLp 2 := by
  have hm : MemLp (partialField φ k) 2 volume := by
    rw [ofgrad_partial_eq hφ k]
    exact (LineDeriv.lineDerivOp (unitVector k) (hφ.2.1.toSchwartzMap hφ.1)).memLp 2 volume
  apply Lp.ext
  have e1 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec
    (toLpOrZero 2 (partialField φ k))
  have e2 : (toLpOrZero 2 (partialField φ k) : Space → Space) =ᵐ[volume] partialField φ k := by
    unfold toLpOrZero
    rw [dif_pos hm]
    exact hm.coeFn_toLp
  have e3 := SchwartzMap.coeFn_toLp
    (LineDeriv.lineDerivOp (unitVector k) (cplxRapid hφ.1 hφ.2.1)) 2 volume
  filter_upwards [e1, e2, e3] with x h1 h2 h3
  change (ContinuousLinearMap.compLpL 2 volume complexifyVec _ : Space → CSpace) x = _
  rw [h1, h2, h3, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hd : HasFDerivAt (fun y => complexifyVec (φ y)) (complexifyVec.comp (fderiv ℝ φ x)) x :=
    complexifyVec.hasFDerivAt.comp x ((hφ.1.differentiable (by simp)) x).hasFDerivAt
  change complexifyVec (fderiv ℝ φ x (unitVector k)) = fderiv ℝ (fun y => complexifyVec (φ y)) x (unitVector k)
  rw [hd.fderiv]
  rfl

theorem ofgrad_freqTr_toLp (f : 𝓢(Space, CSpace)) : freqTrL2 (f.toLp 2) = (𝓕 f).toLp 2 :=
  SchwartzMap.toLp_fourier_eq f

theorem ofgrad_cmul_apply (c : ℂ) (v : CSpace) : cmul c v = c • v := rfl

theorem ofgrad_term (ξ : Space) (ψ : CSpace) (k : Fin 3) :
    cmul (gradSymbol k ξ) ((2 * π * Complex.I) • (inner ℝ ξ (unitVector k) • ψ)) =
      (2 * π * (ξ k) ^ 2 / ‖ξ‖ : ℝ) • ψ := by
  rw [ofgrad_cmul_apply]
  have hi : inner ℝ ξ (unitVector k) = ξ k := by
    simp [unitVector, EuclideanSpace.inner_single_right]
  rw [hi, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
  congr 1
  unfold gradSymbol
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem ofgrad_sum (ξ : Space) :
    2 * π * (ξ 0) ^ 2 / ‖ξ‖ + 2 * π * (ξ 1) ^ 2 / ‖ξ‖ + 2 * π * (ξ 2) ^ 2 / ‖ξ‖ = 2 * π * ‖ξ‖ := by
  have h := EuclideanSpace.real_norm_sq_eq ξ
  rw [Fin.sum_univ_three] at h
  rcases eq_or_ne ‖ξ‖ 0 with h0 | h0
  · simp [h0]
  · field_simp
    nlinarith [h]

theorem ofgrad_symbol_bound (k : Fin 3) (ξ : Space) : ‖cmul (gradSymbol k ξ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [ofgrad_cmul_apply, norm_smul, one_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  unfold gradSymbol
  rw [norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg ξ)]
  rcases eq_or_ne ‖ξ‖ 0 with h0 | h0
  · simp [h0]
  · rw [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
    exact PiLp.norm_apply_le ξ k

theorem ofgrad_cmul_eq :
    cmul = fun c : ℂ => c • (ContinuousLinearMap.id ℂ CSpace).restrictScalars ℝ := by
  funext c
  ext v : 1
  rfl

theorem ofgrad_symbol_meas (k : Fin 3) :
    AEStronglyMeasurable (fun ξ : Space => cmul (gradSymbol k ξ)) volume := by
  have hc : Continuous cmul := by
    rw [ofgrad_cmul_eq]
    exact continuous_id.smul continuous_const
  have hg : Measurable (gradSymbol k) := by
    unfold gradSymbol
    fun_prop
  exact hc.comp_aestronglyMeasurable hg.aestronglyMeasurable

theorem ofgrad_fieldOp_ae (h6 : FieldOpRealized) (k : Fin 3) (f : L2C) :
    (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) f : Space → CSpace) =ᵐ[volume]
      fun ξ => cmul (gradSymbol k ξ) (f ξ) :=
  h6 (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (gradSymbol k ξ)) 1
    (ofgrad_symbol_meas k) (ofgrad_symbol_bound k) f

theorem ofgrad_term_ae (h6 : FieldOpRealized) {φ : Space → Space} (hφ : IsTestField φ) (k : Fin 3) :
    (fieldOp id (fun ξ => cmul (gradSymbol k ξ))
      (freqTrR (complexify (toLpOrZero 2 (partialField φ k)))) : Space → CSpace) =ᵐ[volume]
      fun ξ => (2 * π * (ξ k) ^ 2 / ‖ξ‖ : ℝ) • (𝓕 (cplxRapid hφ.1 hφ.2.1)) ξ := by
  have e : freqTrR (complexify (toLpOrZero 2 (partialField φ k))) =
      (𝓕 (LineDeriv.lineDerivOp (unitVector k) (cplxRapid hφ.1 hφ.2.1))).toLp 2 := by
    rw [ofgrad_cplx_deriv hφ k]
    exact ofgrad_freqTr_toLp _
  rw [e]
  filter_upwards [ofgrad_fieldOp_ae h6 k _, SchwartzMap.coeFn_toLp
    (𝓕 (LineDeriv.lineDerivOp (unitVector k) (cplxRapid hφ.1 hφ.2.1))) 2 volume] with ξ h1 h2
  rw [h1, h2, SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), ofgrad_term]

theorem ofgrad_add3 (A B C : L2C) (a b c : Space → CSpace) (hA : (A : Space → CSpace) =ᵐ[volume] a)
    (hB : (B : Space → CSpace) =ᵐ[volume] b) (hC : (C : Space → CSpace) =ᵐ[volume] c) :
    ((A + B + C : L2C) : Space → CSpace) =ᵐ[volume] a + b + c := by
  filter_upwards [Lp.coeFn_add (A + B) C, Lp.coeFn_add A B, hA, hB, hC] with x h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, Pi.add_apply]

theorem embedX_halfSsp (h6 : FieldOpRealized) (h4 : EmbedMem) {φ : Space → Space}
    (hφ : IsTestField φ) :
    ∀ᵐ ξ ∂volume, ((embedX φ : X) : L2C) ξ =
      (2 * π * ‖ξ‖) • (freqTrL2 ((cplxRapid hφ.1 hφ.2.1).toLp 2) : Space → CSpace) ξ := by
  rw [ofgrad_embed_eq h4 hφ]
  have hR : (freqTrL2 ((cplxRapid hφ.1 hφ.2.1).toLp 2) : Space → CSpace) =ᵐ[volume]
      fun ξ => (𝓕 (cplxRapid hφ.1 hφ.2.1)) ξ := by
    rw [ofgrad_freqTr_toLp]
    exact SchwartzMap.coeFn_toLp _ 2 volume
  unfold ofGrad
  rw [Fin.sum_univ_three]
  filter_upwards [ofgrad_add3 _ _ _ _ _ _ (ofgrad_term_ae h6 hφ 0) (ofgrad_term_ae h6 hφ 1)
    (ofgrad_term_ae h6 hφ 2), hR] with ξ h1 h2
  rw [h1, h2, Pi.add_apply, Pi.add_apply, ← add_smul, ← add_smul, ofgrad_sum]

theorem pairing_integrable {θ : Space → Space} (h1 : ContDiff ℝ ∞ θ) (h2 : HasCompactSupport θ)
    (f : Space → Space) (hf : MemLp f 6 volume) :
    Integrable (fun y => inner ℝ (f y) (θ y)) volume := by
  have hθ : MemLp θ (ENNReal.conjExponent 6) volume := h1.continuous.memLp_of_hasCompactSupport h2
  have hb := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 6) (q := ENNReal.conjExponent 6)
    (r := 1) hf.1 hθ.1 (fun a b : Space => inner ℝ a b) 1
    (Filter.Eventually.of_forall fun y => by simpa using nnnorm_inner_le_nnnorm (𝕜 := ℝ) (f y) (θ y))
  refine memLp_one_iff_integrable.1 ⟨hf.1.inner hθ.1, lt_of_le_of_lt hb ?_⟩
  simpa using ENNReal.mul_lt_top hf.2 hθ.2

theorem pairing_bound {θ : Space → Space} (h1 : ContDiff ℝ ∞ θ) (h2 : HasCompactSupport θ)
    (f : Space → Space) (hf : MemLp f 6 volume) :
    ‖∫ y, inner ℝ (f y) (θ y)‖ ≤
      (eLpNorm f 6 volume).toReal * (eLpNorm θ (ENNReal.conjExponent 6) volume).toReal := by
  have hθ : MemLp θ (ENNReal.conjExponent 6) volume := h1.continuous.memLp_of_hasCompactSupport h2
  have hb := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 6) (q := ENNReal.conjExponent 6)
    (r := 1) hf.1 hθ.1 (fun a b : Space => inner ℝ a b) 1
    (Filter.Eventually.of_forall fun y => by simpa using nnnorm_inner_le_nnnorm (𝕜 := ℝ) (f y) (θ y))
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_norm_eq_lintegral_enorm (hf.1.inner hθ.1), ← eLpNorm_one_eq_lintegral_enorm,
    ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hf.2.ne hθ.2.ne) ?_
  simpa using hb

theorem velocity_embedX_test (h1 : VelocityExists) {φ : Space → Space} (hφ : IsTestField φ) :
    (velocity (embedX φ) : Space → Space) =ᵐ[volume] φ := by
  have hspec : VelocitySpec velocity := by
    have h1' : ∃ V, VelocitySpec V := h1
    unfold velocity
    rw [dif_pos h1']
    exact h1'.choose_spec
  rw [hspec φ hφ]
  have hm : MemLp φ 6 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
  unfold toLpOrZero
  rw [dif_pos hm]
  exact hm.coeFn_toLp

theorem continuous_velocity_pairing {θ : Space → Space} (h1 : ContDiff ℝ ∞ θ)
    (h2 : HasCompactSupport θ) :
    Continuous (fun x : X => ∫ y, inner ℝ ((velocity x : Space → Space) y) (θ y)) := by
  have hL : LipschitzWith (eLpNorm θ (ENNReal.conjExponent 6) volume).toNNReal
      (fun u : L6R => ∫ y, inner ℝ ((u : Space → Space) y) (θ y)) := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [dist_eq_norm, ← integral_sub (pairing_integrable h1 h2 _ (Lp.memLp u))
      (pairing_integrable h1 h2 _ (Lp.memLp v))]
    have hae : (fun y => inner ℝ ((u : Space → Space) y) (θ y) -
        inner ℝ ((v : Space → Space) y) (θ y)) =ᵐ[volume]
        fun y => inner ℝ (((u - v : L6R) : Space → Space) y) (θ y) := by
      filter_upwards [Lp.coeFn_sub u v] with y hy
      rw [hy, Pi.sub_apply, inner_sub_left]
    rw [integral_congr_ae hae, dist_eq_norm, Lp.norm_def, mul_comm]
    exact pairing_bound h1 h2 _ (Lp.memLp (u - v))
  exact hL.continuous.comp velocity.continuous

theorem ae_eq_of_pairing (u : L6R) (v : L2R)
    (h : ∀ θ : Space → Space, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      ∫ y, inner ℝ ((u : Space → Space) y) (θ y) = ∫ y, inner ℝ ((v : Space → Space) y) (θ y)) :
    (u : Space → Space) =ᵐ[volume] (v : Space → Space) := by
  have hu : LocallyIntegrable (u : Space → Space) volume :=
    (Lp.memLp u).locallyIntegrable (by norm_num)
  have hv : LocallyIntegrable (v : Space → Space) volume :=
    (Lp.memLp v).locallyIntegrable (by norm_num)
  refine ae_eq_of_integral_contDiff_smul_eq hu hv fun g hg hgs => ?_
  refine ext_inner_left ℝ fun w => ?_
  rw [← integral_inner (hu.integrable_smul_left_of_hasCompactSupport hg.continuous hgs),
    ← integral_inner (hv.integrable_smul_left_of_hasCompactSupport hg.continuous hgs)]
  have e : ∀ (f : Space → Space), (fun y => inner ℝ w (g y • f y)) =
      fun y => inner ℝ (f y) (g y • w) := by
    intro f
    ext y
    rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm]
  rw [e, e]
  exact h (fun y => g y • w) (hg.smul contDiff_const) (hgs.smul_right (f' := fun _ => w))

end Internal.VelocityInvert

open Internal.VelocityInvert in
theorem velocityInvertsHalfSsp (h1 : VelocityExists) (h2 : TestDense) (h3 : TestSpanSpec)
    (h4 : EmbedMem) (_h5 : EmbedLinear) (h6 : FieldOpRealized) (_h7 : GradCompatible) :
    VelocityInvertsHalfSsp := by
  intro g h hgh
  apply ae_eq_of_pairing
  intro θ t1 t2
  have key : ∀ x : X, ∫ y, inner ℝ ((velocity x : Space → Space) y) (θ y) =
      inner ℝ (x : L2C) ((memLp_thetaFun t1 t2).toLp _) := by
    have hcl : IsClosed {x : X | ∫ y, inner ℝ ((velocity x : Space → Space) y) (θ y) =
        inner ℝ (x : L2C) ((memLp_thetaFun t1 t2).toLp _)} :=
      isClosed_eq (continuous_velocity_pairing t1 t2)
        (continuous_subtype_val.inner continuous_const)
    have hsub : (testSpan : Set X) ⊆ {x : X | ∫ y, inner ℝ ((velocity x : Space → Space) y) (θ y) =
        inner ℝ (x : L2C) ((memLp_thetaFun t1 t2).toLp _)} := by
      intro x hx
      obtain ⟨φ, hφ, rfl⟩ := h3 x hx
      change ∫ y, inner ℝ ((velocity (embedX φ) : Space → Space) y) (θ y) =
        inner ℝ ((embedX φ : X) : L2C) ((memLp_thetaFun t1 t2).toLp _)
      rw [inner_thetaFun _ _ (embedX_halfSsp h6 h4 hφ) t1 t2, inner_freqTr_cplx]
      have e1 := velocity_embedX_test h1 hφ
      have e2 := toPhys_freqTr_cplx (φ := φ) hφ.1 hφ.2.1
      refine (integral_congr_ae (g := fun y => inner ℝ (φ y) (θ y)) ?_).trans
        (integral_congr_ae ?_).symm
      · filter_upwards [e1] with y hy
        rw [hy]
      · filter_upwards [e2] with y hy
        rw [hy]
    intro x
    exact (hcl.closure_subset_iff.2 hsub) (h2 x)
  rw [key h, inner_thetaFun _ _ hgh t1 t2, inner_freqTr_cplx]

end Breakdown.Freq
