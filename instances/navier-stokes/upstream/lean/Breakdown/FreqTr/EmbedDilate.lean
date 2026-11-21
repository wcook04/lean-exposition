import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.EmbedDilate

def scaleOp (a : ℝ) : L2C →L[ℝ] L2C :=
  fieldOp (fun ξ => a • ξ) (fun _ => ContinuousLinearMap.id ℝ CSpace)

def scaleEquiv (a : ℝ) (ha : a ≠ 0) : Space ≃L[ℝ] Space :=
  (LinearEquiv.smulOfNeZero ℝ Space a ha).toContinuousLinearEquiv

theorem scaleEquiv_coe (a : ℝ) (ha : a ≠ 0) : (scaleEquiv a ha : Space → Space) = fun ξ => a • ξ := rfl

theorem scaleOp_ae (h1 : FieldOpRealized) {a : ℝ} (ha : a ≠ 0) (g : L2C) :
    (scaleOp a g : Space → CSpace) =ᵐ[volume] fun ξ => (g : Space → CSpace) (a • ξ) := by
  have := h1 (scaleEquiv a ha) (fun _ => ContinuousLinearMap.id ℝ CSpace) 1 aestronglyMeasurable_const
    (fun _ => ContinuousLinearMap.norm_id_le) g
  rw [scaleEquiv_coe] at this
  simpa [scaleOp] using this

theorem ae_comp_smul {β : Type*} {a : ℝ} (ha : a ≠ 0) {u v : Space → β} (h : u =ᵐ[volume] v) :
    (fun ξ => u (a • ξ)) =ᵐ[volume] fun ξ => v (a • ξ) :=
  (Measure.quasiMeasurePreserving_smul volume ha).ae_eq_comp h

theorem norm_cmul_le (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
  simp [cmul, norm_smul]

theorem continuous_cmul : Continuous cmul := by
  have : cmul = fun c : ℂ => c • ContinuousLinearMap.id ℝ CSpace := by
    funext c; ext v; simp [cmul]
  rw [this]; fun_prop

theorem gradSymbol_norm_le (k : Fin 3) (ξ : Space) : ‖gradSymbol k ξ‖ ≤ 1 := by
  simp only [gradSymbol, norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_norm]
  exact div_le_one_of_le₀ (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ k) (norm_nonneg _)

theorem measurable_gradSymbol (k : Fin 3) : Measurable (gradSymbol k) := by
  unfold gradSymbol; fun_prop

theorem gradSymbol_smul (k : Fin 3) {a : ℝ} (ha : 0 < a) (ξ : Space) :
    gradSymbol k (a • ξ) = gradSymbol k ξ := by
  simp only [gradSymbol, PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_of_nonneg ha.le]
  push_cast
  rw [show Complex.I * ((a : ℂ) * ((ξ k : ℝ) : ℂ)) = (a : ℂ) * (Complex.I * ((ξ k : ℝ) : ℂ)) by ring,
    mul_div_mul_left _ _ (by exact_mod_cast ha.ne')]


theorem freqTr_comp_smul {s : ℝ} (hs : s ≠ 0) (f : Space → CSpace) (ξ : Space) :
    FourierTransform.fourier (fun x => f (s • x)) ξ =
      |(s ^ 3)⁻¹| • FourierTransform.fourier f (s⁻¹ • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have key : ∀ x : Space, Real.fourierChar (-inner ℝ x ξ) • f (s • x) =
      (fun y : Space => Real.fourierChar (-inner ℝ y (s⁻¹ • ξ)) • f y) (s • x) := by
    intro x
    simp only [real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  calc ∫ x : Space, Real.fourierChar (-inner ℝ x ξ) • f (s • x)
      = ∫ x : Space, (fun y : Space => Real.fourierChar (-inner ℝ y (s⁻¹ • ξ)) • f y) (s • x) :=
        integral_congr_ae (Filter.Eventually.of_forall key)
    _ = _ := by
        have := Measure.integral_comp_smul (volume : Measure Space)
          (fun y : Space => Real.fourierChar (-inner ℝ y (s⁻¹ • ξ)) • f y) s
        rw [finrank_euclideanSpace_fin] at this
        exact this

theorem freqTr_scaleOp (h1 : FieldOpRealized) {s : ℝ} (hs : s ≠ 0) (g : L2C) :
    freqTrR (scaleOp s g) = |(s ^ 3)⁻¹| • scaleOp s⁻¹ (freqTrR g) := by
  refine DenseRange.induction_on
    (SchwartzMap.denseRange_toLpCLM (F := CSpace) (p := 2) ENNReal.ofNat_ne_top (μ := volume)) g ?_ ?_
  · exact isClosed_eq (freqTrR ∘L scaleOp s).continuous
      ((|(s ^ 3)⁻¹| • (scaleOp s⁻¹ ∘L freqTrR)) : L2C →L[ℝ] L2C).continuous
  intro φ
  rw [SchwartzMap.toLpCLM_apply]
  set ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleEquiv s hs) φ with hψ
  have e1 : scaleOp s (φ.toLp 2) = ψ.toLp 2 := by
    apply Lp.ext
    filter_upwards [scaleOp_ae h1 hs (φ.toLp 2), ae_comp_smul hs (φ.coeFn_toLp 2), ψ.coeFn_toLp 2]
      with ξ h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    rfl
  have e2 : ∀ χ : SchwartzMap Space CSpace, freqTrR (χ.toLp 2) = (FourierTransform.fourier χ).toLp 2 :=
    fun χ => SchwartzMap.toLp_fourier_eq χ
  rw [e1, e2, e2]
  apply Lp.ext
  filter_upwards [(FourierTransform.fourier ψ).coeFn_toLp 2,
    Lp.coeFn_smul (|(s ^ 3)⁻¹|) (scaleOp s⁻¹ ((FourierTransform.fourier φ).toLp 2)),
    scaleOp_ae h1 (inv_ne_zero hs) ((FourierTransform.fourier φ).toLp 2),
    ae_comp_smul (inv_ne_zero hs) ((FourierTransform.fourier φ).coeFn_toLp 2)] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.smul_apply, h₃, h₄, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  exact freqTr_comp_smul hs φ ξ

theorem hasFDerivAt_scaled {f : Space → Space} (hf : Differentiable ℝ f) (s : ℝ) (y : Space) :
    HasFDerivAt (fun y => s • f (s • y)) ((s * s) • fderiv ℝ f (s • y)) y := by
  have h := ((hf (s • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul s)).const_smul s
  have e : s • (fderiv ℝ f (s • y)).comp (s • ContinuousLinearMap.id ℝ Space) =
      (s * s) • fderiv ℝ f (s • y) := by
    ext v
    simp [smul_smul]
  rw [e] at h
  exact h

theorem scaled_bound {s C r : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hr : 0 ≤ r) :
    s * (C / (1 + s * r)) ≤ (s + 1) ^ 2 * C / (1 + r) ∧
      s * s * (C / (1 + s * r) ^ 2) ≤ (s + 1) ^ 2 * C / (1 + r) ^ 2 := by
  have ha : 0 < 1 + s * r := by positivity
  have hb : 0 < 1 + r := by positivity
  have key : s * (1 + r) ≤ (s + 1) * (1 + s * r) := by nlinarith [mul_nonneg hs.le hr]
  have key2 : s * (1 + r) ≤ (s + 1) ^ 2 * (1 + s * r) := by nlinarith [mul_nonneg hs.le hr]
  have sq : (s * (1 + r)) ^ 2 ≤ ((s + 1) * (1 + s * r)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) key 2
  constructor
  · rw [← mul_div_assoc, div_le_div_iff₀ ha hb]
    nlinarith [mul_le_mul_of_nonneg_left key2 hC]
  · rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left sq hC]

theorem isDecayField_scaled {f : Space → Space} (hf : IsDecayField f) {s : ℝ} (hs : 0 < s) :
    IsDecayField (fun y => s • f (s • y)) := by
  obtain ⟨hcd, hdiv, C, hC⟩ := hf
  have hdiff : Differentiable ℝ f := hcd.differentiable (by simp)
  have hfd : ∀ y, fderiv ℝ (fun y => s • f (s • y)) y = (s * s) • fderiv ℝ f (s • y) :=
    fun y => (hasFDerivAt_scaled hdiff s y).fderiv
  have hC0 : 0 ≤ C := by
    have := (hC 0).1
    simp only [norm_zero, add_zero, div_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨(hcd.comp (contDiff_id.const_smul s)).const_smul s, fun y => ?_, (s + 1) ^ 2 * C, fun y => ?_⟩
  · simp only [divergenceAt, hfd, FunLike.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul,
      ← Finset.mul_sum]
    have := hdiv (s • y)
    simp only [divergenceAt] at this
    rw [this, mul_zero]
  · have hn : ‖s • y‖ = s * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
    obtain ⟨b1, b2⟩ := scaled_bound hs hC0 (norm_nonneg y)
    obtain ⟨c1, c2⟩ := hC (s • y)
    rw [hn] at c1 c2
    constructor
    · rw [norm_smul, Real.norm_of_nonneg hs.le]
      exact (mul_le_mul_of_nonneg_left c1 hs.le).trans b1
    · rw [hfd, norm_smul, Real.norm_of_nonneg (mul_nonneg hs.le hs.le)]
      exact (mul_le_mul_of_nonneg_left c2 (mul_nonneg hs.le hs.le)).trans b2

theorem isDecayField_dilate {f : Space → Space} (hf : IsDecayField f) {μ : ℝ} (hμ : 0 < μ) :
    IsDecayField (dilateField μ f) :=
  isDecayField_scaled hf (Real.sqrt_pos.2 hμ)

theorem partialField_dilate {f : Space → Space} (hf : IsDecayField f) {μ : ℝ} (hμ : 0 < μ) (k : Fin 3) :
    partialField (dilateField μ f) k = fun y => μ • partialField f k (Real.sqrt μ • y) := by
  funext y
  have hdiff : Differentiable ℝ f := hf.1.differentiable (by simp)
  show fderiv ℝ (fun y => Real.sqrt μ • f (Real.sqrt μ • y)) y (unitVector k) = _
  rw [(hasFDerivAt_scaled hdiff (Real.sqrt μ) y).fderiv, Real.mul_self_sqrt hμ.le]
  rfl

theorem memLp_partialField {f : Space → Space} (hf : IsDecayField f) (k : Fin 3) :
    MemLp (partialField f k) 2 volume := by
  obtain ⟨hcd, -, C, hC⟩ := hf
  have hcont : Continuous (partialField f k) :=
    (hcd.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have hint := (integrable_one_add_norm (μ := (volume : Measure Space)) (r := 4)
    (by rw [finrank_euclideanSpace_fin]; norm_num)).const_mul (C ^ 2)
  refine hint.mono' (hcont.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hpos : 0 < 1 + ‖x‖ := by positivity
  have hb : ‖partialField f k x‖ ≤ C / (1 + ‖x‖) ^ 2 := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [show ‖unitVector k‖ = 1 by simp [unitVector], mul_one]
    exact (hC x).2
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hpos.le,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ‖partialField f k x‖ ^ 2 ≤ (C / (1 + ‖x‖) ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = C ^ 2 * ((1 + ‖x‖) ^ 4)⁻¹ := by field_simp

theorem complexify_dilate (h1 : FieldOpRealized) {f : Space → Space} (hf : IsDecayField f) {μ : ℝ}
    (hμ : 0 < μ) (k : Fin 3) :
    complexify (toLpOrZero 2 (partialField (dilateField μ f) k)) =
      μ • scaleOp (Real.sqrt μ) (complexify (toLpOrZero 2 (partialField f k))) := by
  have m1 := memLp_partialField hf k
  have m2 := memLp_partialField (isDecayField_dilate hf hμ) k
  have hs : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
  simp only [toLpOrZero, dif_pos m1, dif_pos m2]
  unfold complexify
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec (m2.toLp _),
    m2.coeFn_toLp,
    Lp.coeFn_smul μ (scaleOp (Real.sqrt μ) (ContinuousLinearMap.compLpL 2 volume complexifyVec (m1.toLp _))),
    scaleOp_ae h1 hs (ContinuousLinearMap.compLpL 2 volume complexifyVec (m1.toLp _)),
    ae_comp_smul hs (ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec (m1.toLp _)),
    ae_comp_smul hs m1.coeFn_toLp] with ξ a b c d e g
  rw [a, b, c, Pi.smul_apply, d, e, g, partialField_dilate hf hμ k]
  exact map_smul complexifyVec μ _

theorem gradHat_dilate (h1 : FieldOpRealized) {f : Space → Space} (hf : IsDecayField f) {μ : ℝ}
    (hμ : 0 < μ) (k : Fin 3) :
    gradHat (dilateField μ f) k = (Real.sqrt μ)⁻¹ • scaleOp (Real.sqrt μ)⁻¹ (gradHat f k) := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  unfold gradHat
  rw [complexify_dilate h1 hf hμ k, map_smul, freqTr_scaleOp h1 hs.ne', smul_smul]
  congr 1
  have e : μ = Real.sqrt μ * Real.sqrt μ := (Real.mul_self_sqrt hμ.le).symm
  rw [abs_of_pos (by positivity)]
  set s := Real.sqrt μ
  clear_value s
  subst e
  field_simp

theorem mult_scaleOp (h1 : FieldOpRealized) (k : Fin 3) {a : ℝ} (ha : 0 < a) (g : L2C) :
    fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (scaleOp a g) =
      scaleOp a (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) g) := by
  have hM : ∀ h : L2C, (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) h : Space → CSpace) =ᵐ[volume]
      fun ξ => cmul (gradSymbol k ξ) ((h : Space → CSpace) ξ) := by
    intro h
    have := h1 (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (gradSymbol k ξ)) 1
      (continuous_cmul.comp_aestronglyMeasurable (measurable_gradSymbol k).aestronglyMeasurable)
      (fun ξ => (norm_cmul_le _).trans (gradSymbol_norm_le k ξ)) h
    simpa using this
  apply Lp.ext
  filter_upwards [hM (scaleOp a g), scaleOp_ae h1 ha.ne' g,
    scaleOp_ae h1 ha.ne' (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) g), ae_comp_smul ha.ne' (hM g)]
    with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, gradSymbol_smul k ha]

theorem dilL2_eq (h1 : FieldOpRealized) {μ : ℝ} (hμ : 0 < μ) (g : L2C) :
    dilL2 μ g = (Real.sqrt μ)⁻¹ • scaleOp (Real.sqrt μ)⁻¹ g := by
  have hc : (Real.sqrt μ)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hμ).ne'
  have := h1 (scaleEquiv _ hc) (fun _ => (Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ CSpace)
    ‖(Real.sqrt μ)⁻¹‖ aestronglyMeasurable_const
    (fun _ => by rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le) g
  rw [scaleEquiv_coe] at this
  unfold dilL2
  apply Lp.ext
  filter_upwards [this, Lp.coeFn_smul (Real.sqrt μ)⁻¹ (scaleOp (Real.sqrt μ)⁻¹ g), scaleOp_ae h1 hc g]
    with ξ a b c
  rw [a, b, Pi.smul_apply, c]
  rfl

theorem ofGrad_dilate (h1 : FieldOpRealized) {f : Space → Space} (hf : IsDecayField f) {μ : ℝ}
    (hμ : 0 < μ) : ofGrad (dilateField μ f) = dilL2 μ (ofGrad f) := by
  rw [dilL2_eq h1 hμ]
  change ∑ k : Fin 3, fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (gradHat (dilateField μ f) k) =
    (Real.sqrt μ)⁻¹ • scaleOp (Real.sqrt μ)⁻¹
      (∑ k : Fin 3, fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (gradHat f k))
  simp only [gradHat_dilate h1 hf hμ, map_smul, mult_scaleOp h1 _ (inv_pos.2 (Real.sqrt_pos.2 hμ)),
    map_sum, Finset.smul_sum]

end Internal.EmbedDilate

theorem embedDilate (h1 : FieldOpRealized) (h2 : DilationAlgebra) (h3 : EmbedMem) :
    EmbedDilate := by
  intro μ f hμ hf
  have hd := Internal.EmbedDilate.isDecayField_dilate hf hμ
  apply Subtype.ext
  rw [h2.2.2.2.2 μ hμ]
  simp only [embedX, dif_pos (h3 f hf), dif_pos (h3 _ hd)]
  exact (Internal.EmbedDilate.ofGrad_dilate h1 hf hμ).symm


end Breakdown.Freq
