import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.EmbedNorm

private theorem toLpOrZero_eq {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f : Space → F}
    (h : MemLp f p volume) : toLpOrZero p f = h.toLp f := by
  unfold toLpOrZero; rw [dif_pos h]

private theorem memLp_partialField {f : Space → Space} (hf : IsDecayField f) (k : Fin 3) :
    MemLp (partialField f k) 2 volume := by
  obtain ⟨hs, -, C, hC⟩ := hf
  have hcont : Continuous (partialField f k) :=
    ((hs.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) volume :=
    integrable_one_add_norm (by simp; norm_num)
  have hg : MemLp (fun y : Space => C * (1 + ‖y‖) ^ (-(2 : ℝ))) 2 volume := by
    have hc : Continuous (fun y : Space => C * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
      continuous_const.mul ((continuous_const.add continuous_norm).rpow_const
        fun y => Or.inl (ne_of_gt (show (0:ℝ) < 1 + ‖y‖ by positivity)))
    refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_
    refine (hint.const_mul (C ^ 2)).congr (Filter.Eventually.of_forall fun y => ?_)
    have h1 : (0 : ℝ) < 1 + ‖y‖ := by positivity
    show C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) = ‖C * (1 + ‖y‖) ^ (-(2 : ℝ))‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs, mul_pow, ← Real.rpow_natCast ((1 + ‖y‖) ^ (-(2:ℝ))) 2,
      ← Real.rpow_mul h1.le]
    norm_num
  refine hg.of_le hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have h1 : (0 : ℝ) < 1 + ‖y‖ := by positivity
  calc ‖partialField f k y‖ ≤ ‖fderiv ℝ f y‖ * ‖unitVector k‖ := (fderiv ℝ f y).le_opNorm _
    _ = ‖fderiv ℝ f y‖ := by simp [unitVector]
    _ ≤ C / (1 + ‖y‖) ^ 2 := (hC y).2
    _ ≤ ‖C * (1 + ‖y‖) ^ (-(2 : ℝ))‖ := by
      rw [Real.rpow_neg h1.le, div_eq_mul_inv]
      norm_cast
      exact le_abs_self _

private theorem partialField_add {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g)
    (k : Fin 3) : partialField (f + g) k = partialField f k + partialField g k := by
  funext x
  simp only [partialField, Pi.add_apply]
  rw [fderiv_add (hf.1.differentiable (by simp) x) (hg.1.differentiable (by simp) x)]
  rfl

private theorem partialField_sub {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g)
    (k : Fin 3) : partialField (f - g) k = partialField f k - partialField g k := by
  funext x
  simp only [partialField, Pi.sub_apply]
  rw [fderiv_sub (hf.1.differentiable (by simp) x) (hg.1.differentiable (by simp) x)]
  rfl

private theorem partialField_smul (c : ℝ) (f : Space → Space) (k : Fin 3) :
    partialField (c • f) k = c • partialField f k := by
  funext x
  simp only [partialField, Pi.smul_apply, fderiv_const_smul_field]
  rfl

private theorem ofGrad_add {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g) :
    ofGrad (f + g) = ofGrad f + ofGrad g := by
  have h : ∀ k, toLpOrZero 2 (partialField (f + g) k) =
      toLpOrZero 2 (partialField f k) + toLpOrZero 2 (partialField g k) := by
    intro k
    rw [partialField_add hf hg, toLpOrZero_eq ((memLp_partialField hf k).add (memLp_partialField hg k)),
      toLpOrZero_eq (memLp_partialField hf k), toLpOrZero_eq (memLp_partialField hg k)]
    exact MemLp.toLp_add _ _
  simp only [ofGrad, h, map_add, Finset.sum_add_distrib]

private theorem ofGrad_sub {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g) :
    ofGrad (f - g) = ofGrad f - ofGrad g := by
  have h : ∀ k, toLpOrZero 2 (partialField (f - g) k) =
      toLpOrZero 2 (partialField f k) - toLpOrZero 2 (partialField g k) := by
    intro k
    rw [partialField_sub hf hg, toLpOrZero_eq ((memLp_partialField hf k).sub (memLp_partialField hg k)),
      toLpOrZero_eq (memLp_partialField hf k), toLpOrZero_eq (memLp_partialField hg k)]
    exact MemLp.toLp_sub _ _
  simp only [ofGrad, h, map_sub, Finset.sum_sub_distrib]

private theorem ofGrad_smul (c : ℝ) {f : Space → Space} (hf : IsDecayField f) :
    ofGrad (c • f) = c • ofGrad f := by
  have h : ∀ k, toLpOrZero 2 (partialField (c • f) k) = c • toLpOrZero 2 (partialField f k) := by
    intro k
    rw [partialField_smul, toLpOrZero_eq ((memLp_partialField hf k).const_smul c),
      toLpOrZero_eq (memLp_partialField hf k)]
    exact MemLp.toLp_const_smul _ _
  simp only [ofGrad, h, map_smul, Finset.smul_sum]

private theorem embedX_coe {f : Space → Space} (h : ofGrad f ∈ Sig) : (embedX f : L2C) = ofGrad f := by
  unfold embedX
  rw [dif_pos h]

private theorem embedLinear_of (h3 : EmbedMem) : EmbedLinear := by
  refine ⟨fun f g hf hg => ?_, fun f g hf hg => ?_, fun c f hf => ?_⟩
  · apply Subtype.ext
    rw [Submodule.coe_add, embedX_coe (h3 f hf), embedX_coe (h3 g hg),
      embedX_coe (by rw [ofGrad_add hf hg]; exact add_mem (h3 f hf) (h3 g hg)), ofGrad_add hf hg]
  · apply Subtype.ext
    rw [Submodule.coe_sub, embedX_coe (h3 f hf), embedX_coe (h3 g hg),
      embedX_coe (by rw [ofGrad_sub hf hg]; exact sub_mem (h3 f hf) (h3 g hg)), ofGrad_sub hf hg]
  · apply Subtype.ext
    rw [Submodule.coe_smul, embedX_coe (h3 f hf),
      embedX_coe (by rw [ofGrad_smul c hf]; exact Submodule.smul_mem _ c (h3 f hf)), ofGrad_smul c hf]

private theorem norm_sq_Lp_eq (𝕜 : Type*) [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (u : Lp (α := Space) F 2) : ‖u‖ ^ 2 = ∫ ξ, ‖(u : Space → F) ξ‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := 𝕜) u u)]
  congr 1
  funext ξ
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜)]

private theorem norm_sq_sum_gradSymbol {ξ : Space} (hξ : ξ ≠ 0) (a : Fin 3 → CSpace)
    (hc : ∀ j k : Fin 3, (ξ k : ℝ) • a j = (ξ j : ℝ) • a k) :
    ‖∑ k, gradSymbol k ξ • a k‖ ^ 2 = ∑ k, ‖a k‖ ^ 2 := by
  set w : CSpace := ∑ i, (ξ i : ℝ) • a i with hw
  have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hsq : ‖ξ‖ ^ 2 = ∑ i, (ξ i) ^ 2 := EuclideanSpace.real_norm_sq_eq ξ
  have h1 : ∑ k, gradSymbol k ξ • a k = (-(Complex.I / (‖ξ‖ : ℂ))) • w := by
    rw [hw, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Complex.coe_smul, smul_smul]
    congr 1
    simp only [gradSymbol]
    ring
  have h2 : ∀ k, (‖ξ‖ ^ 2) • a k = (ξ k : ℝ) • w := by
    intro k
    rw [hsq, Finset.sum_smul, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [sq, mul_smul, ← hc i k, smul_comm]
  have h3 : ‖ξ‖ ^ 2 * ‖w‖ ^ 2 = ‖ξ‖ ^ 2 * (‖ξ‖ ^ 2 * ∑ k, ‖a k‖ ^ 2) := by
    have e : ∀ k, ‖(‖ξ‖ ^ 2) • a k‖ ^ 2 = ‖(ξ k : ℝ) • w‖ ^ 2 := fun k => by rw [h2 k]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, abs_pow, abs_norm] at e
    calc ‖ξ‖ ^ 2 * ‖w‖ ^ 2 = ∑ k, (ξ k) ^ 2 * ‖w‖ ^ 2 := by rw [hsq, Finset.sum_mul]
      _ = ∑ k, (‖ξ‖ ^ 2) ^ 2 * ‖a k‖ ^ 2 := Finset.sum_congr rfl fun k _ => (e k).symm
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hp : 0 < ‖ξ‖ ^ 2 := by positivity
  have h4 : ‖w‖ ^ 2 = ‖ξ‖ ^ 2 * ∑ k, ‖a k‖ ^ 2 := mul_left_cancel₀ hp.ne' h3
  have h5 : ‖-(Complex.I / (‖ξ‖ : ℂ))‖ = ‖ξ‖⁻¹ := by simp
  rw [h1, norm_smul, mul_pow, h5, h4]
  field_simp

private theorem cmul_apply (c : ℂ) (z : CSpace) : cmul c z = c • z := rfl

private theorem norm_cmul_le (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => by rw [cmul_apply, norm_smul]

private theorem cmul_sub (a b : ℂ) : cmul a - cmul b = cmul (a - b) := by
  ext1 z
  simp [cmul_apply, sub_smul]

private theorem continuous_cmul : Continuous cmul :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun a b => by
    rw [dist_eq_norm, dist_eq_norm, cmul_sub]
    simpa using norm_cmul_le (a - b)).continuous

private theorem measurable_gradSymbol (k : Fin 3) : Measurable (gradSymbol k) := by
  unfold gradSymbol
  fun_prop

private theorem norm_gradSymbol_le (k : Fin 3) (ξ : Space) : ‖gradSymbol k ξ‖ ≤ 1 := by
  simp only [gradSymbol, norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_norm]
  exact div_le_one_of_le₀ (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le ξ k) (norm_nonneg _)

private theorem gradOp_ae (h1 : FieldOpRealized) (k : Fin 3) (u : L2C) :
    (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) u : Space → CSpace) =ᵐ[volume]
      fun ξ => gradSymbol k ξ • (u : Space → CSpace) ξ := by
  have h := h1 (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (gradSymbol k ξ)) 1
    (continuous_cmul.comp_aestronglyMeasurable (measurable_gradSymbol k).aestronglyMeasurable)
    (fun ξ => (norm_cmul_le _).trans (norm_gradSymbol_le k ξ))
  rw [ContinuousLinearEquiv.coe_refl'] at h
  filter_upwards [h u] with ξ hξ
  rw [hξ]
  rfl

private theorem ofGrad_ae (h1 : FieldOpRealized) (f : Space → Space) :
    (ofGrad f : Space → CSpace) =ᵐ[volume]
      fun ξ => ∑ k, gradSymbol k ξ • (gradHat f k : Space → CSpace) ξ := by
  have e : ofGrad f = ∑ k, fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (gradHat f k) := rfl
  rw [e]
  simp only [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (fieldOp id (fun ξ => cmul (gradSymbol 0 ξ)) (gradHat f 0) +
      fieldOp id (fun ξ => cmul (gradSymbol 1 ξ)) (gradHat f 1))
      (fieldOp id (fun ξ => cmul (gradSymbol 2 ξ)) (gradHat f 2)),
    Lp.coeFn_add (fieldOp id (fun ξ => cmul (gradSymbol 0 ξ)) (gradHat f 0))
      (fieldOp id (fun ξ => cmul (gradSymbol 1 ξ)) (gradHat f 1)),
    gradOp_ae h1 0 (gradHat f 0), gradOp_ae h1 1 (gradHat f 1), gradOp_ae h1 2 (gradHat f 2)]
    with ξ ha hb h0 h1' h2'
  rw [ha, Pi.add_apply, hb, Pi.add_apply, h0, h1', h2']

private theorem norm_complexify_sq (v : L2R) : ‖complexify v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [norm_sq_Lp_eq ℂ, norm_sq_Lp_eq ℝ]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec v] with ξ hξ
  have e : (complexify v : Space → CSpace) ξ = complexifyVec ((v : Space → Space) ξ) := hξ
  rw [e]
  simp [complexifyVec, EuclideanSpace.norm_sq_eq]

private theorem norm_gradHat_sq {f : Space → Space} (hf : IsDecayField f) (k : Fin 3) :
    ‖gradHat f k‖ ^ 2 = ∫ y, ‖fderiv ℝ f y (unitVector k)‖ ^ 2 := by
  have e1 : ‖gradHat f k‖ = ‖complexify (toLpOrZero 2 (partialField f k))‖ :=
    LinearIsometryEquiv.norm_map freqTrL2 _
  rw [e1, norm_complexify_sq, toLpOrZero_eq (memLp_partialField hf k), norm_sq_Lp_eq ℝ]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_partialField hf k).coeFn_toLp] with y hy
  rw [hy]
  rfl

private theorem embedNorm_of (h1 : FieldOpRealized) (h2 : GradCompatible) (h3 : EmbedMem) : EmbedNorm := by
  intro f hf
  have en : ‖embedX f‖ = ‖ofGrad f‖ := by
    rw [← embedX_coe (h3 f hf)]
    rfl
  rw [en, norm_sq_Lp_eq ℂ]
  have hae : ∀ᵐ ξ ∂volume, ‖(ofGrad f : Space → CSpace) ξ‖ ^ 2 =
      ∑ k, ‖(gradHat f k : Space → CSpace) ξ‖ ^ 2 := by
    have hc : ∀ᵐ ξ ∂volume, ∀ j k : Fin 3,
        (ξ k : ℝ) • (gradHat f j : Space → CSpace) ξ = (ξ j : ℝ) • (gradHat f k : Space → CSpace) ξ := by
      rw [Filter.eventually_all]
      intro j
      rw [Filter.eventually_all]
      intro k
      exact h2 f hf j k
    filter_upwards [ofGrad_ae h1 f, hc, Measure.ae_ne volume (0 : Space)] with ξ he hc' hne
    rw [he]
    exact norm_sq_sum_gradSymbol hne _ hc'
  rw [integral_congr_ae hae, integral_finsetSum _ (fun k _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp (gradHat f k))),
    integral_finsetSum (f := fun k y => ‖fderiv ℝ f y (unitVector k)‖ ^ 2) _ (fun k _ =>
      (memLp_two_iff_integrable_sq_norm (memLp_partialField hf k).1).1 (memLp_partialField hf k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← norm_sq_Lp_eq ℂ, norm_gradHat_sq hf k]

end Internal.EmbedNorm

theorem embedNormLinear (h1 : FieldOpRealized) (h2 : GradCompatible) (h3 : EmbedMem) :
    EmbedNorm ∧ EmbedLinear :=
  ⟨Internal.EmbedNorm.embedNorm_of h1 h2 h3, Internal.EmbedNorm.embedLinear_of h3⟩

end Breakdown.Freq
