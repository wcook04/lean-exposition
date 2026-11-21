import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

open FourierTransform

namespace Internal.EmbedRot

def rotComp (R : Space ≃ₗᵢ[ℝ] Space) (A : CSpace →L[ℂ] CSpace) (g : L2C) : L2C :=
  A.compLp (Lp.compMeasurePreserving R.symm (LinearIsometryEquiv.measurePreserving R.symm) g)

theorem coeFn_rotComp (R : Space ≃ₗᵢ[ℝ] Space) (A : CSpace →L[ℂ] CSpace) (g : L2C) :
    (rotComp R A g : Space → CSpace) =ᵐ[volume] fun x => A (g (R.symm x)) := by
  unfold rotComp
  filter_upwards [A.coeFn_compLp (Lp.compMeasurePreserving R.symm (LinearIsometryEquiv.measurePreserving R.symm) g),
    Lp.coeFn_compMeasurePreserving g (LinearIsometryEquiv.measurePreserving R.symm)] with x h1 h2
  rw [h1, h2]
  rfl

theorem continuous_rotComp (R : Space ≃ₗᵢ[ℝ] Space) (A : CSpace →L[ℂ] CSpace) :
    Continuous (rotComp R A) := by
  unfold rotComp
  exact (A.compLpL 2 volume).continuous.comp
    (Lp.isometry_compMeasurePreserving (LinearIsometryEquiv.measurePreserving R.symm)).continuous

theorem freqTr_rapid_rot (R : Space ≃ₗᵢ[ℝ] Space) (A : CSpace →L[ℂ] CSpace)
    (φ : SchwartzMap Space CSpace) (ξ : Space) :
    𝓕 (fun x => A (φ (R.symm x))) ξ = A (𝓕 (φ : Space → CSpace) (R.symm ξ)) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hint : Integrable (fun v : Space => 𝐞 (-inner ℝ v (R.symm ξ)) • φ v) :=
    (Real.fourierIntegral_convergent_iff (R.symm ξ)).2 (SchwartzMap.integrable φ)
  have hcv : ∫ v, 𝐞 (-inner ℝ v ξ) • A (φ (R.symm v)) =
      ∫ v, 𝐞 (-inner ℝ (R v) ξ) • A (φ (R.symm (R v))) :=
    ((LinearIsometryEquiv.measurePreserving R).integral_comp R.toHomeomorph.measurableEmbedding
      (fun v => 𝐞 (-inner ℝ v ξ) • A (φ (R.symm v)))).symm
  rw [hcv, ← A.integral_comp_comm hint]
  congr 1
  ext1 v
  simp only [LinearIsometryEquiv.symm_apply_apply]
  have h : inner ℝ (R v) ξ = inner ℝ v (R.symm ξ) := by
    rw [← R.inner_map_map v (R.symm ξ), LinearIsometryEquiv.apply_symm_apply]
  rw [h, Circle.smul_def, Circle.smul_def, A.map_smul]

theorem freqTr_rotComp (R : Space ≃ₗᵢ[ℝ] Space) (A : CSpace →L[ℂ] CSpace) (g : L2C) :
    freqTrL2 (rotComp R A g) = rotComp R A (freqTrL2 g) := by
  refine DenseRange.induction_on
    (p := fun g : L2C => freqTrL2 (rotComp R A g) = rotComp R A (freqTrL2 g))
    (SchwartzMap.denseRange_toLpCLM (F := CSpace) (μ := (volume : Measure Space))
      (p := 2) ENNReal.ofNat_ne_top) g ?_ ?_
  · exact isClosed_eq (freqTrL2.continuous.comp (continuous_rotComp R A))
      ((continuous_rotComp R A).comp freqTrL2.continuous)
  · intro φ
    simp only [SchwartzMap.toLpCLM_apply]
    set ψ : SchwartzMap Space CSpace := SchwartzMap.postcompCLM A
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ R.symm.toContinuousLinearEquiv φ) with hψdef
    have hψ : ∀ x, ψ x = A (φ (R.symm x)) := fun x => rfl
    have h1 : rotComp R A (φ.toLp 2) = ψ.toLp 2 := by
      refine Lp.ext ?_
      have hc := (LinearIsometryEquiv.measurePreserving R.symm).quasiMeasurePreserving.ae_eq_comp
        (SchwartzMap.coeFn_toLp φ 2 (volume : Measure Space))
      filter_upwards [coeFn_rotComp R A (φ.toLp 2), SchwartzMap.coeFn_toLp ψ 2 (volume : Measure Space), hc]
        with x h2 h3 h4
      rw [h2, h3, hψ]
      simp only [Function.comp_apply] at h4
      rw [h4]
    have h5 : freqTrL2 (φ.toLp 2) = (𝓕 φ).toLp 2 := SchwartzMap.toLp_fourier_eq φ
    have h6 : freqTrL2 (ψ.toLp 2) = (𝓕 ψ).toLp 2 := SchwartzMap.toLp_fourier_eq ψ
    show freqTrL2 (rotComp R A (φ.toLp 2)) = rotComp R A (freqTrL2 (φ.toLp 2))
    rw [h1, h5, h6]
    refine Lp.ext ?_
    have hc := (LinearIsometryEquiv.measurePreserving R.symm).quasiMeasurePreserving.ae_eq_comp
      (SchwartzMap.coeFn_toLp (𝓕 φ) 2 (volume : Measure Space))
    filter_upwards [coeFn_rotComp R A ((𝓕 φ).toLp 2), SchwartzMap.coeFn_toLp (𝓕 ψ) 2 (volume : Measure Space), hc]
      with x h2 h3 h4
    rw [h2, h3]
    simp only [Function.comp_apply] at h4
    rw [h4, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    have hfun : (ψ : Space → CSpace) = fun x => A (φ (R.symm x)) := funext hψ
    rw [hfun, freqTr_rapid_rot]


def rotCplx (R : Space ≃ₗᵢ[ℝ] Space) : CSpace →L[ℂ] CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => ∑ j : Fin 3, ((R (unitVector j) i : ℝ) : ℂ) * z j)
      map_add' := fun a b => by ext i; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        ext i; simp [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring) }

theorem rotCplx_apply (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : rotCplx R z = rotC R z := rfl

theorem vec_decomp (v : Space) : v = ∑ k : Fin 3, v k • unitVector k := by
  ext i
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem complexifyVec_rot (R : Space ≃ₗᵢ[ℝ] Space) (v : Space) :
    complexifyVec (R v) = rotCplx R (complexifyVec v) := by
  conv_lhs => rw [vec_decomp v]
  ext i
  simp [rotCplx, complexifyVec, map_smul, Fin.sum_univ_three, mul_comm]

theorem memLp_dir (f : Space → Space) (hf : IsDecayField f) (w : Space) :
    MemLp (fun z => fderiv ℝ f z w) 2 volume := by
  obtain ⟨hs, -, C, hC⟩ := hf
  have hcont : Continuous (fun z => fderiv ℝ f z w) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdom : MemLp (fun z : Space => (C * ‖w‖) * (1 + ‖z‖) ^ (-(2 : ℝ))) 2 volume := by
    have hm : AEStronglyMeasurable (fun z : Space => (C * ‖w‖) * (1 + ‖z‖) ^ (-(2 : ℝ))) volume := by
      refine Continuous.aestronglyMeasurable ?_
      refine continuous_const.mul ?_
      exact (continuous_const.add continuous_norm).rpow_const
        (fun z => Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg one_pos (norm_nonneg z))))
    refine (memLp_two_iff_integrable_sq hm).2 ?_
    have hi : Integrable (fun z : Space => (1 + ‖z‖) ^ (-(4 : ℝ))) volume :=
      integrable_one_add_norm (by simp; norm_num)
    refine (hi.const_mul ((C * ‖w‖) ^ 2)).congr (Filter.Eventually.of_forall fun z => ?_)
    have hp : (0 : ℝ) < 1 + ‖z‖ := by positivity
    have key : ((1 + ‖z‖) ^ (-(2 : ℝ))) ^ 2 = (1 + ‖z‖) ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num
    have e : (C * ‖w‖ * (1 + ‖z‖) ^ (-(2 : ℝ))) ^ 2 =
        (C * ‖w‖) ^ 2 * ((1 + ‖z‖) ^ (-(2 : ℝ))) ^ 2 := by ring
    simp only
    rw [e, key]
  refine hdom.of_le hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  have hp : (0 : ℝ) < 1 + ‖z‖ := by positivity
  have h1 := (hC z).2
  have h2 : ‖fderiv ℝ f z w‖ ≤ ‖fderiv ℝ f z‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
  have h3 : C / (1 + ‖z‖) ^ 2 = C * (1 + ‖z‖) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hp.le, div_eq_mul_inv]; norm_cast
  rw [Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  calc ‖fderiv ℝ f z w‖ ≤ ‖fderiv ℝ f z‖ * ‖w‖ := h2
    _ ≤ (C * (1 + ‖z‖) ^ (-(2 : ℝ))) * ‖w‖ := by rw [← h3]; gcongr
    _ = _ := by ring

theorem partialField_push (R : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) (hf : ContDiff ℝ ∞ f)
    (l : Fin 3) (y : Space) :
    partialField (pushForward R f) l y =
      ∑ k : Fin 3, (R.symm (unitVector l)) k • R (partialField f k (R.symm y)) := by
  have hd : DifferentiableAt ℝ f (R.symm y) := (hf.differentiable (by simp)) _
  have hder : HasFDerivAt (pushForward R f)
      ((R.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
        ((fderiv ℝ f (R.symm y)).comp (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space))) y :=
    R.toContinuousLinearEquiv.hasFDerivAt.comp y
      (hd.hasFDerivAt.comp y R.symm.toContinuousLinearEquiv.hasFDerivAt)
  unfold partialField
  rw [hder.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  conv_lhs => rw [vec_decomp (R.symm (unitVector l))]
  simp [map_sum, map_smul]

theorem symbol_rot (R : Space ≃ₗᵢ[ℝ] Space) (ξ : Space) (k : Fin 3) :
    ∑ l : Fin 3, gradSymbol l ξ * (((R.symm (unitVector l)) k : ℝ) : ℂ) = gradSymbol k (R.symm ξ) := by
  have hk : (R.symm ξ) k = ∑ l : Fin 3, ξ l * (R.symm (unitVector l)) k := by
    conv_lhs => rw [vec_decomp ξ]
    simp [map_sum, map_smul]
  unfold gradSymbol
  rw [hk, LinearIsometryEquiv.norm_map]
  push_cast
  rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring


theorem toLpOrZero_of {g : Space → Space} (hg : MemLp g 2 volume) : toLpOrZero 2 g = hg.toLp g := by
  unfold toLpOrZero
  rw [dif_pos hg]

theorem ae_complexify (g : Space → Space) (hg : MemLp g 2 volume) :
    (complexify (toLpOrZero 2 g) : Space → CSpace) =ᵐ[volume] fun y => complexifyVec (g y) := by
  rw [toLpOrZero_of hg]
  have h1 : (complexify (hg.toLp g) : Space → CSpace) =ᵐ[volume]
      fun y => complexifyVec ((hg.toLp g : Space → Space) y) := by
    exact complexifyVec.coeFn_compLp' _
  filter_upwards [h1, hg.coeFn_toLp] with y h2 h3
  rw [h2, h3]

theorem coeFn_sum3 (F : Fin 3 → L2C) :
    ((∑ k, F k : L2C) : Space → CSpace) =ᵐ[volume] fun ξ => ∑ k, (F k : Space → CSpace) ξ := by
  simp only [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (F 0 + F 1) (F 2), Lp.coeFn_add (F 0) (F 1)] with ξ h h'
  rw [h, Pi.add_apply, h', Pi.add_apply]

theorem cmul_eq (c : ℂ) : cmul c = c • ContinuousLinearMap.id ℝ CSpace := by
  ext1 z
  simp [cmul]

theorem measurable_gradSymbol (k : Fin 3) : Measurable (gradSymbol k) := by
  unfold gradSymbol
  fun_prop

theorem norm_gradSymbol_le (k : Fin 3) (ξ : Space) : ‖gradSymbol k ξ‖ ≤ 1 := by
  unfold gradSymbol
  rw [norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    norm_norm]
  exact div_le_one_of_le₀ (PiLp.norm_apply_le ξ k) (norm_nonneg _)

theorem norm_cmul_le (c : ℂ) (hc : ‖c‖ ≤ 1) : ‖cmul c‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => ?_)
  rw [cmul_eq]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq, norm_smul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem ofGrad_ae (h1 : FieldOpRealized) (f : Space → Space) :
    (ofGrad f : Space → CSpace) =ᵐ[volume]
      fun ξ => ∑ k, gradSymbol k ξ • (gradHat f k : Space → CSpace) ξ := by
  have hr : ∀ k : Fin 3, IsRealizedBy (fieldOp id (fun ξ => cmul (gradSymbol k ξ))) id
      (fun ξ => cmul (gradSymbol k ξ)) := by
    intro k
    refine h1 (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (gradSymbol k ξ)) 1 ?_ ?_
    · simp_rw [cmul_eq]
      exact (continuous_id.smul continuous_const).comp_aestronglyMeasurable
        (measurable_gradSymbol k).aestronglyMeasurable
    · exact fun ξ => norm_cmul_le _ (norm_gradSymbol_le k ξ)
  have hall := ae_all_iff.2 (fun k : Fin 3 => hr k (gradHat f k))
  unfold ofGrad
  filter_upwards [coeFn_sum3 (fun k => fieldOp id (fun ξ => cmul (gradSymbol k ξ))
    (freqTrR (complexify (toLpOrZero 2 (partialField f k))))), hall] with ξ h h'
  rw [h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show freqTrR (complexify (toLpOrZero 2 (partialField f k))) = gradHat f k from rfl, h' k]
  rfl


theorem memLp_push (R : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) (hf : IsDecayField f) (l : Fin 3) :
    MemLp (partialField (pushForward R f) l) 2 volume := by
  have he : partialField (pushForward R f) l = fun y =>
      ∑ k : Fin 3, (R.symm (unitVector l)) k • R (partialField f k (R.symm y)) :=
    funext (partialField_push R f hf.1 l)
  rw [he]
  refine memLp_finsetSum Finset.univ (fun k _ => ?_)
  have hk := (memLp_dir f hf (unitVector k)).comp_measurePreserving
    (LinearIsometryEquiv.measurePreserving R.symm)
  have hR : MemLp (fun y => R (partialField f k (R.symm y))) 2 volume :=
    (R.toContinuousLinearEquiv : Space →L[ℝ] Space).comp_memLp' hk
  exact hR.const_smul ((R.symm (unitVector l)) k)

theorem complexify_push (R : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) (hf : IsDecayField f) (l : Fin 3) :
    complexify (toLpOrZero 2 (partialField (pushForward R f) l)) =
      ∑ k : Fin 3, (R.symm (unitVector l)) k •
        rotComp R (rotCplx R) (complexify (toLpOrZero 2 (partialField f k))) := by
  refine Lp.ext ?_
  have hk : ∀ k : Fin 3, (fun y => (complexify (toLpOrZero 2 (partialField f k)) : Space → CSpace) (R.symm y))
      =ᵐ[volume] fun y => complexifyVec (partialField f k (R.symm y)) := fun k =>
    (LinearIsometryEquiv.measurePreserving R.symm).quasiMeasurePreserving.ae_eq_comp
      (ae_complexify _ (memLp_dir f hf (unitVector k)))
  have hrc : ∀ k : Fin 3, (rotComp R (rotCplx R) (complexify (toLpOrZero 2 (partialField f k))) : Space → CSpace)
      =ᵐ[volume] fun y => rotCplx R ((complexify (toLpOrZero 2 (partialField f k)) : Space → CSpace) (R.symm y)) :=
    fun k => coeFn_rotComp R (rotCplx R) _
  have hsm : ∀ k : Fin 3, (((R.symm (unitVector l)) k • rotComp R (rotCplx R)
      (complexify (toLpOrZero 2 (partialField f k))) : L2C) : Space → CSpace) =ᵐ[volume]
      (R.symm (unitVector l)) k • (rotComp R (rotCplx R)
      (complexify (toLpOrZero 2 (partialField f k))) : Space → CSpace) := fun k => Lp.coeFn_smul _ _
  filter_upwards [ae_complexify _ (memLp_push R f hf l),
    coeFn_sum3 (fun k => (R.symm (unitVector l)) k • rotComp R (rotCplx R)
      (complexify (toLpOrZero 2 (partialField f k)))),
    ae_all_iff.2 hk, ae_all_iff.2 hrc, ae_all_iff.2 hsm] with y h1 h2 h3 h4 h5
  rw [h1, h2, partialField_push R f hf.1 l y, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [h5 k, Pi.smul_apply, h4 k, h3 k, map_smul, complexifyVec_rot]

theorem freqTrR_apply (x : L2C) : freqTrR x = freqTrL2 x := rfl

theorem gradHat_push (R : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) (hf : IsDecayField f) (l : Fin 3) :
    gradHat (pushForward R f) l =
      ∑ k : Fin 3, (R.symm (unitVector l)) k • rotComp R (rotCplx R) (gradHat f k) := by
  unfold gradHat
  rw [complexify_push R f hf l, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, freqTrR_apply, freqTr_rotComp, freqTrR_apply]


theorem rotL2_ae (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) :
    IsRealizedBy (rotL2 R) (fun ξ => R.symm ξ) (fun _ => rotC R) :=
  h1 R.symm.toContinuousLinearEquiv (fun _ => rotC R) ‖rotC R‖ aestronglyMeasurable_const
    (fun _ => le_rfl)

theorem rotL2_ofGrad (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space)
    (hf : IsDecayField f) : rotL2 R (ofGrad f) = ofGrad (pushForward R f) := by
  refine Lp.ext ?_
  have hB := (LinearIsometryEquiv.measurePreserving R.symm).quasiMeasurePreserving.ae_eq_comp
    (ofGrad_ae h1 f)
  have hD : ∀ l : Fin 3, (gradHat (pushForward R f) l : Space → CSpace) =ᵐ[volume]
      fun ξ => ∑ k : Fin 3, (R.symm (unitVector l)) k •
        rotCplx R ((gradHat f k : Space → CSpace) (R.symm ξ)) := by
    intro l
    rw [gradHat_push R f hf l]
    have hsm : ∀ k : Fin 3, (((R.symm (unitVector l)) k • rotComp R (rotCplx R) (gradHat f k) : L2C) :
        Space → CSpace) =ᵐ[volume]
        (R.symm (unitVector l)) k • (rotComp R (rotCplx R) (gradHat f k) : Space → CSpace) :=
      fun k => Lp.coeFn_smul _ _
    have hrc : ∀ k : Fin 3, (rotComp R (rotCplx R) (gradHat f k) : Space → CSpace) =ᵐ[volume]
        fun ξ => rotCplx R ((gradHat f k : Space → CSpace) (R.symm ξ)) :=
      fun k => coeFn_rotComp R (rotCplx R) _
    filter_upwards [coeFn_sum3 (fun k => (R.symm (unitVector l)) k • rotComp R (rotCplx R) (gradHat f k)),
      ae_all_iff.2 hsm, ae_all_iff.2 hrc] with ξ h2 h3 h4
    rw [h2]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [h3 k, Pi.smul_apply, h4 k]
  filter_upwards [rotL2_ae h1 R (ofGrad f), hB, ofGrad_ae h1 (pushForward R f), ae_all_iff.2 hD]
    with ξ hA hB' hC hD'
  rw [hA, hC]
  simp only [Function.comp_apply] at hB'
  rw [hB']
  simp_rw [hD']
  rw [← rotCplx_apply, map_sum]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, ← symbol_rot R ξ k, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [mul_smul, Complex.coe_smul]

end Internal.EmbedRot

open Internal.EmbedRot in
theorem embedRot (h1 : FieldOpRealized) (h2 : RotationAlgebra) (h3 : EmbedMem) (_h4 : GradCompatible) :
    EmbedRot := by
  intro R f hf
  have hmem : ofGrad f ∈ Sig := h3 f hf
  have hE : embedX f = ⟨ofGrad f, hmem⟩ := by
    unfold embedX
    rw [dif_pos hmem]
  have hx : ((rotX R (embedX f) : X) : L2C) = ofGrad (pushForward R f) := by
    rw [(h2 R).1, hE]
    exact rotL2_ofGrad h1 R f hf
  have hmem' : ofGrad (pushForward R f) ∈ Sig := hx ▸ (rotX R (embedX f)).2
  have hE' : embedX (pushForward R f) = ⟨ofGrad (pushForward R f), hmem'⟩ := by
    unfold embedX
    rw [dif_pos hmem']
  rw [hE']
  exact Subtype.ext hx

end Breakdown.Freq
