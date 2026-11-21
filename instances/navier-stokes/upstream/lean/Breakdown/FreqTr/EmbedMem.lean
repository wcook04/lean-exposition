import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.Freq

namespace Internal.EmbedMem

theorem norm_cmul_le (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => by
    show ‖c • z‖ ≤ ‖c‖ * ‖z‖
    rw [norm_smul]

theorem continuous_cmul : Continuous cmul :=
  continuous_clm_apply.2 fun z => by
    show Continuous fun c : ℂ => c • z
    fun_prop

theorem measurable_gradSymbol (k : Fin 3) : Measurable (gradSymbol k) := by
  unfold gradSymbol
  fun_prop

theorem norm_gradSymbol_le (k : Fin 3) (ξ : Space) : ‖gradSymbol k ξ‖ ≤ 1 := by
  have hk : |ξ k| ≤ ‖ξ‖ := by
    have := PiLp.norm_apply_le ξ k
    simpa [Real.norm_eq_abs] using this
  unfold gradSymbol
  rw [norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, norm_norm]
  exact div_le_one_of_le₀ hk (norm_nonneg _)

theorem star_gradSymbol_neg (k : Fin 3) (ξ : Space) : star (gradSymbol k (-ξ)) = gradSymbol k ξ := by
  simp [gradSymbol, Complex.conj_ofReal, Complex.conj_I]

theorem gradOp_ae (h1 : FieldOpRealized) (k : Fin 3) (g : L2C) :
    (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) g : Space → CSpace) =ᵐ[volume]
      fun ξ => gradSymbol k ξ • g ξ :=
  h1 (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (gradSymbol k ξ)) 1
    (continuous_cmul.comp_aestronglyMeasurable (measurable_gradSymbol k).aestronglyMeasurable)
    (fun ξ => (norm_cmul_le _).trans (norm_gradSymbol_le k ξ)) g

theorem reflConj_ae (h1 : FieldOpRealized) (g : L2C) :
    (reflConj g : Space → CSpace) =ᵐ[volume] fun ξ => conjVec (g (-ξ)) :=
  h1 (ContinuousLinearEquiv.neg ℝ) (fun _ => conjVec) ‖conjVec‖ aestronglyMeasurable_const
    (fun _ => le_rfl) g

theorem ae_comp_neg {β : Type*} {u v : Space → β} (h : u =ᵐ[volume] v) :
    (fun ξ => u (-ξ)) =ᵐ[volume] fun ξ => v (-ξ) :=
  (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp h

theorem norm_freqVec (ξ : Space) : ‖freqVec ξ‖ = ‖ξ‖ := by
  simp [EuclideanSpace.norm_eq, freqVec, complexifyVec]

theorem norm_longitudinal_le (ξ : Space) : ‖longitudinal ξ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    show ‖((‖ξ‖ ^ 2)⁻¹ : ℝ) • (inner ℂ (freqVec ξ) z • freqVec ξ)‖ ≤ 1 * ‖z‖
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (‖ξ‖ ^ 2)⁻¹ * (‖inner ℂ (freqVec ξ) z‖ * ‖freqVec ξ‖)
        ≤ (‖ξ‖ ^ 2)⁻¹ * (‖freqVec ξ‖ * ‖z‖ * ‖freqVec ξ‖) := by
          gcongr
          exact norm_inner_le_norm _ _
      _ = ((‖ξ‖ ^ 2)⁻¹ * ‖ξ‖ ^ 2) * ‖z‖ := by rw [norm_freqVec]; ring
      _ ≤ 1 * ‖z‖ := by
          gcongr
          rcases eq_or_ne ‖ξ‖ 0 with h | h
          · simp [h]
          · rw [inv_mul_cancel₀ (pow_ne_zero _ h)]

theorem aesm_longitudinal : AEStronglyMeasurable longitudinal volume := by
  have hL : Continuous fun ξ : Space =>
      ((ContinuousLinearMap.smulRight (innerSL ℂ (freqVec ξ)) (freqVec ξ)).restrictScalars ℝ :
        CSpace →L[ℝ] CSpace) :=
    continuous_clm_apply.2 fun z => by
      show Continuous fun ξ : Space => inner ℂ (freqVec ξ) z • freqVec ξ
      have hv : Continuous freqVec := complexifyVec.continuous
      fun_prop
  have hm : Measurable fun ξ : Space => ((‖ξ‖ ^ 2)⁻¹ : ℝ) := by fun_prop
  exact hm.aestronglyMeasurable.smul hL.aestronglyMeasurable

theorem longitudinal_ae (h1 : FieldOpRealized) (g : L2C) :
    (fieldOp id longitudinal g : Space → CSpace) =ᵐ[volume] fun ξ => longitudinal ξ (g ξ) :=
  h1 (ContinuousLinearEquiv.refl ℝ Space) longitudinal 1 aesm_longitudinal norm_longitudinal_le g

end Internal.EmbedMem

namespace Internal.EmbedMem

open SchwartzMap

theorem compLpL_toLp (A : CSpace →L[ℂ] CSpace) (ψ : 𝓢(Space, CSpace)) :
    ContinuousLinearMap.compLpL 2 volume A (ψ.toLp 2) = (postcompCLM (𝕜 := ℂ) A ψ).toLp 2 := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) A (ψ.toLp 2),
    ψ.coeFn_toLp 2 volume, (postcompCLM (𝕜 := ℂ) A ψ).coeFn_toLp 2 volume] with x hx1 hx2 hx3
  rw [hx1, hx3, hx2, postcompCLM_apply]

theorem freqTr_postcomp (A : CSpace →L[ℂ] CSpace) (ψ : 𝓢(Space, CSpace)) :
    𝓕 (postcompCLM (𝕜 := ℂ) A ψ) = postcompCLM (𝕜 := ℂ) A (𝓕 ψ) := by
  ext ξ : 1
  rw [postcompCLM_apply, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq,
    Real.fourier_eq]
  have hi : Integrable (fun v : Space => 𝐞 (-inner ℝ v ξ) • ψ v) volume :=
    (Real.fourierIntegral_convergent_iff ξ).2 ψ.integrable
  rw [← A.integral_comp_comm hi]
  congr 1
  funext v
  rw [postcompCLM_apply, Circle.smul_def, Circle.smul_def, A.map_smul]

theorem freqTrL2_compLpL (A : CSpace →L[ℂ] CSpace) (u : L2C) :
    freqTrL2 (ContinuousLinearMap.compLpL 2 volume A u) =
      ContinuousLinearMap.compLpL 2 volume A (freqTrL2 u) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := Space) (F := CSpace) (p := 2) (μ := volume)
    ENNReal.ofNat_ne_top
  have heq := hd.equalizer (g := fun u => freqTrL2 (ContinuousLinearMap.compLpL 2 volume A u))
    (h := fun u => ContinuousLinearMap.compLpL 2 volume A (freqTrL2 u))
    (freqTrL2.continuous.comp (ContinuousLinearMap.compLpL 2 volume A).continuous)
    ((ContinuousLinearMap.compLpL 2 volume A).continuous.comp freqTrL2.continuous)
    (funext fun ψ => by
      show freqTrL2 (ContinuousLinearMap.compLpL 2 volume A (ψ.toLp 2)) =
        ContinuousLinearMap.compLpL 2 volume A (freqTrL2 (ψ.toLp 2))
      have h2 : freqTrL2 (ψ.toLp 2) = (𝓕 ψ).toLp 2 := SchwartzMap.toLp_fourier_eq ψ
      have h3 : freqTrL2 ((postcompCLM (𝕜 := ℂ) A ψ).toLp 2) =
          (𝓕 (postcompCLM (𝕜 := ℂ) A ψ)).toLp 2 := SchwartzMap.toLp_fourier_eq _
      rw [compLpL_toLp, h3, h2, compLpL_toLp, freqTr_postcomp])
  exact congrFun heq u

theorem complexify_compLpL (B : Space →L[ℝ] Space) (A : CSpace →L[ℂ] CSpace)
    (hAB : ∀ z, complexifyVec (B z) = A (complexifyVec z)) (g : L2R) :
    complexify (ContinuousLinearMap.compLpL 2 volume B g) =
      ContinuousLinearMap.compLpL 2 volume A (complexify g) := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec
      (ContinuousLinearMap.compLpL 2 volume B g),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) B g,
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) A
      (ContinuousLinearMap.compLpL 2 volume complexifyVec g),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec g] with x h1 h2 h3 h4
  rw [complexify, h1, h2, h3, h4, hAB]

theorem memLp_partialField {f : Space → Space} (hf : IsDecayField f) (k : Fin 3) :
    MemLp (partialField f k) 2 volume := by
  obtain ⟨hs, -, C, hC⟩ := hf
  have hcont : Continuous (partialField f k) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  have hint : Integrable (fun y : Space => C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ))) volume :=
    (integrable_one_add_norm (by simp [finrank_euclideanSpace]; norm_num)).const_mul _
  refine hint.mono' (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have hb : ‖partialField f k y‖ ≤ C / (1 + ‖y‖) ^ 2 :=
    calc ‖partialField f k y‖ ≤ ‖fderiv ℝ f y‖ * ‖unitVector k‖ := (fderiv ℝ f y).le_opNorm _
      _ = ‖fderiv ℝ f y‖ := by simp [unitVector]
      _ ≤ C / (1 + ‖y‖) ^ 2 := (hC y).2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖partialField f k y‖ ^ 2 ≤ (C / (1 + ‖y‖) ^ 2) ^ 2 := by gcongr
    _ = C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
      rw [Real.rpow_neg hpos.le, div_pow, ← pow_mul, div_eq_mul_inv]
      norm_cast

def coordReal (i : Fin 3) : Space →L[ℝ] Space :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).smulRight (EuclideanSpace.single 0 1)

def coordCplx (i : Fin 3) : CSpace →L[ℂ] CSpace :=
  (EuclideanSpace.proj i : CSpace →L[ℂ] ℂ).smulRight (EuclideanSpace.single 0 1)

theorem coordReal_apply (i : Fin 3) (z : Space) : coordReal i z = z i • EuclideanSpace.single 0 1 := rfl

theorem coordCplx_apply (i : Fin 3) (z : CSpace) : coordCplx i z = z i • EuclideanSpace.single 0 1 := rfl

theorem complexifyVec_coord (i : Fin 3) (z : Space) :
    complexifyVec (coordReal i z) = coordCplx i (complexifyVec z) := by
  ext j
  simp [coordReal_apply, coordCplx_apply, complexifyVec]
  split_ifs <;> simp

theorem div_ae {f : Space → Space} (hf : IsDecayField f) :
    ∀ᵐ ξ ∂volume, ∑ i : Fin 3, (gradHat f i : Space → CSpace) ξ i = 0 := by
  have hm := memLp_partialField hf
  have hz : ∑ i : Fin 3, ContinuousLinearMap.compLpL 2 volume (coordReal i)
      (toLpOrZero 2 (partialField f i)) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    have hc : ∀ i : Fin 3, toLpOrZero 2 (partialField f i) = (hm i).toLp _ := fun i => by
      simp [toLpOrZero, hm i]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 => ContinuousLinearMap.compLpL 2
        volume (coordReal i) (toLpOrZero 2 (partialField f i))),
      ae_all_iff.2 fun i : Fin 3 => ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
        (coordReal i) (toLpOrZero 2 (partialField f i)),
      ae_all_iff.2 fun i : Fin 3 => (hm i).coeFn_toLp] with x hs hi ht
    rw [hs, Finset.sum_apply]
    simp only [hi]
    simp only [hc, ht, coordReal_apply]
    rw [← Finset.sum_smul]
    have hd : ∑ i : Fin 3, partialField f i x i = 0 := hf.2.1 x
    rw [hd, zero_smul]
    rfl
  have hF : ∑ i : Fin 3, ContinuousLinearMap.compLpL 2 volume (coordCplx i) (gradHat f i) = 0 := by
    have := congrArg (fun g => freqTrR (complexify g)) hz
    simp only [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [complexify_compLpL _ (coordCplx i) (complexifyVec_coord i)]
    exact (freqTrL2_compLpL (coordCplx i) _).symm
  have hae : (((∑ i : Fin 3, ContinuousLinearMap.compLpL 2 volume (coordCplx i) (gradHat f i) :
      L2C)) : Space → CSpace) =ᵐ[volume] 0 := by
    rw [hF]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [hae, Lp.coeFn_finsetSum Finset.univ (fun i : Fin 3 =>
      ContinuousLinearMap.compLpL 2 volume (coordCplx i) (gradHat f i)),
    ae_all_iff.2 fun i : Fin 3 => ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume)
      (coordCplx i) (gradHat f i)] with ξ h0 hs hi
  rw [hs, Finset.sum_apply] at h0
  simp only [hi, coordCplx_apply] at h0
  have := congrArg (fun w : CSpace => w 0) h0
  simpa [← Finset.sum_smul] using this

end Internal.EmbedMem

namespace Internal.EmbedMem

theorem conjSym_grad (h1 : FieldOpRealized) (k : Fin 3) (g : L2C) (hg : reflConj g = g) :
    reflConj (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) g) =
      fieldOp id (fun ξ => cmul (gradSymbol k ξ)) g := by
  have hG : (g : Space → CSpace) =ᵐ[volume] fun ξ => conjVec (g (-ξ)) := by
    have := reflConj_ae h1 g
    rw [hg] at this
    exact this
  apply Lp.ext
  filter_upwards [reflConj_ae h1 (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) g),
    ae_comp_neg (gradOp_ae h1 k g), gradOp_ae h1 k g, hG] with ξ ha hb hc hd
  rw [ha, hb, hc, hd]
  ext i
  simp [conjVec, ← star_gradSymbol_neg k ξ]

theorem ofGrad_ae (h1 : FieldOpRealized) (f : Space → Space) :
    (ofGrad f : Space → CSpace) =ᵐ[volume]
      fun ξ => ∑ k : Fin 3, gradSymbol k ξ • (gradHat f k : Space → CSpace) ξ := by
  have he : ofGrad f = ∑ k : Fin 3, fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (gradHat f k) := rfl
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun k : Fin 3 => fieldOp id (fun ξ => cmul (gradSymbol k ξ)) (gradHat f k)),
    ae_all_iff.2 fun k : Fin 3 => gradOp_ae h1 k (gradHat f k)] with ξ hs hk
  rw [he, hs, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => hk k

theorem inner_freqVec (ξ : Space) (w : CSpace) :
    inner ℂ (freqVec ξ) w = ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * w i := by
  simp [PiLp.inner_apply, freqVec, complexifyVec, mul_comm]

theorem long_ofGrad (h1 : FieldOpRealized) (h2 : GradCompatible) {f : Space → Space}
    (hf : IsDecayField f) : fieldOp id longitudinal (ofGrad f) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hc : ∀ᵐ ξ ∂volume, ∀ j k : Fin 3,
      (ξ k : ℝ) • (gradHat f j : Space → CSpace) ξ = (ξ j : ℝ) • (gradHat f k : Space → CSpace) ξ :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun k => h2 f hf j k
  filter_upwards [longitudinal_ae h1 (ofGrad f), ofGrad_ae h1 f, hc, div_ae hf] with ξ hl ho hcξ hd
  rw [hl, ho, Pi.zero_apply]
  have hcomp : ∀ k : Fin 3, ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * (gradHat f k : Space → CSpace) ξ i = 0 := by
    intro k
    have hik : ∀ i : Fin 3, ((ξ i : ℝ) : ℂ) * (gradHat f k : Space → CSpace) ξ i =
        ((ξ k : ℝ) : ℂ) * (gradHat f i : Space → CSpace) ξ i := by
      intro i
      have := congrArg (fun w : CSpace => w i) (hcξ i k)
      simpa [Complex.real_smul] using this.symm
    rw [Finset.sum_congr rfl fun i _ => hik i, ← Finset.mul_sum, hd, mul_zero]
  have hinner : inner ℂ (freqVec ξ) (∑ k : Fin 3, gradSymbol k ξ • (gradHat f k : Space → CSpace) ξ)
      = 0 := by
    rw [inner_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [inner_smul_right, inner_freqVec, hcomp k, mul_zero]
  show ((‖ξ‖ ^ 2)⁻¹ : ℝ) • (inner ℂ (freqVec ξ)
    (∑ k : Fin 3, gradSymbol k ξ • (gradHat f k : Space → CSpace) ξ) • freqVec ξ) = 0
  rw [hinner, zero_smul, smul_zero]

end Internal.EmbedMem

theorem embedMem (h1 : FieldOpRealized) (h2 : GradCompatible) (h3 : FreqTrConjSym) :
    EmbedMem := by
  intro f hf
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker]
    show reflConj (ofGrad f) - ofGrad f = 0
    rw [sub_eq_zero, ofGrad, map_sum]
    exact Finset.sum_congr rfl fun k _ => Internal.EmbedMem.conjSym_grad h1 k _ (h3 _)
  · rw [LinearMap.mem_ker]
    exact Internal.EmbedMem.long_ofGrad h1 h2 hf

end Breakdown.Freq
