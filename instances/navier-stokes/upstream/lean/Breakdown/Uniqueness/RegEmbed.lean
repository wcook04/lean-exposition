import Breakdown.Uniqueness.RegToolkit
import Breakdown.FreqTr.StatementsBilinFormula
import Breakdown.Uniqueness.RegEmbedAux

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq Breakdown.SmoothFlow.Internal.RegEmbed

private theorem toLpOrZero_ae {g : Space → CSpace} (h : MemLp g 2 volume) :
    (toLpOrZero 2 g : Space → CSpace) =ᵐ[volume] g := by
  have e : toLpOrZero 2 g = h.toLp g := by simp [toLpOrZero, h]
  rw [e]
  exact h.coeFn_toLp

private theorem memLp_partial {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hf : ∀ m, hsNormSq m f < ⊤) (k : Fin 3) : MemLp (partialField (physField f) k) 2 volume := by
  have h := hasMoments_of hm hf
  rw [partialField_physField h k]
  exact memLp_realVec_freqTrInv (hasMoments_dmul h k).integrable (memLp_dmul h hf k)

theorem isH1Field_physField {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤) : IsH1Field (physField f) := by
  have h := hasMoments_of hm hf
  refine ⟨realVec.contDiff.comp (contDiff_freqTrInv h), fun x => ?_,
    memLp_realVec_freqTrInv h.integrable (memLp_self hm hf), memLp_partial hm hf⟩
  unfold divergenceAt
  have e : ∀ i : Fin 3, (fderiv ℝ (physField f) x (unitVector i)) i = (𝓕⁻ (dmul i f) x i).re := by
    intro i
    have := congrFun (partialField_physField h i) x
    simp only [partialField] at this
    rw [this]
    rfl
  simp_rw [e]
  rw [← Complex.re_sum, sum_freqTrInv_dmul h hs x, Complex.zero_re]

private theorem conjSym_of {f : Space → CSpace} (hs : IsSolenoidalSymbol f) :
    ∀ ξ, f (-ξ) = conjVec (f ξ) := fun ξ => (hs ξ).2

private theorem complexify_partial {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤) (k : Fin 3) :
    complexify (toLpOrZero 2 (partialField (physField f) k)) =
      freqTrL2.symm (toLpOrZero 2 (dmul k f)) := by
  have h := hasMoments_of hm hf
  have hg1 := (hasMoments_dmul h k).integrable
  have hg2 := memLp_dmul h hf k
  have hP := memLp_partial hm hf k
  apply Lp.ext
  have e1 : toLpOrZero 2 (partialField (physField f) k) = hP.toLp _ := by simp [toLpOrZero, hP]
  rw [e1]
  change (ContinuousLinearMap.compLpL 2 volume complexifyVec (hP.toLp _) : Space → CSpace) =ᵐ[volume] _
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec (hP.toLp _),
    hP.coeFn_toLp, freqTrInv_ae hg1 hg2] with ξ a b c
  rw [a, b, ← c, partialField_physField h k]
  exact complexifyVec_realVec (conjVec_freqTrInv hg1 (conjSym_dmul (conjSym_of hs) k) ξ)

private theorem continuous_cmul' : Continuous cmul :=
  continuous_clm_apply.2 fun z => by
    show Continuous fun c : ℂ => c • z
    fun_prop

private theorem norm_cmul_le' (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => by
    show ‖c • z‖ ≤ ‖c‖ * ‖z‖
    rw [norm_smul]

private theorem norm_gradSymbol_le' (k : Fin 3) (ξ : Space) : ‖gradSymbol k ξ‖ ≤ 1 := by
  unfold gradSymbol
  rw [norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, norm_norm]
  exact div_le_one_of_le₀ (abs_coord_le ξ k) (norm_nonneg _)

private theorem gradOp_ae' (hR : FieldOpRealized) (k : Fin 3) (g : L2C) :
    (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) g : Space → CSpace) =ᵐ[volume]
      fun ξ => gradSymbol k ξ • g ξ :=
  hR (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (gradSymbol k ξ)) 1
    (continuous_cmul'.comp_aestronglyMeasurable (by unfold gradSymbol; fun_prop : Measurable (gradSymbol k)).aestronglyMeasurable)
    (fun ξ => (norm_cmul_le' _).trans (norm_gradSymbol_le' k ξ)) g

private theorem norm_sq_coords (ξ : Space) : ‖ξ‖ ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

private theorem scalar_identity (a0 a1 a2 n : ℝ) (hn : n ^ 2 = a0 ^ 2 + a1 ^ 2 + a2 ^ 2) :
    -(Complex.I * (a0 : ℂ) / (n : ℂ)) * (2 * (π : ℂ) * Complex.I * (a0 : ℂ)) +
      -(Complex.I * (a1 : ℂ) / (n : ℂ)) * (2 * (π : ℂ) * Complex.I * (a1 : ℂ)) +
      -(Complex.I * (a2 : ℂ) / (n : ℂ)) * (2 * (π : ℂ) * Complex.I * (a2 : ℂ)) =
      (((2 * π * n : ℝ)) : ℂ) := by
  rcases eq_or_ne n 0 with h0 | h0
  · subst h0
    simp
  · have hc : (n : ℂ) ≠ 0 := by exact_mod_cast h0
    have hnC : (n : ℂ) ^ 2 = (a0 : ℂ) ^ 2 + (a1 : ℂ) ^ 2 + (a2 : ℂ) ^ 2 := by exact_mod_cast hn
    calc _ = (2 * (π : ℂ) * ((a0 : ℂ) ^ 2 + (a1 : ℂ) ^ 2 + (a2 : ℂ) ^ 2)) * (-(Complex.I ^ 2)) / n := by
          ring
      _ = 2 * (π : ℂ) * (n : ℂ) ^ 2 / n := by rw [Complex.I_sq, neg_neg, mul_one, ← hnC]
      _ = (((2 * π * n : ℝ)) : ℂ) := by
          push_cast
          field_simp

private theorem sum_gradSymbol_dmul (f : Space → CSpace) (ξ : Space) :
    gradSymbol 0 ξ • dmul 0 f ξ + gradSymbol 1 ξ • dmul 1 f ξ + gradSymbol 2 ξ • dmul 2 f ξ =
      (((2 * π * ‖ξ‖ : ℝ)) : ℂ) • f ξ := by
  simp only [dmul, smul_smul, ← add_smul]
  congr 1
  exact scalar_identity _ _ _ _ (norm_sq_coords ξ)

private theorem ofGrad_physField_ae (hR : FieldOpRealized) {f : Space → CSpace}
    (hm : AEStronglyMeasurable f volume) (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤) :
    (ofGrad (physField f) : Space → CSpace) =ᵐ[volume] fun ξ => (((2 * π * ‖ξ‖ : ℝ)) : ℂ) • f ξ := by
  have h := hasMoments_of hm hf
  have hk : ∀ k : Fin 3, (fieldOp id (fun ξ => cmul (gradSymbol k ξ))
      (freqTrR (complexify (toLpOrZero 2 (partialField (physField f) k)))) : Space → CSpace)
        =ᵐ[volume] fun ξ => gradSymbol k ξ • dmul k f ξ := by
    intro k
    rw [complexify_partial hm hs hf k]
    have e : freqTrR (freqTrL2.symm (toLpOrZero 2 (dmul k f))) = toLpOrZero 2 (dmul k f) :=
      freqTrL2.apply_symm_apply _
    rw [e]
    filter_upwards [gradOp_ae' hR k (toLpOrZero 2 (dmul k f)), toLpOrZero_ae (memLp_dmul h hf k)]
      with ξ a b
    rw [a, b]
  unfold ofGrad
  simp only [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (_ + _ : L2C) _, Lp.coeFn_add (_ : L2C) _, hk 0, hk 1, hk 2]
    with ξ a1 a2 b0 b1 b2
  rw [a1, Pi.add_apply, a2, Pi.add_apply, b0, b1, b2]
  exact sum_gradSymbol_dmul f ξ

private theorem ae_comp_neg' {β : Type*} {u v : Space → β} (h : u =ᵐ[volume] v) :
    (fun ξ => u (-ξ)) =ᵐ[volume] fun ξ => v (-ξ) :=
  (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp h

private theorem inner_freqVec (ξ : Space) (z : CSpace) :
    inner ℂ (freqVec ξ) z = ∑ i, ((ξ i : ℝ) : ℂ) * z i := by
  simp [freqVec, complexifyVec, PiLp.inner_apply, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem norm_freqVec' (ξ : Space) : ‖freqVec ξ‖ = ‖ξ‖ := by
  simp [EuclideanSpace.norm_eq, freqVec, complexifyVec]

private theorem norm_longitudinal_le' (ξ : Space) : ‖longitudinal ξ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  show ‖((‖ξ‖ ^ 2)⁻¹ : ℝ) • (inner ℂ (freqVec ξ) z • freqVec ξ)‖ ≤ 1 * ‖z‖
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_freqVec', one_mul]
  rcases eq_or_ne ‖ξ‖ 0 with h | h
  · simp [h]
  · have hi : ‖inner ℂ (freqVec ξ) z‖ ≤ ‖ξ‖ * ‖z‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) (freqVec ξ) z
      rwa [norm_freqVec'] at this
    have hp : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    calc (‖ξ‖ ^ 2)⁻¹ * (‖inner ℂ (freqVec ξ) z‖ * ‖ξ‖) ≤ (‖ξ‖ ^ 2)⁻¹ * ((‖ξ‖ * ‖z‖) * ‖ξ‖) := by
          gcongr
      _ = ‖z‖ := by field_simp

private theorem aesm_longitudinal' : AEStronglyMeasurable longitudinal volume := by
  have hL : Continuous fun ξ : Space =>
      ((ContinuousLinearMap.smulRight (innerSL ℂ (freqVec ξ)) (freqVec ξ)).restrictScalars ℝ :
        CSpace →L[ℝ] CSpace) :=
    continuous_clm_apply.2 fun z => by
      show Continuous fun ξ : Space => inner ℂ (freqVec ξ) z • freqVec ξ
      have hv : Continuous freqVec := complexifyVec.continuous
      fun_prop
  have hm : Measurable fun ξ : Space => ((‖ξ‖ ^ 2)⁻¹ : ℝ) := by fun_prop
  exact hm.aestronglyMeasurable.smul hL.aestronglyMeasurable

private theorem ofGrad_physField_mem (hR : FieldOpRealized) {f : Space → CSpace}
    (hm : AEStronglyMeasurable f volume) (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤) :
    ofGrad (physField f) ∈ Sig := by
  have hae := ofGrad_physField_ae hR hm hs hf
  simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    _root_.sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
  constructor
  · apply Lp.ext
    filter_upwards [hR (ContinuousLinearEquiv.neg ℝ) (fun _ => conjVec) ‖conjVec‖
      aestronglyMeasurable_const (fun _ => le_rfl) (ofGrad (physField f)), ae_comp_neg' hae, hae]
      with ξ a b c
    change (reflConj (ofGrad (physField f)) : Space → CSpace) ξ = _ at a
    rw [a]
    change conjVec ((ofGrad (physField f) : Space → CSpace) (-ξ)) = _
    rw [b, c]
    simp only [norm_neg, conjVec_smul, (hs ξ).2, conjVec_conjVec,
      Complex.star_def, Complex.conj_ofReal]
  · apply Lp.ext
    have hL := hR (ContinuousLinearEquiv.refl ℝ Space) longitudinal 1 ?_ ?_ (ofGrad (physField f))
    · filter_upwards [hL, hae, Lp.coeFn_zero CSpace 2 volume] with ξ a b c
      change (fieldOp id longitudinal (ofGrad (physField f)) : Space → CSpace) ξ = _ at a
      rw [a, c]
      change longitudinal ξ ((ofGrad (physField f) : Space → CSpace) ξ) = 0
      rw [b]
      simp only [longitudinal, FunLike.coe_smul, Pi.smul_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
        inner_smul_right, inner_freqVec, (hs ξ).1, mul_zero, zero_smul, smul_zero]
    · exact aesm_longitudinal'
    · exact norm_longitudinal_le'

theorem coe_embedX_physField (hR : FieldOpRealized) {f : Space → CSpace}
    (hm : AEStronglyMeasurable f volume) (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤) :
    ((embedX (physField f) : X) : Space → CSpace) =ᵐ[volume]
      fun ξ => (((2 * π * ‖ξ‖ : ℝ)) : ℂ) • f ξ := by
  have e : ((embedX (physField f) : X) : L2C) = ofGrad (physField f) := by
    simp [embedX, ofGrad_physField_mem hR hm hs hf]
  rw [e]
  exact ofGrad_physField_ae hR hm hs hf

theorem norm_embedX_physField_sq (hR : FieldOpRealized) {f : Space → CSpace}
    (hm : AEStronglyMeasurable f volume) (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤) :
    ‖embedX (physField f)‖ ^ 2 = 4 * π ^ 2 * (homNormSq 1 f).toReal := by
  have e : ((embedX (physField f) : X) : L2C) = ofGrad (physField f) := by
    simp [embedX, ofGrad_physField_mem hR hm hs hf]
  have hn : ‖embedX (physField f)‖ = ‖ofGrad (physField f)‖ := by rw [← e]; rfl
  rw [hn, Lp.norm_def, eLpNorm_congr_ae (ofGrad_physField_ae hR hm hs hf),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hpt : ∀ ξ : Space, ‖(((2 * π * ‖ξ‖ : ℝ)) : ℂ) • f ξ‖ₑ ^ 2 =
      ENNReal.ofReal (4 * π ^ 2) * (ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖f ξ‖ₑ ^ 2) := by
    intro ξ
    rw [enorm_smul, mul_pow, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), ← ENNReal.ofReal_pow (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  rfl

end Breakdown.SmoothFlow
