import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.Dilation

theorem fieldOp_isRealizedBy_of_exists {A : Space → Space} {F : Space → CSpace →L[ℝ] CSpace}
    (h : ∃ T, IsRealizedBy T A F) : IsRealizedBy (fieldOp A F) A F := by
  unfold fieldOp
  rw [dif_pos h]
  exact h.choose_spec

theorem fieldOp_eq_zero_of_not {A : Space → Space} {F : Space → CSpace →L[ℝ] CSpace}
    (h : ¬ ∃ T, IsRealizedBy T A F) : fieldOp A F = 0 := by
  unfold fieldOp
  rw [dif_neg h]

theorem dilL2_ae (h1 : FieldOpRealized) {μ : ℝ} (hμ : 0 < μ) (f : L2C) :
    (dilL2 μ f : Space → CSpace) =ᵐ[volume]
      fun ξ => (Real.sqrt μ)⁻¹ • (f : Space → CSpace) ((Real.sqrt μ)⁻¹ • ξ) := by
  have hc : (Real.sqrt μ)⁻¹ ≠ 0 := (inv_pos.2 (Real.sqrt_pos.2 hμ)).ne'
  have := h1 (LinearEquiv.smulOfNeZero ℝ Space _ hc).toContinuousLinearEquiv
    (fun _ => (Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ CSpace)
    ‖(Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ CSpace‖
    aestronglyMeasurable_const (fun _ => le_rfl) f
  have e : fieldOp (⇑(LinearEquiv.smulOfNeZero ℝ Space _ hc).toContinuousLinearEquiv)
      (fun _ => (Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ CSpace) = dilL2 μ := rfl
  rw [e] at this
  exact this.mono fun ξ hξ => by rw [hξ]; rfl

theorem heatFactor_le_one (t : ℝ) (ξ : Space) : |heatFactor t ξ| ≤ 1 := by
  unfold heatFactor
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  positivity

theorem heatL2_ae (h1 : FieldOpRealized) (t : ℝ) (f : L2C) :
    (heatL2 t f : Space → CSpace) =ᵐ[volume] fun ξ => heatFactor t ξ • (f : Space → CSpace) ξ := by
  have hcont : Continuous (fun ξ : Space => heatFactor t ξ) := by
    unfold heatFactor
    fun_prop
  have hF : Continuous (fun ξ : Space => heatFactor t ξ • ContinuousLinearMap.id ℝ CSpace) :=
    hcont.smul continuous_const
  have hb : ∀ ξ, ‖heatFactor t ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 := fun ξ => by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]
    calc |heatFactor t ξ| * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 * 1 :=
          mul_le_mul (heatFactor_le_one t ξ) ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have := h1 (ContinuousLinearEquiv.refl ℝ Space) _ 1 hF.aestronglyMeasurable hb f
  have e : fieldOp (⇑(ContinuousLinearEquiv.refl ℝ Space))
      (fun ξ => heatFactor t ξ • ContinuousLinearMap.id ℝ CSpace) = heatL2 t := rfl
  rw [e] at this
  exact this.mono fun ξ hξ => by rw [hξ]; rfl

theorem longitudinal_smul {c : ℝ} (hc : c ≠ 0) (ξ : Space) (v : CSpace) :
    longitudinal (c • ξ) v = longitudinal ξ v := by
  simp only [longitudinal, freqVec, smul_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, smul_smul, RCLike.conj_ofReal]
  congr 1
  push_cast
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  field_simp
  exact mul_div_mul_left _ _ hc'

theorem dilL2_mem (h1 : FieldOpRealized) {μ : ℝ} (hμ : 0 < μ) {f : L2C} (hf : f ∈ Sig) :
    dilL2 μ f ∈ Sig := by
  have hc : (Real.sqrt μ)⁻¹ ≠ 0 := (inv_pos.2 (Real.sqrt_pos.2 hμ)).ne'
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure Space) hc
  have hn : Measure.QuasiMeasurePreserving (fun ξ : Space => -ξ) volume volume :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving
  have hD := dilL2_ae h1 hμ f
  simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at hf ⊢
  obtain ⟨hf1, hf2⟩ := hf
  constructor
  · by_cases hR : ∃ T, IsRealizedBy T (fun ξ => -ξ) (fun _ => conjVec)
    · have hRr := fieldOp_isRealizedBy_of_exists hR
      have e1 : (fun η => conjVec ((f : Space → CSpace) (-η))) =ᵐ[volume] (f : Space → CSpace) := by
        have h := hRr f
        change (reflConj f : Space → CSpace) =ᵐ[volume] _ at h
        rw [hf1] at h
        exact h.symm
      apply Lp.ext
      have hD' := hRr (dilL2 μ f)
      change (reflConj (dilL2 μ f) : Space → CSpace) =ᵐ[volume] _ at hD'
      filter_upwards [hD', hn.ae_eq_comp hD, hq.ae_eq_comp e1, hD] with ξ a b c d
      simp only [Function.comp_apply] at b c
      rw [a, b, d, ← c, map_smul, smul_neg]
    · have h0 : reflConj = 0 := fieldOp_eq_zero_of_not hR
      rw [h0, zero_apply] at hf1
      rw [← hf1, map_zero, h0, zero_apply]
  · by_cases hL : ∃ T, IsRealizedBy T id longitudinal
    · have hLr := fieldOp_isRealizedBy_of_exists hL
      have e2 : (fun η => longitudinal η ((f : Space → CSpace) η)) =ᵐ[volume] (0 : Space → CSpace) := by
        have h := hLr f
        rw [hf2] at h
        exact h.symm.trans (Lp.coeFn_zero _ _ _)
      apply Lp.ext
      filter_upwards [hLr (dilL2 μ f), hq.ae_eq_comp e2, hD, Lp.coeFn_zero CSpace 2 (volume : Measure Space)]
        with ξ a b d z
      simp only [Function.comp_apply, Pi.zero_apply] at b
      rw [a, z, id, d, map_smul, ← longitudinal_smul hc ξ, b, smul_zero, Pi.zero_apply]
    · rw [fieldOp_eq_zero_of_not hL, zero_apply]

theorem dilX_coe (h1 : FieldOpRealized) {μ : ℝ} (hμ : 0 < μ) (x : X) :
    (dilX μ x : L2C) = dilL2 μ x := by
  have hmem : ∀ y ∈ Sig, dilL2 μ y ∈ Sig := fun y hy => dilL2_mem h1 hμ hy
  simp only [dilX, if_pos hμ, restrictX, dif_pos hmem]
  rfl

theorem norm_dilL2 (h1 : FieldOpRealized) {μ : ℝ} (hμ : 0 < μ) (f : L2C) :
    ‖dilL2 μ f‖ = μ ^ (1 / 4 : ℝ) * ‖f‖ := by
  have hcpos : 0 < (Real.sqrt μ)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hμ)
  have hD := dilL2_ae h1 hμ f
  have key' : ‖dilL2 μ f‖ ^ 2 = Real.sqrt μ * ‖f‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (dilL2 μ f), ← inner_self_eq_norm_sq (𝕜 := ℂ) f,
      L2.inner_def, L2.inner_def, integral_congr_ae (hD.mono fun ξ hξ => congrArg (fun v => inner ℂ v v) hξ)]
    simp_rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (Real.sqrt μ)⁻¹, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal, ← mul_assoc]
    rw [integral_const_mul]
    have hsub := Measure.integral_comp_smul (volume : Measure Space)
      (fun a => inner ℂ ((f : Space → CSpace) a) ((f : Space → CSpace) a)) (Real.sqrt μ)⁻¹
    rw [hsub, finrank_euclideanSpace, Fintype.card_fin, abs_of_pos (inv_pos.2 (pow_pos hcpos 3))]
    generalize (∫ a, inner ℂ ((f : Space → CSpace) a) ((f : Space → CSpace) a)) = z
    have hs : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 hμ).ne'
    have e : (Real.sqrt μ)⁻¹ * (Real.sqrt μ)⁻¹ * ((Real.sqrt μ)⁻¹ ^ 3)⁻¹ = Real.sqrt μ := by
      field_simp
    simp only [RCLike.re_to_complex, Complex.real_smul, ← mul_assoc, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    rw [e]
  rw [← Real.sqrt_sq (norm_nonneg (dilL2 μ f)), key', Real.sqrt_mul (Real.sqrt_nonneg μ),
    Real.sqrt_sq (norm_nonneg f)]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hμ.le]
  norm_num

theorem heatFactor_dil {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (ξ : Space) :
    heatFactor (μ * t) ((Real.sqrt μ)⁻¹ • ξ) = heatFactor t ξ := by
  unfold heatFactor
  rw [max_eq_left (mul_nonneg hμ.le ht), max_eq_left ht, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hμ)), mul_pow, inv_pow, Real.sq_sqrt hμ.le]
  congr 1
  field_simp

end Internal.Dilation

open Internal.Dilation in
theorem dilationAlgebra (h1 : FieldOpRealized) (h2 : HeatSemigroup) : DilationAlgebra := by
  refine ⟨?_, ?_, ?_, ?_, fun μ hμ x => dilX_coe h1 hμ x⟩
  · intro μ hμ x
    rw [Submodule.coe_norm, dilX_coe h1 hμ, norm_dilL2 h1 hμ, ← Submodule.coe_norm]
  · ext x : 1
    apply Subtype.ext
    rw [dilX_coe h1 one_pos, ContinuousLinearMap.id_apply]
    apply Lp.ext
    filter_upwards [dilL2_ae h1 one_pos ((x : X) : L2C)] with ξ a
    rw [a]
    simp
  · intro μ ν hμ hν
    ext x : 1
    apply Subtype.ext
    have hc : (Real.sqrt μ)⁻¹ ≠ 0 := (inv_pos.2 (Real.sqrt_pos.2 hμ)).ne'
    have hq := Measure.quasiMeasurePreserving_smul (volume : Measure Space) hc
    rw [ContinuousLinearMap.comp_apply, dilX_coe h1 (mul_pos hμ hν), dilX_coe h1 hμ, dilX_coe h1 hν]
    apply Lp.ext
    filter_upwards [dilL2_ae h1 (mul_pos hμ hν) ((x : X) : L2C), dilL2_ae h1 hμ (dilL2 ν x),
      hq.ae_eq_comp (dilL2_ae h1 hν ((x : X) : L2C))] with ξ a b d
    simp only [Function.comp_apply] at d
    rw [a, b, d, Real.sqrt_mul hμ.le, mul_inv]
    simp only [smul_smul]
    rw [mul_comm (Real.sqrt ν)⁻¹ (Real.sqrt μ)⁻¹]
  · intro μ t hμ ht
    ext x : 1
    apply Subtype.ext
    have hc : (Real.sqrt μ)⁻¹ ≠ 0 := (inv_pos.2 (Real.sqrt_pos.2 hμ)).ne'
    have hq := Measure.quasiMeasurePreserving_smul (volume : Measure Space) hc
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, dilX_coe h1 hμ,
      h2.2.2.2.2.2 (μ * t) x, h2.2.2.2.2.2 t, dilX_coe h1 hμ]
    apply Lp.ext
    filter_upwards [dilL2_ae h1 hμ (heatL2 (μ * t) ((x : X) : L2C)),
      hq.ae_eq_comp (heatL2_ae h1 (μ * t) ((x : X) : L2C)),
      heatL2_ae h1 t (dilL2 μ ((x : X) : L2C)), dilL2_ae h1 hμ ((x : X) : L2C)] with ξ a b d e
    simp only [Function.comp_apply] at b
    rw [a, b, d, e, heatFactor_dil hμ ht, smul_comm]

end Breakdown.Freq
