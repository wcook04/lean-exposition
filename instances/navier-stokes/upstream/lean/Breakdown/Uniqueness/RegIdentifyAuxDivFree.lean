import Breakdown.Uniqueness.RegToolkit
import Breakdown.FreqTr.FreqTrL1
import Breakdown.Uniqueness.RegEmbedAux

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace Internal.RegIdentifyDivFree

open Breakdown.SmoothFlow.Internal.RegEmbed

theorem toLpOrZero_ae_eq {A : Space → CSpace} (h : MemLp A 2 volume) :
    (toLpOrZero 2 A : Space → CSpace) =ᵐ[volume] A := by
  rw [toLpOrZero, dif_pos h]
  exact h.coeFn_toLp

theorem toLpOrZero_ae_eq_real {f : Space → Space} (h : MemLp f 2 volume) :
    (toLpOrZero 2 f : Space → Space) =ᵐ[volume] f := by
  rw [toLpOrZero, dif_pos h]
  exact h.coeFn_toLp

theorem longitudinal_eq (ξ : Space) (z : CSpace) :
    longitudinal ξ z = ((‖ξ‖ ^ 2)⁻¹ : ℝ) • (inner ℂ (freqVec ξ) z • freqVec ξ) := rfl

theorem inner_freqVec_eq (ξ : Space) (z : CSpace) :
    inner ℂ (freqVec ξ) z = ∑ i, ((ξ i : ℝ) : ℂ) * z i := by
  simp [freqVec, complexifyVec, PiLp.inner_apply, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem norm_freqVec_eq (ξ : Space) : ‖freqVec ξ‖ = ‖ξ‖ := by
  simp [EuclideanSpace.norm_eq, freqVec, complexifyVec]

theorem freqVec_zero : freqVec 0 = 0 := map_zero complexifyVec

theorem divFreeC_eq_sub (ξ : Space) (z : CSpace) : divFreeC ξ z = z - longitudinal ξ z := by
  rw [divFreeC, longitudinal_eq, inner_freqVec_eq, mul_smul, Complex.coe_smul]

theorem norm_longitudinal_le_one (ξ : Space) : ‖longitudinal ξ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [longitudinal_eq, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    norm_freqVec_eq, one_mul]
  rcases eq_or_ne ‖ξ‖ 0 with h | h
  · simp [h]
  · have hi : ‖inner ℂ (freqVec ξ) z‖ ≤ ‖ξ‖ * ‖z‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) (freqVec ξ) z
      rwa [norm_freqVec_eq] at this
    have hp : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    calc (‖ξ‖ ^ 2)⁻¹ * (‖inner ℂ (freqVec ξ) z‖ * ‖ξ‖) ≤ (‖ξ‖ ^ 2)⁻¹ * ((‖ξ‖ * ‖z‖) * ‖ξ‖) := by
          gcongr
      _ = ‖z‖ := by field_simp

theorem aestronglyMeasurable_longitudinal : AEStronglyMeasurable longitudinal volume := by
  have hL : Continuous fun ξ : Space =>
      ((ContinuousLinearMap.smulRight (innerSL ℂ (freqVec ξ)) (freqVec ξ)).restrictScalars ℝ :
        CSpace →L[ℝ] CSpace) :=
    continuous_clm_apply.2 fun z => by
      show Continuous fun ξ : Space => inner ℂ (freqVec ξ) z • freqVec ξ
      have hv : Continuous freqVec := complexifyVec.continuous
      fun_prop
  have hm : Measurable fun ξ : Space => ((‖ξ‖ ^ 2)⁻¹ : ℝ) := by fun_prop
  exact hm.aestronglyMeasurable.smul hL.aestronglyMeasurable

theorem continuous_phi (τ : ℝ) : Continuous (phiFactor τ) := by
  unfold phiFactor
  fun_prop

theorem phiFactor_neg (τ : ℝ) (ξ : Space) : phiFactor τ (-ξ) = phiFactor τ ξ := by
  simp [phiFactor]

theorem norm_phiFactor_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    ‖phiFactor τ ξ‖ ≤ 2 * π * (1 + (4 * π ^ 2 * τ)⁻¹) := by
  set a := 4 * π ^ 2 * τ with ha_def
  have ha : 0 < a := by positivity
  have hr : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have hexp := Real.add_one_le_exp (a * ‖ξ‖ ^ 2)
  have hprod : a⁻¹ * (a * ‖ξ‖ ^ 2) = ‖ξ‖ ^ 2 := by field_simp
  have h1 : ‖ξ‖ ≤ (1 + a⁻¹) * Real.exp (a * ‖ξ‖ ^ 2) := by
    have h2 : (1 + a⁻¹) * (a * ‖ξ‖ ^ 2 + 1) ≤ (1 + a⁻¹) * Real.exp (a * ‖ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    have h3 : (1 + a⁻¹) * (a * ‖ξ‖ ^ 2 + 1) = a * ‖ξ‖ ^ 2 + 1 + ‖ξ‖ ^ 2 + a⁻¹ := by
      rw [mul_add, add_mul, add_mul, hprod]
      ring
    nlinarith [sq_nonneg (‖ξ‖ - 1), mul_nonneg ha.le (sq_nonneg ‖ξ‖)]
  have h4 : ‖ξ‖ * Real.exp (-(a * ‖ξ‖ ^ 2)) ≤ 1 + a⁻¹ := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    exact h1
  have hnn : 0 ≤ phiFactor τ ξ := by unfold phiFactor; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  unfold phiFactor
  rw [← ha_def, mul_assoc]
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

theorem inner_freqVec_divFreeC {ξ : Space} (hξ : ξ ≠ 0) (z : CSpace) :
    inner ℂ (freqVec ξ) (divFreeC ξ z) = 0 := by
  have hn : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hξ
  rw [divFreeC, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_freqVec_eq,
    ← inner_freqVec_eq]
  push_cast
  field_simp
  simp

theorem longitudinal_divFreeC (ξ : Space) (z : CSpace) : longitudinal ξ (divFreeC ξ z) = 0 := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [longitudinal_eq, freqVec_zero]
  · rw [longitudinal_eq, inner_freqVec_divFreeC hξ, zero_smul, smul_zero]

theorem conjVec_divFreeC_neg (ξ : Space) (z : CSpace) :
    conjVec (divFreeC (-ξ) (conjVec z)) = divFreeC ξ z := by
  ext i
  simp [divFreeC, conjVec, freqVec, complexifyVec, map_sum, Complex.conj_ofReal]
  ring

theorem inner_longitudinal_eq_zero {ξ : Space} {v : CSpace} (hv : longitudinal ξ v = 0) (z : CSpace) :
    inner ℝ (longitudinal ξ z) v = 0 := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [longitudinal_eq, freqVec_zero]
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
    have hf : freqVec ξ ≠ 0 := by
      intro h
      apply hn
      rw [← norm_freqVec_eq, h, norm_zero]
    have hs : inner ℂ (freqVec ξ) v = 0 := by
      rw [longitudinal_eq] at hv
      rcases smul_eq_zero.1 hv with h | h
      · exact absurd h (inv_ne_zero (pow_ne_zero _ hn))
      · rcases smul_eq_zero.1 h with h' | h'
        · exact h'
        · exact absurd h' hf
    rw [show inner ℝ (longitudinal ξ z) v = (inner ℂ (longitudinal ξ z) v).re from rfl, longitudinal_eq, ← Complex.coe_smul, smul_smul, inner_smul_left,
      ← inner_conj_symm, hs]
    simp

theorem coe_complexify (g : L2R) :
    (complexify g : Space → CSpace) =ᵐ[volume] fun x => complexifyVec (g x) :=
  ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) complexifyVec g

theorem freqTrR_complexify_physField {A : Space → CSpace} (h1 : MemLp A 1 volume)
    (h2 : MemLp A 2 volume) (hA : ∀ ξ, A (-ξ) = conjVec (A ξ)) :
    freqTrR (complexify (toLpOrZero 2 (physField A))) = toLpOrZero 2 A := by
  have hi : Integrable A volume := memLp_one_iff_integrable.1 h1
  have hm : MemLp (physField A) 2 volume := memLp_realVec_freqTrInv hi h2
  have e : complexify (toLpOrZero 2 (physField A)) = freqTrL2.symm (toLpOrZero 2 A) := by
    apply Lp.ext
    filter_upwards [coe_complexify (toLpOrZero 2 (physField A)), toLpOrZero_ae_eq_real hm,
      freqTrInv_ae hi h2] with x a b c
    rw [a, b, ← c]
    exact complexifyVec_realVec (conjVec_freqTrInv hi hA x)
  rw [e]
  exact freqTrL2.apply_symm_apply _

end Internal.RegIdentifyDivFree

open Internal.RegIdentifyDivFree Internal.RegEmbed in
theorem coe_heatDivFree_physField (hR : FieldOpRealized) {A : Space → CSpace}
    (h1 : MemLp A 1 volume) (h2 : MemLp A 2 volume) (hA : ∀ ξ, A (-ξ) = conjVec (A ξ))
    {τ : ℝ} (hτ : 0 < τ) :
    ((heatDivFree τ (toLpOrZero 2 (physField A)) : X) : Space → CSpace) =ᵐ[volume]
      fun ξ => ((phiFactor τ ξ : ℝ) : ℂ) • divFreeC ξ (A ξ) := by
  set k : L2C := fieldOp id (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace)
    (toLpOrZero 2 A) with hk_def
  have hk : (k : Space → CSpace) =ᵐ[volume] fun ξ => phiFactor τ ξ • A ξ := by
    have : (k : Space → CSpace) =ᵐ[volume]
        fun ξ => (phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) ((toLpOrZero 2 A : Space → CSpace) ξ) :=
      hR (ContinuousLinearEquiv.refl ℝ Space)
      (fun ξ => phiFactor τ ξ • ContinuousLinearMap.id ℝ CSpace) (2 * π * (1 + (4 * π ^ 2 * τ)⁻¹))
      ((continuous_phi τ).aestronglyMeasurable.smul aestronglyMeasurable_const)
      (fun ξ => (norm_smul_le _ _).trans (by
        calc ‖phiFactor τ ξ‖ * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ ‖phiFactor τ ξ‖ * 1 :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (norm_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact norm_phiFactor_le hτ ξ))
      (toLpOrZero 2 A)
    filter_upwards [this, toLpOrZero_ae_eq h2] with ξ a b
    rw [a]
    simp [b]
  set c : L2C := fieldOp id (fun ξ => ContinuousLinearMap.id ℝ CSpace - longitudinal ξ) k with hc_def
  have hc0 : (c : Space → CSpace) =ᵐ[volume] fun ξ => k ξ - longitudinal ξ (k ξ) := by
    have : (c : Space → CSpace) =ᵐ[volume]
        fun ξ => (ContinuousLinearMap.id ℝ CSpace - longitudinal ξ) ((k : Space → CSpace) ξ) :=
      hR (ContinuousLinearEquiv.refl ℝ Space)
      (fun ξ => ContinuousLinearMap.id ℝ CSpace - longitudinal ξ) 2
      (aestronglyMeasurable_const.sub aestronglyMeasurable_longitudinal)
      (fun ξ => (norm_sub_le _ _).trans (by
        linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := CSpace), norm_longitudinal_le_one ξ]))
      k
    filter_upwards [this] with ξ a
    rw [a]
    rfl
  have hc : (c : Space → CSpace) =ᵐ[volume] fun ξ => ((phiFactor τ ξ : ℝ) : ℂ) • divFreeC ξ (A ξ) := by
    filter_upwards [hc0, hk] with ξ a b
    rw [a, b, map_smul, ← smul_sub, ← divFreeC_eq_sub, Complex.coe_smul]
  have hcS : c ∈ Sig := by
    simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      _root_.sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
    constructor
    · apply Lp.ext
      have hneg : (fun ξ => (c : Space → CSpace) (-ξ)) =ᵐ[volume]
          fun ξ => ((phiFactor τ (-ξ) : ℝ) : ℂ) • divFreeC (-ξ) (A (-ξ)) :=
        (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp hc
      filter_upwards [hR (ContinuousLinearEquiv.neg ℝ) (fun _ => conjVec) ‖conjVec‖
        aestronglyMeasurable_const (fun _ => le_rfl) c, hneg, hc] with ξ a b d
      change (reflConj c : Space → CSpace) ξ = _ at a
      rw [a]
      change conjVec ((c : Space → CSpace) (-ξ)) = _
      rw [b, d, phiFactor_neg, hA, conjVec_smul, conjVec_divFreeC_neg]
      simp [Complex.conj_ofReal]
    · apply Lp.ext
      have hl : (fieldOp id longitudinal c : Space → CSpace) =ᵐ[volume]
          fun ξ => longitudinal ξ ((c : Space → CSpace) ξ) :=
        hR (ContinuousLinearEquiv.refl ℝ Space) longitudinal 1
          aestronglyMeasurable_longitudinal norm_longitudinal_le_one c
      filter_upwards [hl, hc, Lp.coeFn_zero CSpace 2 volume] with ξ a b d
      rw [a, d, b, Complex.coe_smul, map_smul, longitudinal_divFreeC, smul_zero]
      rfl
  have horth : ∀ w ∈ Sig, inner ℝ (k - c) w = 0 := by
    intro w hw
    have hw2 : fieldOp id longitudinal w = 0 := by
      simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hw
      exact hw.2
    have hwl : ∀ᵐ ξ ∂(volume : Measure Space), longitudinal ξ ((w : Space → CSpace) ξ) = 0 := by
      have hl : (fieldOp id longitudinal w : Space → CSpace) =ᵐ[volume]
          fun ξ => longitudinal ξ ((w : Space → CSpace) ξ) :=
        hR (ContinuousLinearEquiv.refl ℝ Space) longitudinal 1
          aestronglyMeasurable_longitudinal norm_longitudinal_le_one w
      filter_upwards [hl, Lp.coeFn_zero CSpace 2 volume] with ξ a d
      rw [← a, hw2, d]
      rfl
    rw [MeasureTheory.L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_sub k c, hc0, hwl] with ξ a b d
    rw [a, Pi.sub_apply, b, sub_sub_cancel]
    exact inner_longitudinal_eq_zero d _
  have hproj : heatDivFree τ (toLpOrZero 2 (physField A)) = ⟨c, hcS⟩ := by
    have e : heatDivFree τ (toLpOrZero 2 (physField A)) = projX k := by
      simp only [heatDivFree, ContinuousLinearMap.comp_apply, freqTrR_complexify_physField h1 h2 hA, hk_def]
    rw [e]
    apply Subtype.ext
    have := Submodule.eq_starProjection_of_mem_of_inner_eq_zero hcS horth
    rw [Submodule.starProjection_apply] at this
    exact this
  rw [hproj]
  exact hc

end Breakdown.SmoothFlow
