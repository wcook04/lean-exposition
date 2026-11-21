import Breakdown.Frac.StSpaceReg
import Breakdown.Frac.RHeat
import Breakdown.FreqTr.FieldOp
import Breakdown.Uniqueness.RegIdentifyAuxDivFree

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace PowerInternal.HeatProj

theorem powerPhi_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ fracPhiFactor α τ ξ := by
  unfold fracPhiFactor
  positivity

theorem powerPhi_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    fracPhiFactor α τ ξ ≤ 1 + τ⁻¹ := by
  unfold fracPhiFactor
  set s := 2 * π * ‖ξ‖ with hs_def
  have hs : 0 ≤ s := by positivity
  have hpow : 0 ≤ s ^ (2 * α) := Real.rpow_nonneg hs _
  have he : Real.exp (-(τ * s ^ (2 * α))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hti : 0 < τ⁻¹ := inv_pos.mpr hτ
  rcases le_or_gt s 1 with h1 | h1
  · have : s * Real.exp (-(τ * s ^ (2 * α))) ≤ 1 * 1 :=
      mul_le_mul h1 he (Real.exp_pos _).le zero_le_one
    linarith
  · have hsp : s ≤ s ^ (2 * α) := by
      calc s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
        _ ≤ s ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    have he2 : Real.exp (-(τ * s ^ (2 * α))) ≤ Real.exp (-(τ * s)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hex : τ * s ≤ Real.exp (τ * s) := by
      have := Real.add_one_le_exp (τ * s)
      linarith
    have hkey : τ * (s * Real.exp (-(τ * s))) ≤ 1 := by
      rw [Real.exp_neg, ← mul_assoc, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      exact hex
    have hk2 : s * Real.exp (-(τ * s)) ≤ τ⁻¹ := by
      calc s * Real.exp (-(τ * s)) = τ⁻¹ * (τ * (s * Real.exp (-(τ * s)))) := by
            field_simp
        _ ≤ τ⁻¹ * 1 := mul_le_mul_of_nonneg_left hkey hti.le
        _ = τ⁻¹ := mul_one _
    have : s * Real.exp (-(τ * s ^ (2 * α))) ≤ s * Real.exp (-(τ * s)) :=
      mul_le_mul_of_nonneg_left he2 hs
    linarith

theorem powerPhi_continuous {α : ℝ} (hα : 1 < α) (τ : ℝ) : Continuous (fracPhiFactor α τ) := by
  have hb : Continuous fun ξ : Space => 2 * π * ‖ξ‖ := continuous_const.mul continuous_norm
  have hr : Continuous fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α) :=
    hb.rpow_const fun _ => Or.inr (by linarith)
  exact hb.mul (Real.continuous_exp.comp ((continuous_const.mul hr).neg))

theorem powerPhi_neg (α τ : ℝ) (ξ : Space) : fracPhiFactor α τ (-ξ) = fracPhiFactor α τ ξ := by
  simp [fracPhiFactor]

theorem powerPhi_norm_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    ‖fracPhiFactor α τ ξ‖ ≤ 1 + τ⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (powerPhi_nonneg α τ ξ)]
  exact powerPhi_le hα hτ ξ

end PowerInternal.HeatProj

open PowerInternal.HeatProj

theorem powerHeatX (α : ℝ) : PowerHeatXStatement α := by
  intro t x
  have hm : Measurable fun ξ : Space => fracHeatFactor α t ξ :=
    Breakdown.FracInternal.RHeat.measurable_factor α t
  have hreal := fieldOpRealized (ContinuousLinearEquiv.refl ℝ Space)
    (fun ξ => fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace) 1
    (hm.aestronglyMeasurable.smul aestronglyMeasurable_const) (fun ξ => by
      refine (norm_smul_le _ _).trans ?_
      have h1 : ‖fracHeatFactor α t ξ‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (Breakdown.FracInternal.RHeat.factor_pos α t ξ)]
        exact Breakdown.FracInternal.RHeat.factor_le_one α t ξ
      calc ‖fracHeatFactor α t ξ‖ * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 * 1 :=
            mul_le_mul h1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
  have e := (fracHeatSemigroup α).2.2.2.2.2 t x
  have h2 := hreal (x : L2C)
  rw [e]
  filter_upwards [h2] with ξ hξ
  rw [Complex.coe_smul]
  exact hξ

open Internal.RegIdentifyDivFree Internal.RegEmbed in
private theorem coe_powerProj_physField {α : ℝ} (hα : 1 < α) {A : Space → CSpace}
    (h1 : MemLp A 1 volume) (h2 : MemLp A 2 volume) (hA : ∀ ξ, A (-ξ) = conjVec (A ξ))
    {τ : ℝ} (hτ : 0 < τ) :
    ((fracHeatSolenoidal α τ (toLpOrZero 2 (physField A)) : X) : Space → CSpace) =ᵐ[volume]
      fun ξ => ((fracPhiFactor α τ ξ : ℝ) : ℂ) • divFreeC ξ (A ξ) := by
  set k : L2C := fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace)
    (toLpOrZero 2 A) with hk_def
  have hk : (k : Space → CSpace) =ᵐ[volume] fun ξ => fracPhiFactor α τ ξ • A ξ := by
    have : (k : Space → CSpace) =ᵐ[volume]
        fun ξ => (fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace)
          ((toLpOrZero 2 A : Space → CSpace) ξ) :=
      fieldOpRealized (ContinuousLinearEquiv.refl ℝ Space)
      (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) (1 + τ⁻¹)
      ((powerPhi_continuous hα τ).aestronglyMeasurable.smul aestronglyMeasurable_const)
      (fun ξ => (norm_smul_le _ _).trans (by
        calc ‖fracPhiFactor α τ ξ‖ * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤
              ‖fracPhiFactor α τ ξ‖ * 1 :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (norm_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact powerPhi_norm_le hα hτ ξ))
      (toLpOrZero 2 A)
    filter_upwards [this, toLpOrZero_ae_eq h2] with ξ a b
    rw [a]
    simp [b]
  set c : L2C := fieldOp id (fun ξ => ContinuousLinearMap.id ℝ CSpace - longitudinal ξ) k
    with hc_def
  have hc0 : (c : Space → CSpace) =ᵐ[volume] fun ξ => k ξ - longitudinal ξ (k ξ) := by
    have : (c : Space → CSpace) =ᵐ[volume]
        fun ξ => (ContinuousLinearMap.id ℝ CSpace - longitudinal ξ) ((k : Space → CSpace) ξ) :=
      fieldOpRealized (ContinuousLinearEquiv.refl ℝ Space)
      (fun ξ => ContinuousLinearMap.id ℝ CSpace - longitudinal ξ) 2
      (aestronglyMeasurable_const.sub aestronglyMeasurable_longitudinal)
      (fun ξ => (norm_sub_le _ _).trans (by
        linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := CSpace),
          norm_longitudinal_le_one ξ]))
      k
    filter_upwards [this] with ξ a
    rw [a]
    rfl
  have hc : (c : Space → CSpace) =ᵐ[volume]
      fun ξ => ((fracPhiFactor α τ ξ : ℝ) : ℂ) • divFreeC ξ (A ξ) := by
    filter_upwards [hc0, hk] with ξ a b
    rw [a, b, map_smul, ← smul_sub, ← divFreeC_eq_sub, Complex.coe_smul]
  have hcS : c ∈ Sig := by
    simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      _root_.sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
    constructor
    · apply Lp.ext
      have hneg : (fun ξ => (c : Space → CSpace) (-ξ)) =ᵐ[volume]
          fun ξ => ((fracPhiFactor α τ (-ξ) : ℝ) : ℂ) • divFreeC (-ξ) (A (-ξ)) :=
        (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp hc
      filter_upwards [fieldOpRealized (ContinuousLinearEquiv.neg ℝ) (fun _ => conjVec) ‖conjVec‖
        aestronglyMeasurable_const (fun _ => le_rfl) c, hneg, hc] with ξ a b d
      change (reflConj c : Space → CSpace) ξ = _ at a
      rw [a]
      change conjVec ((c : Space → CSpace) (-ξ)) = _
      rw [b, d, powerPhi_neg, hA, conjVec_smul, conjVec_divFreeC_neg]
      simp [Complex.conj_ofReal]
    · apply Lp.ext
      have hl : (fieldOp id longitudinal c : Space → CSpace) =ᵐ[volume]
          fun ξ => longitudinal ξ ((c : Space → CSpace) ξ) :=
        fieldOpRealized (ContinuousLinearEquiv.refl ℝ Space) longitudinal 1
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
        fieldOpRealized (ContinuousLinearEquiv.refl ℝ Space) longitudinal 1
          aestronglyMeasurable_longitudinal norm_longitudinal_le_one w
      filter_upwards [hl, Lp.coeFn_zero CSpace 2 volume] with ξ a d
      rw [← a, hw2, d]
      rfl
    rw [MeasureTheory.L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_sub k c, hc0, hwl] with ξ a b d
    rw [a, Pi.sub_apply, b, sub_sub_cancel]
    exact inner_longitudinal_eq_zero d _
  have hproj : fracHeatSolenoidal α τ (toLpOrZero 2 (physField A)) = ⟨c, hcS⟩ := by
    have e : fracHeatSolenoidal α τ (toLpOrZero 2 (physField A)) = projX k := by
      simp only [fracHeatSolenoidal, ContinuousLinearMap.comp_apply,
        freqTrR_complexify_physField h1 h2 hA, hk_def]
    rw [e]
    apply Subtype.ext
    have := Submodule.eq_starProjection_of_mem_of_inner_eq_zero hcS horth
    rw [Submodule.starProjection_apply] at this
    exact this
  rw [hproj]
  exact hc

theorem powerSolenoidal (α : ℝ) (hα : 1 < α) : PowerSolenoidalStatement α :=
  ⟨powerPhi_continuous hα, powerPhi_neg α, ⟨1, fun τ hτ ξ => by
    rw [one_mul]; exact powerPhi_norm_le hα hτ ξ⟩,
    fun _ h1 h2 hA _ hτ => coe_powerProj_physField hα h1 h2 hA hτ⟩

end Breakdown.SmoothFlow
