import Breakdown.Frac.StRealize
import Breakdown.FreqTr.FieldOp
import Breakdown.FreqTr.Dilation
import Breakdown.FreqTr.DilationCont

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace FracInternal.Dilation

open Internal.Dilation Internal.DilationCont

theorem fracDilL2_ae {α μ : ℝ} (hμ : 0 < μ) (f : L2C) :
    (fracDilL2 α μ f : Space → CSpace) =ᵐ[volume]
      fun ξ => (μ ^ (1 - 3 / (2 * α))) • (f : Space → CSpace) ((μ ^ (-(1 / (2 * α)))) • ξ) := by
  have hc : μ ^ (-(1 / (2 * α))) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  have := fieldOpRealized (scaleEquiv _ hc)
    (fun _ => (μ ^ (1 - 3 / (2 * α))) • ContinuousLinearMap.id ℝ CSpace)
    ‖(μ ^ (1 - 3 / (2 * α))) • ContinuousLinearMap.id ℝ CSpace‖
    aestronglyMeasurable_const (fun _ => le_rfl) f
  have e : fieldOp (⇑(scaleEquiv _ hc))
      (fun _ => (μ ^ (1 - 3 / (2 * α))) • ContinuousLinearMap.id ℝ CSpace) = fracDilL2 α μ := rfl
  rw [e] at this
  exact this.mono fun ξ hξ => by rw [hξ]; rfl

theorem fracDilL2_eq {α μ : ℝ} (hα : α ≠ 0) (hμ : 0 < μ) (f : L2C) :
    fracDilL2 α μ f = (μ ^ (1 - 1 / α)) • scaleOp (μ ^ (-(1 / (2 * α)))) f := by
  have hc : μ ^ (-(1 / (2 * α))) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  apply Lp.ext
  filter_upwards [fracDilL2_ae (α := α) hμ f, Lp.coeFn_smul (μ ^ (1 - 1 / α)) (scaleOp _ f),
    scaleOp_realized fieldOpRealized hc f] with ξ a b d
  rw [a, b, Pi.smul_apply, d, smul_smul, ← Real.rpow_add hμ]
  congr 2
  field_simp
  ring

theorem norm_fracDilL2 {α μ : ℝ} (hα : α ≠ 0) (hμ : 0 < μ) (f : L2C) :
    ‖fracDilL2 α μ f‖ = μ ^ dilExponent α * ‖f‖ := by
  have hcpos : 0 < μ ^ (-(1 / (2 * α))) := Real.rpow_pos_of_pos hμ _
  rw [fracDilL2_eq hα hμ f, norm_smul, norm_scaleOp fieldOpRealized hcpos,
    Real.norm_of_nonneg (Real.rpow_nonneg hμ.le _)]
  have h3 : ((μ ^ (-(1 / (2 * α)))) ^ 3)⁻¹ = μ ^ (3 * (1 / (2 * α))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμ.le, ← Real.rpow_neg hμ.le]
    congr 1
    push_cast
    ring
  rw [h3, ← Real.rpow_mul hμ.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hμ, ← Real.rpow_add hμ]
  congr 2
  unfold dilExponent
  field_simp
  ring

theorem fracHeatFactor_le_one (α t : ℝ) (ξ : Space) : |fracHeatFactor α t ξ| ≤ 1 := by
  unfold fracHeatFactor
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  have h1 : 0 ≤ max t 0 := le_max_right _ _
  have h2 : 0 ≤ (2 * π * ‖ξ‖) ^ (2 * α) := Real.rpow_nonneg (by positivity) _
  exact mul_nonneg h1 h2

theorem fracHeatL2_ae {α : ℝ} (hα : 0 < α) (t : ℝ) (f : L2C) :
    (fracHeatL2 α t f : Space → CSpace) =ᵐ[volume]
      fun ξ => fracHeatFactor α t ξ • (f : Space → CSpace) ξ := by
  have hcont : Continuous (fun ξ : Space => fracHeatFactor α t ξ) := by
    unfold fracHeatFactor
    have hr : Continuous (fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α)) :=
      (continuous_const.mul continuous_norm).rpow_const fun _ => Or.inr (by positivity)
    exact (continuous_const.mul hr).neg.rexp
  have hF : Continuous (fun ξ : Space => fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace) :=
    hcont.smul continuous_const
  have hb : ∀ ξ, ‖fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 := fun ξ => by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]
    calc |fracHeatFactor α t ξ| * ‖ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 * 1 :=
          mul_le_mul (fracHeatFactor_le_one α t ξ) ContinuousLinearMap.norm_id_le (norm_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have := fieldOpRealized (ContinuousLinearEquiv.refl ℝ Space) _ 1 hF.aestronglyMeasurable hb f
  have e : fieldOp (⇑(ContinuousLinearEquiv.refl ℝ Space))
      (fun ξ => fracHeatFactor α t ξ • ContinuousLinearMap.id ℝ CSpace) = fracHeatL2 α t := rfl
  rw [e] at this
  exact this.mono fun ξ hξ => by rw [hξ]; rfl

theorem mem_sig_of_ae {T : L2C →L[ℝ] L2C} {a c : ℝ} (hc : c ≠ 0)
    (hT : ∀ f : L2C, (T f : Space → CSpace) =ᵐ[volume] fun ξ => a • (f : Space → CSpace) (c • ξ))
    {f : L2C} (hf : f ∈ Sig) : T f ∈ Sig := by
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure Space) hc
  have hn : Measure.QuasiMeasurePreserving (fun ξ : Space => -ξ) volume volume :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving
  have hD := hT f
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
      have hD' := hRr (T f)
      change (reflConj (T f) : Space → CSpace) =ᵐ[volume] _ at hD'
      filter_upwards [hD', hn.ae_eq_comp hD, hq.ae_eq_comp e1, hD] with ξ h₁ h₂ h₃ h₄
      simp only [Function.comp_apply] at h₂ h₃
      rw [h₁, h₂, h₄, ← h₃, map_smul, smul_neg]
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
      filter_upwards [hLr (T f), hq.ae_eq_comp e2, hD, Lp.coeFn_zero CSpace 2 (volume : Measure Space)]
        with ξ h₁ h₂ h₄ z
      simp only [Function.comp_apply, Pi.zero_apply] at h₂
      rw [h₁, z, id, h₄, map_smul, ← longitudinal_smul hc ξ, h₂, smul_zero, Pi.zero_apply]
    · rw [fieldOp_eq_zero_of_not hL, zero_apply]

theorem fracDilX_coe {α μ : ℝ} (hμ : 0 < μ) (x : X) :
    (fracDilX α μ x : L2C) = fracDilL2 α μ x := by
  have hc : μ ^ (-(1 / (2 * α))) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
  have hmem : ∀ y ∈ Sig, fracDilL2 α μ y ∈ Sig := fun y hy =>
    mem_sig_of_ae hc (fracDilL2_ae hμ) hy
  simp only [fracDilX, if_pos hμ, restrictX, dif_pos hmem]
  rfl

theorem fracHeatFactor_dil {α μ t : ℝ} (hα : 0 < α) (hμ : 0 < μ) (ht : 0 ≤ t) (ξ : Space) :
    fracHeatFactor α (μ * t) ((μ ^ (-(1 / (2 * α)))) • ξ) = fracHeatFactor α t ξ := by
  unfold fracHeatFactor
  rw [max_eq_left (mul_nonneg hμ.le ht), max_eq_left ht, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hμ _),
    show 2 * π * (μ ^ (-(1 / (2 * α))) * ‖ξ‖) = μ ^ (-(1 / (2 * α))) * (2 * π * ‖ξ‖) by ring,
    Real.mul_rpow (Real.rpow_nonneg hμ.le _) (by positivity), ← Real.rpow_mul hμ.le,
    show -(1 / (2 * α)) * (2 * α) = -1 by field_simp, Real.rpow_neg_one]
  congr 2
  field_simp

end FracInternal.Dilation

open FracInternal.Dilation Internal.DilationCont in
theorem fracDilationAlgebra (α : ℝ) (hα : 0 < α) (h1 : FracHeatSemigroup α) :
    FracDilationAlgebra α := by
  refine ⟨?_, ?_, ?_, ?_, fun μ hμ x => fracDilX_coe hμ x⟩
  · intro μ hμ x
    rw [Submodule.coe_norm, fracDilX_coe hμ, norm_fracDilL2 hα.ne' hμ, ← Submodule.coe_norm]
  · ext x : 1
    apply Subtype.ext
    rw [fracDilX_coe one_pos, ContinuousLinearMap.id_apply]
    apply Lp.ext
    filter_upwards [fracDilL2_ae (α := α) one_pos ((x : X) : L2C)] with ξ a
    rw [a]
    simp
  · intro μ ν hμ hν
    ext x : 1
    apply Subtype.ext
    have hc : μ ^ (-(1 / (2 * α))) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
    have hq := Measure.quasiMeasurePreserving_smul (volume : Measure Space) hc
    rw [ContinuousLinearMap.comp_apply, fracDilX_coe (mul_pos hμ hν), fracDilX_coe hμ,
      fracDilX_coe hν]
    apply Lp.ext
    filter_upwards [fracDilL2_ae (α := α) (mul_pos hμ hν) ((x : X) : L2C),
      fracDilL2_ae (α := α) hμ (fracDilL2 α ν x),
      hq.ae_eq_comp (fracDilL2_ae (α := α) hν ((x : X) : L2C))] with ξ a b d
    simp only [Function.comp_apply] at d
    rw [a, b, d, Real.mul_rpow hμ.le hν.le, Real.mul_rpow hμ.le hν.le]
    simp only [smul_smul]
    rw [mul_comm (ν ^ (-(1 / (2 * α)))) (μ ^ (-(1 / (2 * α))))]
  · intro μ t hμ ht
    ext x : 1
    apply Subtype.ext
    have hc : μ ^ (-(1 / (2 * α))) ≠ 0 := (Real.rpow_pos_of_pos hμ _).ne'
    have hq := Measure.quasiMeasurePreserving_smul (volume : Measure Space) hc
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, fracDilX_coe hμ,
      h1.2.2.2.2.2 (μ * t) x, h1.2.2.2.2.2 t, fracDilX_coe hμ]
    apply Lp.ext
    filter_upwards [fracDilL2_ae (α := α) hμ (fracHeatL2 α (μ * t) ((x : X) : L2C)),
      hq.ae_eq_comp (fracHeatL2_ae hα (μ * t) ((x : X) : L2C)),
      fracHeatL2_ae hα t (fracDilL2 α μ ((x : X) : L2C)),
      fracDilL2_ae (α := α) hμ ((x : X) : L2C)] with ξ a b d e
    simp only [Function.comp_apply] at b
    rw [a, b, d, e, fracHeatFactor_dil hα hμ ht, smul_comm]

open FracInternal.Dilation Internal.DilationCont in
theorem fracDilationContinuous (α : ℝ) (hα : 0 < α) (h1 : FracDilationAlgebra α) :
    FracDilationContinuous α := by
  intro x
  refine continuousOn_of_forall_continuousAt fun μ₀ hμ₀ => ?_
  rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
  have heq : (Subtype.val ∘ fun μ => fracDilX α μ x) =ᶠ[𝓝 μ₀]
      fun μ => (μ ^ (1 - 1 / α)) • scaleOp (μ ^ (-(1 / (2 * α)))) (x : L2C) := by
    filter_upwards [Ioi_mem_nhds hμ₀] with μ hμ
    exact (h1.2.2.2.2 μ hμ x).trans (fracDilL2_eq hα.ne' hμ x)
  refine ContinuousAt.congr ?_ heq.symm
  have hs : ContinuousAt (fun μ : ℝ => μ ^ (-(1 / (2 * α)))) μ₀ :=
    Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hμ₀))
  have ha : ContinuousAt (fun μ : ℝ => μ ^ (1 - 1 / α)) μ₀ :=
    Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hμ₀))
  exact ha.smul ((tendsto_scaleOp fieldOpRealized (Real.rpow_pos_of_pos hμ₀ _) _).comp hs)

end Breakdown.Freq
