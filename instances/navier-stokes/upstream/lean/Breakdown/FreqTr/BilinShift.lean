import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.BilinShift

theorem scalar_ae (h3 : FieldOpRealized) {m : Space → ℝ} (hm : Continuous m) {C : ℝ}
    (hC : ∀ ξ, |m ξ| ≤ C) (f : L2C) :
    (fieldOp id (fun ξ => m ξ • ContinuousLinearMap.id ℝ CSpace) f : Space → CSpace) =ᵐ[volume]
      fun ξ => m ξ • (f : Space → CSpace) ξ := by
  have hF : AEStronglyMeasurable (fun ξ => m ξ • ContinuousLinearMap.id ℝ CSpace) volume :=
    (hm.smul continuous_const).aestronglyMeasurable
  have hb : ∀ ξ, ‖m ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ C := by
    intro ξ
    calc ‖m ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ ‖m ξ‖ * ‖ContinuousLinearMap.id ℝ CSpace‖ :=
          norm_smul_le _ _
      _ ≤ |m ξ| * 1 :=
          mul_le_mul (le_of_eq (Real.norm_eq_abs _)) ContinuousLinearMap.norm_id_le (norm_nonneg _)
            (abs_nonneg _)
      _ ≤ C := by rw [mul_one]; exact hC ξ
  have h := h3 (ContinuousLinearEquiv.refl ℝ Space) _ C hF hb
  rw [ContinuousLinearEquiv.coe_refl'] at h
  filter_upwards [h f] with ξ hξ
  simpa using hξ

theorem heatFactor_abs_le (t : ℝ) (ξ : Space) : |heatFactor t ξ| ≤ 1 := by
  unfold heatFactor
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  have := le_max_right t 0
  positivity

theorem phiFactor_abs_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) : |phiFactor τ ξ| ≤ 1 + τ⁻¹ := by
  unfold phiFactor
  set a : ℝ := 2 * π * ‖ξ‖ with ha
  have ha0 : 0 ≤ a := by positivity
  have hq : 4 * π ^ 2 * τ * ‖ξ‖ ^ 2 = τ * a ^ 2 := by rw [ha]; ring
  rw [hq]
  have he : 1 + τ * a ^ 2 ≤ Real.exp (τ * a ^ 2) := by
    linarith [Real.add_one_le_exp (τ * a ^ 2)]
  have hpos : 0 < 1 + τ * a ^ 2 := by positivity
  have hm : Real.exp (-(τ * a ^ 2)) * Real.exp (τ * a ^ 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hE : 0 < Real.exp (-(τ * a ^ 2)) := Real.exp_pos _
  have hinv : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ.ne'
  have hτi : 0 < τ⁻¹ := inv_pos.mpr hτ
  rw [abs_of_nonneg (by positivity)]
  have key : a ≤ (1 + τ⁻¹) * (1 + τ * a ^ 2) := by
    nlinarith [sq_nonneg (a - 1), mul_nonneg hτi.le (sq_nonneg a)]
  have h1 : a * Real.exp (-(τ * a ^ 2)) * (1 + τ * a ^ 2) ≤ a := by
    calc a * Real.exp (-(τ * a ^ 2)) * (1 + τ * a ^ 2)
        ≤ a * Real.exp (-(τ * a ^ 2)) * Real.exp (τ * a ^ 2) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = a := by rw [mul_assoc, hm, mul_one]
  by_contra hc
  push Not at hc
  have := mul_lt_mul_of_pos_right hc hpos
  linarith

theorem continuous_heatFactor (t : ℝ) : Continuous (heatFactor t) := by
  unfold heatFactor; fun_prop

theorem continuous_phiFactor (τ : ℝ) : Continuous (phiFactor τ) := by
  unfold phiFactor; fun_prop

theorem phiFactor_mul_heatFactor {s : ℝ} (hs : 0 ≤ s) (τ : ℝ) (ξ : Space) :
    phiFactor τ ξ * heatFactor s ξ = phiFactor (s + τ) ξ := by
  unfold phiFactor heatFactor
  rw [max_eq_left hs, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem phiX_heatX (h2 : HeatSemigroup) (h3 : FieldOpRealized) {s τ : ℝ} (hs : 0 ≤ s)
    (hτ : 0 < τ) (ψ : X) : phiX τ (heatX s ψ) = phiX (s + τ) ψ := by
  have hst : 0 < s + τ := by linarith
  simp only [phiX, ContinuousLinearMap.coe_comp, Function.comp_apply]
  congr 1
  change fieldOp id _ (heatX s ψ : L2C) = fieldOp id _ (ψ : L2C)
  rw [h2.2.2.2.2.2 s ψ]
  apply Lp.ext
  filter_upwards [scalar_ae h3 (continuous_phiFactor τ) (phiFactor_abs_le hτ) (heatL2 s ψ),
    scalar_ae h3 (continuous_heatFactor s) (heatFactor_abs_le s) (ψ : L2C),
    scalar_ae h3 (continuous_phiFactor (s + τ)) (phiFactor_abs_le hst) (ψ : L2C)] with ξ e1 e2 e3
  rw [e1, e3]
  change phiFactor τ ξ • (fieldOp id (fun ξ => heatFactor s ξ • ContinuousLinearMap.id ℝ CSpace)
    (ψ : L2C) : Space → CSpace) ξ = _
  rw [e2, smul_smul, phiFactor_mul_heatFactor hs]

theorem bilinX_spec (h1 : BilinExists) {t : ℝ} (ht : 0 < t) : BilinSpec t (bilinX t) := by
  have h : 0 < t ∧ ∃ B, BilinSpec t B := ⟨ht, h1 t ht⟩
  unfold bilinX
  rw [dif_pos h]
  exact h.2.choose_spec

end Internal.BilinShift

open Internal.BilinShift in
theorem bilinShift (h1 : BilinExists) (h2 : HeatSemigroup) (h3 : FieldOpRealized) :
    BilinShift := by
  intro s τ hs hτ u v
  have hst : 0 < s + τ := by linarith
  apply ext_inner_right ℝ
  intro ψ
  rw [h2.2.2.2.2.1 s, bilinX_spec h1 hτ, bilinX_spec h1 hst, bilinForm, bilinForm,
    phiX_heatX h2 h3 hs hτ]

end Breakdown.Freq
