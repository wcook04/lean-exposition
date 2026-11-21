import Breakdown.Frac.StTorusShell
import Breakdown.Torus.HeatComparisonProj
import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.FreqTrL1
import Breakdown.FreqTr.FreqTrConjSym

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracSolenoidalProjection.Internal

open Freq Freq.Internal.H1Consistency

theorem fracHeat_neg (α τ : ℝ) (ξ : Space) : fracHeatFactor α τ (-ξ) = fracHeatFactor α τ ξ := by
  simp [fracHeatFactor, norm_neg]

theorem fracPhi_neg (α τ : ℝ) (ξ : Space) : fracPhiFactor α τ (-ξ) = fracPhiFactor α τ ξ := by
  simp [fracPhiFactor, norm_neg]

theorem norm_fracHeat_smul_le (α τ : ℝ) (ξ : Space) :
    ‖fracHeatFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 := by
  refine (norm_smul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans ?_
  unfold fracHeatFactor
  rw [mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  have : 0 ≤ max τ 0 * (2 * π * ‖ξ‖) ^ (2 * α) := by positivity
  linarith

theorem base_le (α : ℝ) (hα : 1 < α) (r : ℝ) (hr : 0 ≤ r) : r ≤ 1 + r ^ (2 * α) := by
  rcases le_or_gt r 1 with h | h
  · have : 0 ≤ r ^ (2 * α) := Real.rpow_nonneg hr _
    linarith
  · have h2 : r ^ (1 : ℝ) ≤ r ^ (2 * α) := Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
    rw [Real.rpow_one] at h2
    linarith

theorem norm_fracPhi_smul_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    ‖fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ 1 + 1 / τ := by
  refine (norm_smul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans ?_
  have hp : 0 ≤ fracPhiFactor α τ ξ := by unfold fracPhiFactor; positivity
  rw [mul_one, Real.norm_eq_abs, abs_of_nonneg hp]
  unfold fracPhiFactor
  set r := 2 * π * ‖ξ‖ with hrdef
  have hr : 0 ≤ r := by positivity
  set s := r ^ (2 * α) with hsdef
  have hs : 0 ≤ s := Real.rpow_nonneg hr _
  have hrs : r ≤ 1 + s := base_le α hα r hr
  have he := Real.add_one_le_exp (τ * s)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have h1 : (1 + 1 / τ) * (τ * s + 1) = τ * s + 1 + s + 1 / τ := by
    field_simp
    ring
  have h2 : r ≤ (1 + 1 / τ) * (τ * s + 1) := by
    rw [h1]
    have : 0 ≤ 1 / τ := by positivity
    have : 0 ≤ τ * s := by positivity
    linarith
  calc r ≤ (1 + 1 / τ) * (τ * s + 1) := h2
    _ ≤ (1 + 1 / τ) * Real.exp (τ * s) := by
      apply mul_le_mul_of_nonneg_left he; positivity

theorem fracHeat_ae (h1 : FieldOpRealized) (α τ : ℝ) (f : L2C) :
    (fieldOp id (fun ξ => fracHeatFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) f : Space → CSpace)
      =ᵐ[volume] fun ξ => fracHeatFactor α τ ξ • f ξ := by
  have hm : Measurable (fun ξ : Space => fracHeatFactor α τ ξ) := by
    unfold fracHeatFactor; fun_prop
  have hc : AEStronglyMeasurable
      (fun ξ : Space => fracHeatFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) volume :=
    (hm.smul_const _).aestronglyMeasurable
  have := Freq.Internal.BilinTestFormula.fieldOp_id_ae h1 _ 1 hc (norm_fracHeat_smul_le α τ) f
  simpa using this

theorem fracPhi_ae (h1 : FieldOpRealized) {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (f : L2C) :
    (fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) f : Space → CSpace)
      =ᵐ[volume] fun ξ => fracPhiFactor α τ ξ • f ξ := by
  have hm : Measurable (fun ξ : Space => fracPhiFactor α τ ξ) := by
    unfold fracPhiFactor; fun_prop
  have hc : AEStronglyMeasurable
      (fun ξ : Space => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) volume :=
    (hm.smul_const _).aestronglyMeasurable
  have := Freq.Internal.BilinTestFormula.fieldOp_id_ae h1 _ (1 + 1 / τ) hc
    (norm_fracPhi_smul_le hα hτ) f
  simpa using this

end FracSolenoidalProjection.Internal

open DivFreeProjection.Internal FracSolenoidalProjection.Internal Freq.Internal.H1Consistency in
theorem fracHeatSolenoidalFactor (α : ℝ) (hα : 1 < α) : FracHeatSolenoidalFactor α := by
  have h1 : Freq.FieldOpRealized := Freq.fieldOpRealized_holds
  have h2 : Freq.FreqTrL1L2 := Freq.freqTrL1L2.1
  have h3 : Freq.FreqTrConjSym := Freq.freqTrConjSym h1
  intro b' τ hτ A hA
  set W : Freq.L2C := Freq.freqTrR (Freq.complexify A) with hWdef
  set s : Freq.L2C := W - Freq.fieldOp id Freq.longitudinal W with hsdef
  set H := Freq.fieldOp id
    (fun ξ => Freq.fracHeatFactor α τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace) with hHdef
  set M := Freq.fieldOp id
    (fun ξ => Freq.fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace) with hMdef
  have hWfreqTr := freqTr_ae h2 hA
  have hs : (s : Space → Freq.CSpace) =ᵐ[volume] fun ξ => W ξ - Freq.longitudinal ξ (W ξ) := by
    filter_upwards [Lp.coeFn_sub W (Freq.fieldOp id Freq.longitudinal W), longitudinal_ae h1 W]
      with ξ e1 e2
    rw [e1, Pi.sub_apply, e2]
  have hsig : s ∈ Freq.Sig := divFree_mem_sig h1 W (h3 A)
  have hg : H s ∈ Freq.Sig :=
    mem_sig_of_ae h1 hsig (Freq.fracHeatFactor α τ) (fracHeat_neg α τ) (fracHeat_ae h1 α τ s)
  have hv : M s ∈ Freq.Sig :=
    mem_sig_of_ae h1 hsig (Freq.fracPhiFactor α τ) (fracPhi_neg α τ) (fracPhi_ae h1 hα hτ s)
  have hp : (Freq.projX (M W) : Freq.L2C) = M s := by
    rw [Freq.projX, Submodule.coe_orthogonalProjectionOnto_apply]
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hv
    intro t ht
    rw [MeasureTheory.L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_sub (M W) (M s), fracPhi_ae h1 hα hτ W, fracPhi_ae h1 hα hτ s, hs,
      ae_longitudinal_of_mem h1 ht] with ξ e1 e2 e3 e4 e5
    rw [e1, Pi.sub_apply, e2, e3, e4, ← smul_sub, sub_sub_cancel, real_inner_smul_left,
      inner_longitudinal, e5, inner_zero_right, mul_zero]
    rfl
  have hhl : (Freq.fracHeatSolenoidal α τ A : Freq.L2C) = M s := hp
  refine ⟨⟨H s, hg⟩, ?_, ?_⟩
  · filter_upwards [fracHeat_ae h1 α τ s, hs, hWfreqTr] with ξ e1 e2 e3
    show (H s : Space → Freq.CSpace) ξ = _
    rw [e1, e2, e3, divFreeVec_eq]
  · unfold Freq.IsHalfSspOf
    rw [hhl]
    filter_upwards [fracPhi_ae h1 hα hτ s, fracHeat_ae h1 α τ s] with ξ e1 e2
    show (M s : Space → Freq.CSpace) ξ = _ • (H s : Space → Freq.CSpace) ξ
    rw [e1, e2, smul_smul]
    congr 1
    unfold Freq.fracPhiFactor Freq.fracHeatFactor
    rw [max_eq_left hτ.le]

end Breakdown.Periodic
