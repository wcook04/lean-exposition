import Breakdown.Frac.StRealize
import Breakdown.Frac.StNiceEmbed
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracInternal.MildWeak

open Breakdown.Freq Breakdown.Freq.Internal.Phi Breakdown.Freq.Internal.WeakInX
  Breakdown.Freq.Internal.MildOfWeak

def powNorm (α : ℝ) (ξ : Space) : ℝ := (2 * π * ‖ξ‖) ^ (2 * α)

theorem powNorm_nonneg (α : ℝ) (ξ : Space) : 0 ≤ powNorm α ξ :=
  Real.rpow_nonneg (by positivity) _

theorem continuous_powNorm {α : ℝ} (hα : 0 < α) : Continuous (powNorm α) := by
  unfold powNorm
  exact (by fun_prop : Continuous fun ξ : Space => 2 * π * ‖ξ‖).rpow_const
    (fun _ => Or.inr (by linarith))

theorem powNorm_neg (α : ℝ) (ξ : Space) : powNorm α (-ξ) = powNorm α ξ := by
  simp [powNorm, norm_neg]

theorem sqFactor_le_powNorm {α : ℝ} (hα : 1 ≤ α) (ξ : Space) :
    sspFactor ξ ≤ 1 + powNorm α ξ := by
  have e : sspFactor ξ = (2 * π * ‖ξ‖) ^ (2 : ℝ) := by
    unfold sspFactor
    rw [Real.rpow_two]
    ring
  rw [e]
  unfold powNorm
  have hy : 0 ≤ 2 * π * ‖ξ‖ := by positivity
  rcases le_or_gt (2 * π * ‖ξ‖) 1 with h | h
  · have h1 : (2 * π * ‖ξ‖) ^ (2 : ℝ) ≤ 1 := Real.rpow_le_one hy h (by norm_num)
    have h2 := Real.rpow_nonneg hy (2 * α)
    linarith
  · have h1 : (2 * π * ‖ξ‖) ^ (2 : ℝ) ≤ (2 * π * ‖ξ‖) ^ (2 * α) :=
      Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
    linarith

theorem one_add_powNorm_pos (α : ℝ) (ξ : Space) : 0 < 1 + powNorm α ξ := by
  have := powNorm_nonneg α ξ
  linarith

def cmpFactor (α : ℝ) (ξ : Space) : ℝ := sspFactor ξ / (1 + powNorm α ξ)

theorem continuous_sqFactor : Continuous sspFactor := by
  unfold sspFactor
  fun_prop

theorem continuous_cmpFactor {α : ℝ} (hα : 0 < α) : Continuous (cmpFactor α) :=
  continuous_sqFactor.div (continuous_const.add (continuous_powNorm hα))
    (fun ξ => (one_add_powNorm_pos α ξ).ne')

theorem abs_cmpFactor_le {α : ℝ} (hα : 1 ≤ α) (ξ : Space) : |cmpFactor α ξ| ≤ 1 := by
  have hp := one_add_powNorm_pos α ξ
  unfold cmpFactor
  rw [abs_of_nonneg (div_nonneg (sspFactor_nonneg ξ) hp.le), div_le_one hp]
  exact sqFactor_le_powNorm hα ξ

theorem sq_norm_le {α : ℝ} (hα : 1 ≤ α) {c d e : X} (hl : IsSspOf c d) (hf : IsFracOf α c e) :
    ‖d‖ ≤ ‖c‖ + ‖e‖ := by
  have h0 : (0 : ℝ) < α := by linarith
  have hyae := scalarOp_ae fieldOpRealized_holds (continuous_cmpFactor h0) (abs_cmpFactor_le hα)
    ((c : L2C) + (e : L2C))
  have hdy : (d : L2C) = fieldOp id (fun ξ => cmpFactor α ξ • ContinuousLinearMap.id ℝ CSpace)
      ((c : L2C) + (e : L2C)) := by
    apply Lp.ext
    filter_upwards [hyae, hl, hf, Lp.coeFn_add (c : L2C) (e : L2C)] with ξ h1 h2 h3 h4
    rw [h1, h2, h4, Pi.add_apply, h3]
    show sspFactor ξ • (c : L2C) ξ = cmpFactor α ξ • ((c : L2C) ξ + powNorm α ξ • (c : L2C) ξ)
    rw [smul_add, smul_smul, ← add_smul]
    congr 1
    have hp := (one_add_powNorm_pos α ξ).ne'
    calc sspFactor ξ = sspFactor ξ / (1 + powNorm α ξ) * (1 + powNorm α ξ) :=
          (div_mul_cancel₀ _ hp).symm
      _ = _ := by unfold cmpFactor; ring
  have hn : ‖d‖ = ‖(d : L2C)‖ := rfl
  rw [hn, hdy]
  refine (scalarOp_norm_le fieldOpRealized_holds (continuous_cmpFactor h0) (abs_cmpFactor_le hα)
    _).trans ?_
  rw [one_mul]
  exact norm_add_le _ _

theorem isFracOf_sub {α : ℝ} {χ h χ' h' : X} (hl : IsFracOf α χ h) (hl' : IsFracOf α χ' h') :
    IsFracOf α (χ - χ') (h - h') := by
  have e1 : ((χ - χ' : X) : L2C) = (χ : L2C) - (χ' : L2C) := rfl
  have e2 : ((h - h' : X) : L2C) = (h : L2C) - (h' : L2C) := rfl
  filter_upwards [hl, hl', Lp.coeFn_sub (χ : L2C) (χ' : L2C), Lp.coeFn_sub (h : L2C) (h' : L2C)]
    with ξ a b c d
  rw [e1, e2, c, d, Pi.sub_apply, Pi.sub_apply, a, b, smul_sub]

theorem velocity_second_nice {α : ℝ} (hN : NiceFieldProps α) {φ : Space → Space}
    (hφ : IsNiceField φ) :
    (velocity (embedX (negSsp φ)) : Space → Space) =ᵐ[volume] negSsp φ :=
  velocityDecay_holds _ (hN _ (hN φ hφ).2.2.1).2.1

def aHeatX (α τ : ℝ) : X →L[ℝ] X :=
  restrictX (fieldOp id (fun ξ =>
    (powNorm α ξ * fracHeatFactor α τ ξ) • ContinuousLinearMap.id ℝ CSpace))

def sqHeatX (α τ : ℝ) : X →L[ℝ] X :=
  restrictX (fieldOp id (fun ξ =>
    (sspFactor ξ * fracHeatFactor α τ ξ) • ContinuousLinearMap.id ℝ CSpace))

theorem heatF_eq (α τ : ℝ) :
    fracHeatFactor α τ = fun ξ => Real.exp (-(max τ 0 * powNorm α ξ)) := rfl

theorem heatF_pos_eq {α τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    fracHeatFactor α τ ξ = Real.exp (-(τ * powNorm α ξ)) := by
  show Real.exp (-(max τ 0 * powNorm α ξ)) = _
  rw [max_eq_left hτ.le]

theorem continuous_heatF {α : ℝ} (hα : 0 < α) (τ : ℝ) : Continuous (fracHeatFactor α τ) := by
  rw [heatF_eq]
  exact Real.continuous_exp.comp ((continuous_const.mul (continuous_powNorm hα)).neg)

theorem heatF_le (α τ : ℝ) (ξ : Space) : |fracHeatFactor α τ ξ| ≤ 1 := by
  show |Real.exp (-(max τ 0 * powNorm α ξ))| ≤ 1
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg (le_max_right _ _) (powNorm_nonneg α ξ)

theorem heatF_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ fracHeatFactor α τ ξ := (Real.exp_pos _).le

theorem heatF_neg (α τ : ℝ) (ξ : Space) : fracHeatFactor α τ (-ξ) = fracHeatFactor α τ ξ := by
  simp [fracHeatFactor, norm_neg]

theorem aHeat_le {α τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    |powNorm α ξ * fracHeatFactor α τ ξ| ≤ τ⁻¹ := by
  rw [heatF_pos_eq hτ, abs_of_nonneg (mul_nonneg (powNorm_nonneg α ξ) (Real.exp_pos _).le)]
  have h := mul_exp_neg_le_one (τ * powNorm α ξ)
  calc powNorm α ξ * Real.exp (-(τ * powNorm α ξ)) =
        τ⁻¹ * (τ * powNorm α ξ * Real.exp (-(τ * powNorm α ξ))) := by
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hτ.ne', one_mul]
    _ ≤ τ⁻¹ * 1 := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hτ.le)
    _ = τ⁻¹ := mul_one _

theorem sqHeat_le {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 < τ) (ξ : Space) :
    |sspFactor ξ * fracHeatFactor α τ ξ| ≤ 1 + τ⁻¹ := by
  have hH0 := heatF_nonneg α τ ξ
  have hH1 : fracHeatFactor α τ ξ ≤ 1 := (le_abs_self _).trans (heatF_le α τ ξ)
  have hPH : powNorm α ξ * fracHeatFactor α τ ξ ≤ τ⁻¹ := (le_abs_self _).trans (aHeat_le hτ ξ)
  rw [abs_of_nonneg (mul_nonneg (sspFactor_nonneg ξ) hH0)]
  calc sspFactor ξ * fracHeatFactor α τ ξ ≤ (1 + powNorm α ξ) * fracHeatFactor α τ ξ :=
        mul_le_mul_of_nonneg_right (sqFactor_le_powNorm hα ξ) hH0
    _ = fracHeatFactor α τ ξ + powNorm α ξ * fracHeatFactor α τ ξ := by ring
    _ ≤ 1 + τ⁻¹ := add_le_add hH1 hPH

theorem aHeat_neg (α τ : ℝ) (ξ : Space) :
    powNorm α (-ξ) * fracHeatFactor α τ (-ξ) = powNorm α ξ * fracHeatFactor α τ ξ := by
  rw [powNorm_neg, heatF_neg]

theorem sqHeat_neg (α τ : ℝ) (ξ : Space) :
    sspFactor (-ξ) * fracHeatFactor α τ (-ξ) = sspFactor ξ * fracHeatFactor α τ ξ := by
  rw [heatF_neg]
  simp [sspFactor, norm_neg]

theorem continuous_aHeat {α : ℝ} (hα : 0 < α) (τ : ℝ) :
    Continuous (fun ξ => powNorm α ξ * fracHeatFactor α τ ξ) :=
  (continuous_powNorm hα).mul (continuous_heatF hα τ)

theorem continuous_sqHeat {α : ℝ} (hα : 0 < α) (τ : ℝ) :
    Continuous (fun ξ => sspFactor ξ * fracHeatFactor α τ ξ) :=
  continuous_sqFactor.mul (continuous_heatF hα τ)

theorem aHeatX_coe {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (x : X) :
    (aHeatX α τ x : L2C) = fieldOp id (fun ξ =>
      (powNorm α ξ * fracHeatFactor α τ ξ) • ContinuousLinearMap.id ℝ CSpace) x := by
  unfold aHeatX restrictX
  rw [dif_pos (fun y hy => scalarOp_mem fieldOpRealized_holds (continuous_aHeat hα τ)
    (aHeat_le hτ) (aHeat_neg α τ) hy)]
  rfl

theorem sqHeatX_coe {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 < τ) (x : X) :
    (sqHeatX α τ x : L2C) = fieldOp id (fun ξ =>
      (sspFactor ξ * fracHeatFactor α τ ξ) • ContinuousLinearMap.id ℝ CSpace) x := by
  unfold sqHeatX restrictX
  rw [dif_pos (fun y hy => scalarOp_mem fieldOpRealized_holds
    (continuous_sqHeat (by linarith) τ) (sqHeat_le hα hτ) (sqHeat_neg α τ) hy)]
  rfl

theorem isFracOf_heat {α τ : ℝ} (hα : 0 < α) (hH : FracHeatSemigroup α) (hτ : 0 < τ) (ψ : X) :
    IsFracOf α (fracHeatX α τ ψ) (aHeatX α τ ψ) := by
  have ha := scalarOp_ae fieldOpRealized_holds (continuous_aHeat hα τ) (aHeat_le hτ) (ψ : L2C)
  have hb := scalarOp_ae fieldOpRealized_holds (continuous_heatF hα τ) (heatF_le α τ) (ψ : L2C)
  rw [← aHeatX_coe hα hτ] at ha
  have e : (fracHeatX α τ ψ : L2C) =
      fieldOp id (fun ξ => fracHeatFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) ψ :=
    hH.2.2.2.2.2 τ ψ
  rw [← e] at hb
  filter_upwards [ha, hb] with ξ a b
  show (aHeatX α τ ψ : L2C) ξ = powNorm α ξ • (fracHeatX α τ ψ : L2C) ξ
  rw [a, b, smul_smul]

theorem sq_heat_rel {α τ : ℝ} (hα : 1 ≤ α) (hH : FracHeatSemigroup α) (hτ : 0 < τ) (ψ : X) :
    IsSspOf (fracHeatX α τ ψ) (sqHeatX α τ ψ) := by
  have h0 : (0 : ℝ) < α := by linarith
  have ha := scalarOp_ae fieldOpRealized_holds (continuous_sqHeat h0 τ) (sqHeat_le hα hτ)
    (ψ : L2C)
  have hb := scalarOp_ae fieldOpRealized_holds (continuous_heatF h0 τ) (heatF_le α τ) (ψ : L2C)
  rw [← sqHeatX_coe hα hτ] at ha
  have e : (fracHeatX α τ ψ : L2C) =
      fieldOp id (fun ξ => fracHeatFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) ψ :=
    hH.2.2.2.2.2 τ ψ
  rw [← e] at hb
  filter_upwards [ha, hb] with ξ a b
  rw [a, b, smul_smul]

set_option maxHeartbeats 1000000 in
theorem frac_heat_expansion_norm {α τ r : ℝ} (hα : 0 < α) (hH : FracHeatSemigroup α) (hτ : 0 < τ)
    (hr : |r - τ| ≤ τ / 2) (ψ : X) :
    ‖fracHeatX α r ψ - fracHeatX α τ ψ - (r - τ) • (-(aHeatX α τ ψ))‖ ≤
      16 / τ ^ 2 * (r - τ) ^ 2 * ‖ψ‖ := by
  have hr0 : 0 < r := by have := neg_abs_le (r - τ); linarith
  have ha := scalarOp_ae fieldOpRealized_holds (continuous_heatF hα r) (heatF_le α r) (ψ : L2C)
  have hb := scalarOp_ae fieldOpRealized_holds (continuous_heatF hα τ) (heatF_le α τ) (ψ : L2C)
  have hc := scalarOp_ae fieldOpRealized_holds (continuous_aHeat hα τ) (aHeat_le hτ) (ψ : L2C)
  have ea : (fracHeatX α r ψ : L2C) =
      fieldOp id (fun ξ => fracHeatFactor α r ξ • ContinuousLinearMap.id ℝ CSpace) ψ :=
    hH.2.2.2.2.2 r ψ
  have eb : (fracHeatX α τ ψ : L2C) =
      fieldOp id (fun ξ => fracHeatFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) ψ :=
    hH.2.2.2.2.2 τ ψ
  rw [← ea] at ha
  rw [← eb] at hb
  rw [← aHeatX_coe hα hτ] at hc
  have hn : ‖fracHeatX α r ψ - fracHeatX α τ ψ - (r - τ) • (-(aHeatX α τ ψ))‖ =
      ‖(fracHeatX α r ψ : L2C) - (fracHeatX α τ ψ : L2C) - (r - τ) • (-(aHeatX α τ ψ : L2C))‖ :=
    rfl
  rw [hn]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ha, hb, hc,
    Lp.coeFn_sub ((fracHeatX α r ψ : L2C) - (fracHeatX α τ ψ : L2C))
      ((r - τ) • (-(aHeatX α τ ψ : L2C))),
    Lp.coeFn_sub (fracHeatX α r ψ : L2C) (fracHeatX α τ ψ : L2C),
    Lp.coeFn_smul (r - τ) (-(aHeatX α τ ψ : L2C)), Lp.coeFn_neg (aHeatX α τ ψ : L2C)]
    with ξ h_a h_b h_c s1 s2 s3 s4
  rw [s1, Pi.sub_apply, s2, Pi.sub_apply, s3, Pi.smul_apply, s4, Pi.neg_apply, h_a, h_b, h_c,
    smul_neg, sub_neg_eq_add, smul_smul, ← sub_smul, ← add_smul, norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [heatF_pos_eq hr0, heatF_pos_eq hτ]
  exact heat_expansion hτ hr (powNorm_nonneg α ξ)

set_option maxHeartbeats 1000000 in
theorem frac_heat_hasDerivAt {α τ : ℝ} (hα : 0 < α) (hH : FracHeatSemigroup α) (hτ : 0 < τ)
    (ψ : X) : HasDerivAt (fun r => fracHeatX α r ψ) (-(aHeatX α τ ψ)) τ := by
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun r => ‖r - τ‖ ^ 2) ?_
    (Asymptotics.isLittleO_pow_sub_sub τ one_lt_two)
  refine Asymptotics.IsBigO.of_bound (16 / τ ^ 2 * ‖ψ‖) ?_
  have hev : ∀ᶠ r in nhds τ, |r - τ| ≤ τ / 2 := by
    filter_upwards [Metric.ball_mem_nhds τ (half_pos hτ)] with r hr
    rw [Metric.mem_ball, Real.dist_eq] at hr
    exact hr.le
  filter_upwards [hev] with r hr
  have := frac_heat_expansion_norm hα hH hτ hr ψ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), sq_abs]
  refine this.trans (le_of_eq ?_)
  ring

end Breakdown.FracInternal.MildWeak
