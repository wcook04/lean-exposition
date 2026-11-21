import Breakdown.Frac.StRealize
import Breakdown.FreqTr.FieldOp

open MeasureTheory Set Real
open scoped ENNReal ContDiff Nat

noncomputable section

namespace Breakdown.Freq

namespace FracInternal.BilinShiftCont

def scalarMul (m : Space → ℝ) : Space → CSpace →L[ℝ] CSpace :=
  fun ξ => m ξ • ContinuousLinearMap.id ℝ CSpace

theorem realized_ae {T : L2C →L[ℝ] L2C} {m : Space → ℝ} (hT : IsRealizedBy T id (scalarMul m))
    (f : L2C) : (T f : Space → CSpace) =ᵐ[volume] fun ξ => m ξ • (f : Space → CSpace) ξ := by
  filter_upwards [hT f] with ξ h
  simpa [scalarMul] using h

theorem realized_of_ae {T : L2C →L[ℝ] L2C} {m : Space → ℝ}
    (h : ∀ f : L2C, (T f : Space → CSpace) =ᵐ[volume] fun ξ => m ξ • (f : Space → CSpace) ξ) :
    IsRealizedBy T id (scalarMul m) := by
  intro f
  filter_upwards [h f] with ξ hξ
  simpa [scalarMul] using hξ

theorem bounded_realized {m : Space → ℝ} (hm : Measurable m) {C : ℝ} (hC : ∀ ξ, |m ξ| ≤ C) :
    IsRealizedBy (fieldOp id (scalarMul m)) id (scalarMul m) := by
  have hF : AEStronglyMeasurable (scalarMul m) volume :=
    hm.aestronglyMeasurable.smul aestronglyMeasurable_const
  have hB : ∀ ξ, ‖scalarMul m ξ‖ ≤ C := by
    intro ξ
    calc ‖scalarMul m ξ‖ ≤ ‖m ξ‖ * ‖ContinuousLinearMap.id ℝ CSpace‖ := norm_smul_le _ _
      _ ≤ |m ξ| * 1 := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)
      _ ≤ C := by rw [mul_one]; exact hC ξ
  exact isRealizedBy_fieldOp (ContinuousLinearEquiv.refl ℝ Space) ContinuousLinearEquiv.coe_refl' hF hB

theorem heat_eq (α s : ℝ) : fracHeatL2 α s = fieldOp id (scalarMul (fracHeatFactor α s)) := rfl

theorem heat_realized (α s : ℝ) :
    IsRealizedBy (fracHeatL2 α s) id (scalarMul (fracHeatFactor α s)) := by
  rw [heat_eq]
  refine bounded_realized (C := 1) (by unfold fracHeatFactor; fun_prop) fun ξ => ?_
  unfold fracHeatFactor
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  have := le_max_right s 0
  positivity

theorem phi_measurable (α τ : ℝ) : Measurable (fracPhiFactor α τ) := by
  unfold fracPhiFactor; fun_prop

theorem phi_mul_heat (α τ : ℝ) {s : ℝ} (hs : 0 ≤ s) (ξ : Space) :
    fracPhiFactor α τ ξ * fracHeatFactor α s ξ = fracPhiFactor α (s + τ) ξ := by
  unfold fracPhiFactor fracHeatFactor
  rw [max_eq_left hs, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem phi_bound {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (ξ : Space) :
    |fracPhiFactor α τ ξ| ≤ 1 + ((⌈1 / (2 * α)⌉₊)! : ℝ) / τ ^ ⌈1 / (2 * α)⌉₊ := by
  set n := ⌈1 / (2 * α)⌉₊ with hn
  unfold fracPhiFactor
  set a := 2 * π * ‖ξ‖ with ha
  have ha0 : 0 ≤ a := by positivity
  have hE : 0 < Real.exp (-(τ * a ^ (2 * α))) := Real.exp_pos _
  have hE1 : Real.exp (-(τ * a ^ (2 * α))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  have hF : 0 ≤ ((n)! : ℝ) / τ ^ n := by positivity
  rw [abs_of_nonneg (by positivity)]
  rcases le_or_gt a 1 with h1 | h1
  · calc a * Real.exp (-(τ * a ^ (2 * α))) ≤ a * 1 := mul_le_mul_of_nonneg_left hE1 ha0
      _ ≤ 1 + ((n)! : ℝ) / τ ^ n := by linarith
  · have hb : a ≤ (a ^ (2 * α)) ^ n := by
      have hn1 : 1 ≤ 2 * α * n := by
        have h := Nat.le_ceil (1 / (2 * α))
        rw [← hn, div_le_iff₀ (by positivity)] at h
        linarith
      calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
        _ ≤ a ^ (2 * α * n) := Real.rpow_le_rpow_of_exponent_le h1.le hn1
        _ = (a ^ (2 * α)) ^ n := by rw [Real.rpow_mul ha0, Real.rpow_natCast]
    set x := τ * a ^ (2 * α) with hxdef
    have hx0 : 0 ≤ x := by positivity
    have hxn : x ^ n * Real.exp (-x) ≤ n ! := by
      have h := Real.pow_div_factorial_le_exp x hx0 n
      rw [div_le_iff₀ (by positivity)] at h
      calc x ^ n * Real.exp (-x) ≤ (Real.exp x * n !) * Real.exp (-x) :=
            mul_le_mul_of_nonneg_right h hE.le
        _ = n ! := by
            rw [mul_comm (Real.exp x), mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
              mul_one]
    have hxe : (a ^ (2 * α)) ^ n = x ^ n / τ ^ n := by
      rw [hxdef, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hτ.ne')]
    calc a * Real.exp (-x) ≤ (a ^ (2 * α)) ^ n * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hb hE.le
      _ = (x ^ n * Real.exp (-x)) / τ ^ n := by rw [hxe]; ring
      _ ≤ (n ! : ℝ) / τ ^ n := by gcongr
      _ ≤ 1 + ((n)! : ℝ) / τ ^ n := by linarith

def lowPart (α τ : ℝ) (ξ : Space) : ℝ :=
  fracPhiFactor α τ ξ * (if 2 * π * ‖ξ‖ ≤ 1 then 1 else 0)

def highPart (α s : ℝ) (ξ : Space) : ℝ :=
  Real.exp (s * (2 * π * ‖ξ‖) ^ (2 * α)) * (1 - if 2 * π * ‖ξ‖ ≤ 1 then 1 else 0)

theorem cut_measurable : Measurable (fun ξ : Space => if 2 * π * ‖ξ‖ ≤ 1 then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const measurable_const

theorem lowPart_measurable (α τ : ℝ) : Measurable (lowPart α τ) :=
  (phi_measurable α τ).mul cut_measurable

theorem highPart_measurable (α s : ℝ) : Measurable (highPart α s) :=
  (by fun_prop : Measurable fun ξ : Space => Real.exp (s * (2 * π * ‖ξ‖) ^ (2 * α))).mul
    (measurable_const.sub cut_measurable)

theorem lowPart_bound (α : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (ξ : Space) : |lowPart α τ ξ| ≤ 1 := by
  unfold lowPart fracPhiFactor
  by_cases h : 2 * π * ‖ξ‖ ≤ 1
  · rw [if_pos h, mul_one, abs_of_nonneg (by positivity)]
    have hE : Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]; positivity
    calc 2 * π * ‖ξ‖ * Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α)))
        ≤ 2 * π * ‖ξ‖ * 1 := mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ 1 := by linarith
  · rw [if_neg h, mul_zero, abs_zero]; exact zero_le_one

theorem highPart_bound {α s : ℝ} (hα : α ≤ 0) (hs : 0 ≤ s) (ξ : Space) :
    |highPart α s ξ| ≤ Real.exp s := by
  unfold highPart
  by_cases h : 2 * π * ‖ξ‖ ≤ 1
  · rw [if_pos h, sub_self, mul_zero, abs_zero]; exact (Real.exp_pos s).le
  · rw [if_neg h, sub_zero, mul_one, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    have hb : (2 * π * ‖ξ‖) ^ (2 * α) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt (not_le.mp h)) (by linarith)
    exact mul_le_of_le_one_right hs hb

theorem split_eq (α τ : ℝ) {s : ℝ} (ξ : Space) :
    fracPhiFactor α τ ξ = lowPart α τ ξ + fracPhiFactor α (s + τ) ξ * highPart α s ξ := by
  have e : fracPhiFactor α (s + τ) ξ * Real.exp (s * (2 * π * ‖ξ‖) ^ (2 * α)) =
      fracPhiFactor α τ ξ := by
    unfold fracPhiFactor
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  unfold lowPart highPart
  linear_combination (-(1 - if 2 * π * ‖ξ‖ ≤ 1 then (1 : ℝ) else 0)) * e

theorem realized_of_shift {α s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) {T : L2C →L[ℝ] L2C}
    (hT : IsRealizedBy T id (scalarMul (fracPhiFactor α (s + τ)))) :
    ∃ T', IsRealizedBy T' id (scalarMul (fracPhiFactor α τ)) := by
  rcases lt_or_ge 0 α with hα | hα
  · exact ⟨_, bounded_realized (phi_measurable α τ) (phi_bound hα hτ)⟩
  · have h1 := bounded_realized (lowPart_measurable α τ) (lowPart_bound α hτ.le)
    have h2 := bounded_realized (highPart_measurable α s) (highPart_bound hα hs)
    refine ⟨fieldOp id (scalarMul (lowPart α τ)) + T ∘L fieldOp id (scalarMul (highPart α s)),
      realized_of_ae fun f => ?_⟩
    change ((fieldOp id (scalarMul (lowPart α τ)) f +
      T (fieldOp id (scalarMul (highPart α s)) f) : L2C) : Space → CSpace) =ᵐ[volume] _
    filter_upwards [Lp.coeFn_add (fieldOp id (scalarMul (lowPart α τ)) f)
        (T (fieldOp id (scalarMul (highPart α s)) f)), realized_ae h1 f,
      realized_ae hT (fieldOp id (scalarMul (highPart α s)) f), realized_ae h2 f]
      with ξ e0 e1 e2 e3
    rw [e0, Pi.add_apply, e1, e2, e3, smul_smul, ← add_smul, ← split_eq]

theorem phi_heat (α : ℝ) {s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) (f : L2C) :
    fieldOp id (scalarMul (fracPhiFactor α τ)) (fracHeatL2 α s f) =
      fieldOp id (scalarMul (fracPhiFactor α (s + τ))) f := by
  by_cases hA : ∃ T, IsRealizedBy T id (scalarMul (fracPhiFactor α τ))
  · obtain ⟨T, hT⟩ := hA
    have hH := heat_realized α s
    have hB : IsRealizedBy (T ∘L fracHeatL2 α s) id (scalarMul (fracPhiFactor α (s + τ))) :=
      realized_of_ae fun g => by
        filter_upwards [realized_ae hT (fracHeatL2 α s g), realized_ae hH g] with ξ e1 e2
        rw [ContinuousLinearMap.comp_apply, e1, e2, smul_smul, phi_mul_heat α τ hs]
    rw [fieldOp_eq_of_isRealizedBy hB, fieldOp_eq_of_isRealizedBy hT]
    rfl
  · have hB : ¬ ∃ T, IsRealizedBy T id (scalarMul (fracPhiFactor α (s + τ))) :=
      fun ⟨_, hT⟩ => hA (realized_of_shift hs hτ hT)
    have e1 : fieldOp id (scalarMul (fracPhiFactor α τ)) = 0 := by
      unfold fieldOp; exact dif_neg hA
    have e2 : fieldOp id (scalarMul (fracPhiFactor α (s + τ))) = 0 := by
      unfold fieldOp; exact dif_neg hB
    rw [e1, e2]
    rfl

theorem phiX_heatX {α : ℝ} (h2 : FracHeatSemigroup α) {s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ)
    (ψ : X) : fracPhiX α τ (fracHeatX α s ψ) = fracPhiX α (s + τ) ψ := by
  have e1 : fracPhiX α τ (fracHeatX α s ψ) =
      toPhys (fieldOp id (scalarMul (fracPhiFactor α τ)) ((fracHeatX α s ψ : X) : L2C)) := rfl
  have e2 : fracPhiX α (s + τ) ψ =
      toPhys (fieldOp id (scalarMul (fracPhiFactor α (s + τ))) (ψ : L2C)) := rfl
  rw [e1, e2, h2.2.2.2.2.2 s ψ, phi_heat α hs hτ]

theorem bilinX_spec {α : ℝ} (h1 : FracBilinExists α) {τ : ℝ} (hτ : 0 < τ) :
    FracBilinSpec α τ (fracBilinX α τ) := by
  have h : 0 < τ ∧ ∃ B, FracBilinSpec α τ B := ⟨hτ, h1 τ hτ⟩
  rw [fracBilinX, dif_pos h]
  exact h.2.choose_spec

end FracInternal.BilinShiftCont

open FracInternal.BilinShiftCont in
theorem fracBilinShift (α : ℝ) (h1 : FracBilinExists α) (h2 : FracHeatSemigroup α) :
    FracBilinShift α := by
  intro s τ hs hτ u v
  have hst : 0 < s + τ := by linarith
  apply ext_inner_right ℝ
  intro ψ
  rw [h2.2.2.2.2.1 s, bilinX_spec h1 hτ, bilinX_spec h1 hst, fracBilinForm, fracBilinForm,
    phiX_heatX h2 hs hτ]

theorem fracBilinContinuous (α : ℝ) (_hα : 1 < α) (h1 : FracBilinExists α)
    (_h2 : FracBilinBound α) (_h3 : FracPhiBounds α) (_h4 : FracPhiVelocity α)
    (h5 : FracHeatSemigroup α) : FracBilinContinuous α := by
  intro u v τ₀ hτ₀
  have hτ : (0 : ℝ) < τ₀ := hτ₀
  have hs : 0 < τ₀ / 2 := by positivity
  have hc : ContinuousAt (fun t => fracHeatX α t (fracBilinX α (τ₀ / 2) u v)) (τ₀ - τ₀ / 2) :=
    (h5.2.2.2.1 (fracBilinX α (τ₀ / 2) u v)).continuousAt (Ici_mem_nhds (by linarith))
  have hcont : ContinuousAt (fun τ => fracHeatX α (τ - τ₀ / 2) (fracBilinX α (τ₀ / 2) u v)) τ₀ :=
    ContinuousAt.comp_of_eq (g := fun t => fracHeatX α t (fracBilinX α (τ₀ / 2) u v))
      (f := fun τ => τ - τ₀ / 2) hc (continuous_sub_right (τ₀ / 2)).continuousAt rfl
  have heq : (fun τ => fracHeatX α (τ - τ₀ / 2) (fracBilinX α (τ₀ / 2) u v)) =ᶠ[nhds τ₀]
      (fun τ => fracBilinX α τ u v) := by
    filter_upwards [Ioi_mem_nhds (show τ₀ / 2 < τ₀ by linarith)] with τ hτ'
    have hlt : τ₀ / 2 < τ := hτ'
    have hd : 0 ≤ τ - τ₀ / 2 := by linarith
    have e : τ - τ₀ / 2 + τ₀ / 2 = τ := by ring
    exact (fracBilinShift α h1 h5 _ _ hd hs u v).trans (congrArg (fun r => fracBilinX α r u v) e)
  exact (hcont.congr heq).continuousWithinAt

end Breakdown.Freq
