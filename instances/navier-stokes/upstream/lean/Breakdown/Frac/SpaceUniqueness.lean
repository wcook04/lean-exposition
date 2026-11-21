import Breakdown.Frac.StSpace
import Breakdown.Uniqueness.LocalEnergyAuxTime

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.FracInternal.SpaceUniqueness

open Breakdown.Internal.CutoffEnergy

theorem lintegral_norm_sub_sq_le {f g : Space → Space} {a b : ℝ} (hfc : Continuous f)
    (hf : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ≤ ENNReal.ofReal a)
    (hg : ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ≤ ENNReal.ofReal b) :
    ∫⁻ x, ENNReal.ofReal (‖g x - f x‖ ^ 2) ≤ ENNReal.ofReal (2 * |a| + 2 * |b|) := by
  have hmf : Measurable (fun x => ENNReal.ofReal (2 * ‖f x‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hfc.norm.pow 2).const_mul 2).measurable
  have hpt : ∀ x, ENNReal.ofReal (‖g x - f x‖ ^ 2) ≤
      ENNReal.ofReal (2 * ‖f x‖ ^ 2) + ENNReal.ofReal (2 * ‖g x‖ ^ 2) := by
    intro x
    have h1 : ‖g x - f x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2 := by
      have := norm_sub_le (g x) (f x)
      nlinarith [mul_self_le_mul_self (norm_nonneg _) this, sq_nonneg (‖g x‖ - ‖f x‖)]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1
  have hsc : ∀ h : Space → Space, (∫⁻ x, ENNReal.ofReal (2 * ‖h x‖ ^ 2)) =
      ENNReal.ofReal 2 * ∫⁻ x, ENNReal.ofReal (‖h x‖ ^ 2) := by
    intro h
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
  have h2a : ENNReal.ofReal 2 * ENNReal.ofReal a ≤ ENNReal.ofReal (2 * |a|) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [le_abs_self a])
  have h2b : ENNReal.ofReal 2 * ENNReal.ofReal b ≤ ENNReal.ofReal (2 * |b|) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [le_abs_self b])
  calc ∫⁻ x, ENNReal.ofReal (‖g x - f x‖ ^ 2)
      ≤ ∫⁻ x, (ENNReal.ofReal (2 * ‖f x‖ ^ 2) + ENNReal.ofReal (2 * ‖g x‖ ^ 2)) :=
        lintegral_mono hpt
    _ = (∫⁻ x, ENNReal.ofReal (2 * ‖f x‖ ^ 2)) + ∫⁻ x, ENNReal.ofReal (2 * ‖g x‖ ^ 2) :=
        lintegral_add_left hmf _
    _ = ENNReal.ofReal 2 * (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) +
        ENNReal.ofReal 2 * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) := by rw [hsc f, hsc g]
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal a + ENNReal.ofReal 2 * ENNReal.ofReal b := by
        gcongr
    _ ≤ ENNReal.ofReal (2 * |a|) + ENNReal.ofReal (2 * |b|) := add_le_add h2a h2b
    _ = ENNReal.ofReal (2 * |a| + 2 * |b|) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

theorem le_of_hasDerivAt_le_linear {T L c : ℝ} {y D : ℝ → ℝ} (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (hD : ∀ τ ∈ Ioo 0 T, HasDerivAt y (D τ) τ)
    (hb : ∀ τ ∈ Ioo 0 T, D τ ≤ L * y τ + c) (h0 : y 0 = 0) :
    ∀ t ∈ Icc 0 T, y t ≤ exp (|L| * T) * exp (|L| * T) * T * |c| := by
  intro t ht
  set C := exp (|L| * T) * |c| with hC
  have hC0 : 0 ≤ C := by positivity
  have hexp : ∀ τ ∈ Icc 0 T, exp (-L * τ) ≤ exp (|L| * T) ∧ exp (L * τ) ≤ exp (|L| * T) := by
    intro τ hτ
    have h1 : |L| * τ ≤ |L| * T := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg L)
    constructor
    · apply exp_le_exp.2
      have : -L * τ ≤ |L| * τ := mul_le_mul_of_nonneg_right (neg_le_abs L) hτ.1
      linarith
    · apply exp_le_exp.2
      have : L * τ ≤ |L| * τ := mul_le_mul_of_nonneg_right (le_abs_self L) hτ.1
      linarith
  have hanti : AntitoneOn (fun τ => exp (-L * τ) * y τ - C * τ) (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (f' := fun τ => exp (-L * τ) * (D τ - L * y τ) - C) ?_ ?_ ?_
    · exact ((continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hy).sub
        (continuous_const.mul continuous_id).continuousOn
    · intro τ hτ
      rw [interior_Icc] at hτ
      have h1 : HasDerivAt (fun τ => exp (-L * τ)) (exp (-L * τ) * (-L)) τ := by
        have := ((hasDerivAt_id τ).const_mul (-L)).exp
        simpa using this
      have h2 := (h1.mul (hD τ hτ)).sub ((hasDerivAt_id τ).const_mul C)
      refine (h2.congr_deriv ?_).hasDerivWithinAt
      ring
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hτ' := Ioo_subset_Icc_self hτ
      have e1 := (hexp τ hτ').1
      have hpos : 0 < exp (-L * τ) := exp_pos _
      have hb' : D τ - L * y τ ≤ |c| := by linarith [hb τ hτ, le_abs_self c]
      have h3 : exp (-L * τ) * (D τ - L * y τ) ≤ exp (-L * τ) * |c| :=
        mul_le_mul_of_nonneg_left hb' hpos.le
      have h4 : exp (-L * τ) * |c| ≤ exp (|L| * T) * |c| :=
        mul_le_mul_of_nonneg_right e1 (abs_nonneg c)
      show exp (-L * τ) * (D τ - L * y τ) - C ≤ 0
      rw [hC]
      linarith
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hg := hanti h0mem ht ht.1
  simp only [mul_zero, exp_zero, h0, sub_zero] at hg
  have hyt : y t = exp (L * t) * (exp (-L * t) * y t) := by
    rw [← mul_assoc, ← exp_add, show L * t + -L * t = 0 by ring, exp_zero, one_mul]
  rw [hyt]
  have e2 := (hexp t ht).2
  have hCt : C * t ≤ C * T := mul_le_mul_of_nonneg_left ht.2 hC0
  calc exp (L * t) * (exp (-L * t) * y t) ≤ exp (L * t) * (C * t) :=
        mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
    _ ≤ exp (|L| * T) * (C * T) := mul_le_mul e2 hCt (mul_nonneg hC0 ht.1) (exp_pos _).le
    _ = exp (|L| * T) * exp (|L| * T) * T * |c| := by rw [hC]; ring

theorem cutoffPow_mono {R r : ℝ} (hR : 0 < R) (hRr : R ≤ r) (x : Space) :
    cutoffPow R x ≤ cutoffPow r x := by
  have h1 : ‖x‖ / r ≤ ‖x‖ / R := div_le_div_of_nonneg_left (norm_nonneg x) hR hRr
  have h2 : radialCutoff R x ≤ radialCutoff r x :=
    Real.smoothTransition.monotone (by linarith)
  exact pow_le_pow_left₀ (radialCutoff_nonneg R x) h2 4


theorem memLp_two_of_lintegral {f : Space → Space} (hf : Continuous f) {a : ℝ}
    (h : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ≤ ENNReal.ofReal a) : MemLp f 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable]
  refine ⟨(hf.norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by positivity)]
  exact h.trans_lt ENNReal.ofReal_lt_top

theorem power_sub_eq (h6 : AdditivityStatement) (h7 : RemainderIntegrableStatement) {α : ℝ}
    (hα1 : 1 < α) (hα2 : α < 3 / 2) {f g : Space → Space} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfL : MemLp f 2 volume) (hgL : MemLp g 2 volume) (x : Space) :
    fractionalPowerAt α f x - fractionalPowerAt α g x = fractionalPowerAt α (f - g) x := by
  have hd : ContDiff ℝ ∞ (f - g) := hf.sub hg
  have key := h6 α g (f - g) x (h7 α hα1 hα2 g hg (Or.inl hgL) x)
    (h7 α hα1 hα2 (f - g) hd (Or.inl (hfL.sub hgL)) x)
    (hg.differentiable (by simp) x) (hd.differentiable (by simp) x)
    (show ContDiff ℝ 2 g from hg.of_le (by norm_cast)).contDiffAt
    (show ContDiff ℝ 2 (f - g) from hd.of_le (by norm_cast)).contDiffAt
  rw [add_sub_cancel] at key
  rw [key, add_sub_cancel_left]

theorem dissipation_eq (h5 : SymmetryCompactStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2)
    {w : Space → Space} (hw : ContDiff ℝ ∞ w) (hwL : MemLp w 2 volume) {r : ℝ} (hr : 0 < r) :
    (∫ x, cutoffPow r x * inner ℝ (w x) (fractionalPowerAt α w x)) =
      ∫ x, inner ℝ (w x) (fractionalPowerAt α (fun y => cutoffPow r y • w y) x) := by
  have hφ : ContDiff ℝ ∞ (fun y => cutoffPow r y • w y) := (contDiff_cutoffPow hr).smul hw
  have hφc : HasCompactSupport (fun y => cutoffPow r y • w y) :=
    hasCompactSupport_of_cutoffPow hr fun x h => by simp [h]
  obtain ⟨-, -, hsym⟩ := h5 α hα1 hα2 w _ hw (Or.inl hwL) hφ hφc
  rw [← hsym]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_smul_right, real_inner_comm]

end FracInternal.SpaceUniqueness

open FracInternal.SpaceUniqueness Internal.CutoffEnergy in
theorem fracUniqueness_of (h1 : ForcedLocalEnergyStatement) (h2 : ForcedPressureDifferenceStatement)
    (h3 : FracForcedStatement) (h4 : FracDifferenceStatement) (h5 : SymmetryCompactStatement)
    (h6 : AdditivityStatement) (h7 : RemainderIntegrableStatement) : FracUniquenessStatement := by
  intro α hα1 hα5 T u v p q hu hv hEu hEv hB h0 t ht
  have hα2 : α < 3 / 2 := by linarith
  rcases eq_or_lt_of_le ht.1 with h | htpos
  · rw [← h]; exact h0
  have hFu := h3 α hα1 hα2 T u p hu hEu
  have hFv := h3 α hα1 hα2 T v q hv hEv
  obtain ⟨Au, hAu⟩ := id hEu
  obtain ⟨Av, hAv⟩ := id hEv
  obtain ⟨B, hBd⟩ := id hB
  obtain ⟨K, r₀, hr₀, hK⟩ := h4 α hα1 hα5
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hus : ∀ τ ∈ Icc 0 T, ContDiff ℝ ∞ (u τ) := fun τ hτ => contDiff_slice hu.smooth_velocity hτ
  have hvs : ∀ τ ∈ Icc 0 T, ContDiff ℝ ∞ (v τ) := fun τ hτ => contDiff_slice hv.smooth_velocity hτ
  set A := Real.sqrt (2 * |Au| + 2 * |Av|) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA2 : A ^ 2 = 2 * |Au| + 2 * |Av| := Real.sq_sqrt (by positivity)
  have hdata : ∀ τ ∈ Ioo 0 T, IsDifferenceData A B B (u τ) (v τ - u τ) := by
    intro τ hτ
    have hτ' := Ioo_subset_Icc_self hτ
    have hus := hus τ hτ'
    have hvs := hvs τ hτ'
    refine ⟨⟨hvs.sub hus, ?_, hA0, ?_⟩, hus, hu.incompressible τ hτ',
      fun x => (hBd τ hτ' x).1, fun x => (hBd τ hτ' x).2⟩
    · intro x
      have hf : fderiv ℝ (v τ - u τ) x = fderiv ℝ (v τ) x - fderiv ℝ (u τ) x :=
        fderiv_sub (hvs.differentiable (by simp) x) (hus.differentiable (by simp) x)
      have e1 := hv.incompressible τ hτ' x
      have e2 := hu.incompressible τ hτ' x
      unfold divergenceAt at e1 e2 ⊢
      rw [hf]
      simp only [sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib, e1, e2,
        sub_zero]
    · rw [hA2]
      simpa only [Pi.sub_apply] using
        lintegral_norm_sub_sq_le hus.continuous (hAu τ hτ') (hAv τ hτ')
  set M := exp (|2 * B| * T) * exp (|2 * B| * T) * T * |K * (1 + B) * (A ^ 2 + A ^ 6)| with hM
  have hbound : ∀ r : ℝ, r₀ ≤ r → cutoffEnergy r (v t - u t) ≤ M / r := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos (hr₀.trans hr)
    have hderiv : ∀ τ ∈ Ioo 0 T, HasDerivAt (fun τ => cutoffEnergy r (v τ - u τ))
        (fracDifferenceRHS α r (u τ) (v τ - u τ)) τ := by
      intro τ hτ
      have hτ' := Ioo_subset_Icc_self hτ
      have huL := memLp_two_of_lintegral (hus τ hτ').continuous (hAu τ hτ')
      have hvL := memLp_two_of_lintegral (hvs τ hτ').continuous (hAv τ hτ')
      have e1 : (∫ x, cutoffPow r x * inner ℝ (v τ x - u τ x)
          (fractionalPowerAt α (v τ) x - fractionalPowerAt α (u τ) x)) =
          ∫ x, inner ℝ ((v τ - u τ) x)
            (fractionalPowerAt α (fun y => cutoffPow r y • (v τ - u τ) y) x) := by
        rw [← dissipation_eq (w := v τ - u τ) h5 hα1 hα2 ((hvs τ hτ').sub (hus τ hτ')) (hvL.sub huL) hr0]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [power_sub_eq h6 h7 hα1 hα2 (hvs τ hτ') (hus τ hτ') hvL huL x, Pi.sub_apply]
      have hD := (h1 T u v p q _ _ hFu hFv r hr0).2 τ hτ
      rw [h2 T u v p q _ _ hFu hFv hEu hEv r hr0 τ hτ] at hD
      beta_reduce at hD
      rw [e1] at hD
      convert hD using 1
      simp only [fracDifferenceRHS, Pi.sub_apply, add_sub_cancel]
    have hy0 : cutoffEnergy r (v 0 - u 0) = 0 := by
      simp [cutoffEnergy, h0]
    have key := le_of_hasDerivAt_le_linear (L := 2 * B) (c := K * (1 + B) * (A ^ 2 + A ^ 6) / r)
      hT (h1 T u v p q _ _ hFu hFv r hr0).1 hderiv
      (fun τ hτ => hK A B B (u τ) (v τ - u τ) (hdata τ hτ) r hr) hy0 t ht
    rw [abs_div, abs_of_pos hr0] at key
    rw [hM, mul_div_assoc]
    simpa only [mul_div_assoc] using key
  have hw : ContDiff ℝ ∞ (v t - u t) := (hvs t ht).sub (hus t ht)
  have hwc : Continuous (fun x => ‖(v t - u t) x‖ ^ 2) := hw.continuous.norm.pow 2
  funext x₀
  set R := max r₀ ‖x₀‖ with hR
  have hR1 : r₀ ≤ R := le_max_left _ _
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (hr₀.trans hR1)
  have hint : ∀ r : ℝ, 0 < r → Integrable (fun x => cutoffPow r x * ‖(v t - u t) x‖ ^ 2) :=
    fun r hr => integrable_cutoffPow_mul hr hwc
  have hFR : ∀ r : ℝ, R ≤ r →
      (∫ x, cutoffPow R x * ‖(v t - u t) x‖ ^ 2) ≤ 2 * M / r := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hR0 hr
    have h1 : (∫ x, cutoffPow R x * ‖(v t - u t) x‖ ^ 2) ≤
        ∫ x, cutoffPow r x * ‖(v t - u t) x‖ ^ 2 :=
      integral_mono (hint R hR0) (hint r hr0)
        (fun x => mul_le_mul_of_nonneg_right (cutoffPow_mono hR0 hr x) (by positivity))
    have h2 := hbound r (hR1.trans hr)
    unfold cutoffEnergy at h2
    rw [mul_div_assoc]
    linarith
  have htend : Tendsto (fun r : ℝ => 2 * M / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hle : (∫ x, cutoffPow R x * ‖(v t - u t) x‖ ^ 2) ≤ 0 :=
    ge_of_tendsto htend ((eventually_ge_atTop R).mono hFR)
  have hnn : ∀ x, 0 ≤ cutoffPow R x * ‖(v t - u t) x‖ ^ 2 := fun x =>
    mul_nonneg (pow_nonneg (radialCutoff_nonneg R x) 4) (by positivity)
  have hzero : (∫ x, cutoffPow R x * ‖(v t - u t) x‖ ^ 2) = 0 :=
    le_antisymm hle (integral_nonneg hnn)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => hnn x) (hint R hR0)).1 hzero
  have hcont : Continuous (fun x => cutoffPow R x * ‖(v t - u t) x‖ ^ 2) :=
    (contDiff_cutoffPow hR0).continuous.mul hwc
  have hfun := (Continuous.ae_eq_iff_eq volume hcont continuous_zero).1 hae
  have hx := congrFun hfun x₀
  have hone : cutoffPow R x₀ = 1 := by
    simp [cutoffPow, radialCutoff_eq_one hR0 (le_max_right r₀ ‖x₀‖)]
  rw [hone, one_mul, Pi.zero_apply] at hx
  have hw0 : (v t - u t) x₀ = 0 := norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx)
  rw [Pi.sub_apply, sub_eq_zero] at hw0
  exact hw0.symm

end Breakdown
