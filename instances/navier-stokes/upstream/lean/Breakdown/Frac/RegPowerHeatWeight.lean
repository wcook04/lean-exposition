import Breakdown.Frac.StSpaceReg

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem weightSymbol_sq (α τ : ℝ) (ξ : Space) :
    powerHeatSymbol α τ ξ ^ 2 = Real.exp (-((2 * (2 * π * ‖ξ‖) ^ (2 * α)) * τ)) := by
  unfold powerHeatSymbol
  rw [sq, ← Real.exp_add]
  congr 1
  ring

private theorem weightSymbol_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ powerHeatSymbol α τ ξ :=
  (Real.exp_pos _).le

private theorem integral_expDecayWeight {a t c : ℝ} (hc : c ≠ 0) :
    ∫ s in a..t, Real.exp (-(c * (t - s))) = (1 - Real.exp (-(c * (t - a)))) / c := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => Real.exp (-(c * (t - s))) / c)]
  · simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
    ring
  · intro s _
    have h0 : HasDerivAt (fun s : ℝ => -(c * (t - s))) (-(c * (0 - 1))) s :=
      (((hasDerivAt_const s t).sub (hasDerivAt_id' s)).const_mul c).neg
    have h1 : HasDerivAt (fun s : ℝ => -(c * (t - s))) c s := h0.congr_deriv (by ring)
    exact ((h1.exp).div_const c).congr_deriv (by field_simp)
  · exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-(c * (t - s)))).intervalIntegrable _ _

theorem powerHeatWeight (α : ℝ) (hα : 1 < α) : PowerHeatWeightStatement α := by
  refine ⟨2, fun a t hat ht1 ξ => ?_⟩
  have hvol : volume (Ioc a t) ≤ 1 := by
    rw [Real.volume_Ioc, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rcases le_or_gt ‖ξ‖ 1 with hξ | hξ
  · have hpt : ∀ s ∈ Ioc a t, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) * powerHeatSymbol α (t - s) ξ ^ 2) ≤
        ENNReal.ofReal 2 := by
      intro s hs
      refine ENNReal.ofReal_le_ofReal ?_
      have hP : powerHeatSymbol α (t - s) ξ ^ 2 ≤ 1 := by
        rw [weightSymbol_sq, Real.exp_le_one_iff]
        have hts : 0 ≤ t - s := by linarith [hs.2]
        have : 0 ≤ (2 * (2 * π * ‖ξ‖) ^ (2 * α)) * (t - s) := by positivity
        linarith
      have h2 : ‖ξ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ξ]
      have hP0 : 0 ≤ powerHeatSymbol α (t - s) ξ ^ 2 := by positivity
      nlinarith
    calc _ ≤ ∫⁻ s in Ioc a t, ENNReal.ofReal 2 := setLIntegral_mono' measurableSet_Ioc hpt
      _ = ENNReal.ofReal 2 * volume (Ioc a t) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal 2 * 1 := by gcongr
      _ = ENNReal.ofReal 2 := mul_one _
  · have hb0 : 0 < 2 * π * ‖ξ‖ := by nlinarith [Real.pi_gt_three]
    have hbase : 1 ≤ 2 * π * ‖ξ‖ := by nlinarith [Real.pi_gt_three]
    have hLge : (2 * π * ‖ξ‖) ^ 2 ≤ (2 * π * ‖ξ‖) ^ (2 * α) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hbase (by push_cast; linarith)
    have hLpos : 0 < (2 * π * ‖ξ‖) ^ (2 * α) := Real.rpow_pos_of_pos hb0 _
    set c := 2 * (2 * π * ‖ξ‖) ^ (2 * α) with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    have hpt : ∀ s ∈ Ioc a t, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) * powerHeatSymbol α (t - s) ξ ^ 2) ≤
        ENNReal.ofReal (2 * ‖ξ‖ ^ 2 * Real.exp (-(c * (t - s)))) := by
      intro s _
      refine ENNReal.ofReal_le_ofReal ?_
      rw [weightSymbol_sq]
      have h2 : 1 ≤ ‖ξ‖ ^ 2 := by nlinarith
      nlinarith [Real.exp_pos (-(c * (t - s)))]
    have hint : IntegrableOn (fun s => 2 * ‖ξ‖ ^ 2 * Real.exp (-(c * (t - s)))) (Ioc a t) :=
      ((by fun_prop : Continuous fun s : ℝ => 2 * ‖ξ‖ ^ 2 * Real.exp (-(c * (t - s)))).integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    refine (setLIntegral_mono' measurableSet_Ioc hpt).trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun s => by positivity),
      ← intervalIntegral.integral_of_le hat, intervalIntegral.integral_const_mul,
      integral_expDecayWeight hcpos.ne']
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_div_assoc, div_le_iff₀ hcpos]
    have hpi : 1 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    have he := Real.exp_pos (-(c * (t - a)))
    have hsq : (2 * π * ‖ξ‖) ^ 2 = 4 * π ^ 2 * ‖ξ‖ ^ 2 := by ring
    rw [hsq] at hLge
    nlinarith [sq_nonneg ‖ξ‖]

private theorem rpow_half_sq_weight (A : ℝ≥0∞) : (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem powerHeatIntegral_of (α : ℝ) (hα : 1 < α) (h1 : PowerHeatWeightStatement α) :
    PowerHeatIntegralStatement α := by
  obtain ⟨C, hC⟩ := h1
  refine ⟨C, fun n a t hat ht1 N hN K hK => ?_⟩
  have hNs : ∀ ξ, Measurable (fun s => N s ξ) := fun ξ => hN.comp (measurable_id.prodMk measurable_const)
  have hpt : ∀ ξ, ENNReal.ofReal (hsWeight (n + 1) ξ) *
      ‖∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • N s ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal C * ∫⁻ s in Ioc a t, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 := by
    intro ξ
    have hx : 0 ≤ 1 + ‖ξ‖ ^ 2 := by positivity
    have hw : 0 ≤ hsWeight n ξ := by unfold hsWeight; positivity
    have hw1 : hsWeight (n + 1) ξ = (1 + ‖ξ‖ ^ 2) * hsWeight n ξ := by unfold hsWeight; ring
    set f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.sqrt (1 + ‖ξ‖ ^ 2) * powerHeatSymbol α (t - s) ξ) with hf
    set g : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.sqrt (hsWeight n ξ)) * ‖N s ξ‖ₑ with hg
    have hfg : ∀ s, ENNReal.ofReal (Real.sqrt (hsWeight (n + 1) ξ)) *
        (ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * ‖N s ξ‖ₑ) = (f * g) s := by
      intro s
      simp only [hf, hg, Pi.mul_apply]
      rw [hw1, Real.sqrt_mul hx, ENNReal.ofReal_mul (Real.sqrt_nonneg _),
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      ring
    have hI : ‖∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • N s ξ‖ₑ ≤
        ∫⁻ s in Ioc a t, ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * ‖N s ξ‖ₑ := by
      rw [intervalIntegral.integral_of_le hat]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun s => ?_
      rw [enorm_smul, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (weightSymbol_nonneg _ _ _)]
    have hfm : AEMeasurable f (volume.restrict (Ioc a t)) :=
      (ENNReal.continuous_ofReal.comp (by unfold powerHeatSymbol; fun_prop :
        Continuous fun s : ℝ => Real.sqrt (1 + ‖ξ‖ ^ 2) * powerHeatSymbol α (t - s) ξ)).measurable.aemeasurable
    have hgm : AEMeasurable g (volume.restrict (Ioc a t)) :=
      ((hNs ξ).enorm.const_mul _).aemeasurable
    have hCst := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc a t))
      Real.HolderConjugate.two_two hfm hgm
    have hf2 : ∫⁻ s in Ioc a t, f s ^ (2 : ℝ) ≤ ENNReal.ofReal C := by
      refine le_trans (le_of_eq ?_) (hC a t hat ht1 ξ)
      refine lintegral_congr fun s => ?_
      simp only [hf, ENNReal.rpow_two]
      rw [← ENNReal.ofReal_pow (by have := weightSymbol_nonneg α (t - s) ξ; positivity), mul_pow,
        Real.sq_sqrt hx]
    have hg2 : ∫⁻ s in Ioc a t, g s ^ (2 : ℝ) =
        ∫⁻ s in Ioc a t, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 := by
      refine lintegral_congr fun s => ?_
      simp only [hg, ENNReal.rpow_two]
      rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hw]
    calc ENNReal.ofReal (hsWeight (n + 1) ξ) *
          ‖∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • N s ξ‖ₑ ^ 2
        = (ENNReal.ofReal (Real.sqrt (hsWeight (n + 1) ξ)) *
          ‖∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • N s ξ‖ₑ) ^ 2 := by
          rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
            Real.sq_sqrt (by unfold hsWeight; positivity)]
      _ ≤ (ENNReal.ofReal (Real.sqrt (hsWeight (n + 1) ξ)) *
          ∫⁻ s in Ioc a t, ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * ‖N s ξ‖ₑ) ^ 2 := by
          gcongr
      _ = (∫⁻ s in Ioc a t, (f * g) s) ^ 2 := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_congr hfg
      _ ≤ ((∫⁻ s in Ioc a t, f s ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ s in Ioc a t, g s ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by
          gcongr
      _ = (∫⁻ s in Ioc a t, f s ^ (2 : ℝ)) * (∫⁻ s in Ioc a t, g s ^ (2 : ℝ)) := by
          rw [mul_pow, rpow_half_sq_weight, rpow_half_sq_weight]
      _ ≤ ENNReal.ofReal C * ∫⁻ s in Ioc a t, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 := by
          rw [hg2]
          gcongr
  have hmeas : AEMeasurable (Function.uncurry fun (ξ : Space) (s : ℝ) =>
      ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2) (volume.prod (volume.restrict (Ioc a t))) := by
    have h1 : Measurable fun p : Space × ℝ => ENNReal.ofReal (hsWeight n p.1) :=
      ENNReal.measurable_ofReal.comp ((by unfold hsWeight; fun_prop :
        Continuous fun ξ : Space => hsWeight n ξ).measurable.comp measurable_fst)
    have h2 : Measurable fun p : Space × ℝ => ‖N p.2 p.1‖ₑ ^ 2 :=
      (hN.comp (measurable_snd.prodMk measurable_fst)).enorm.pow_const 2
    exact (h1.mul h2).aemeasurable
  calc hsNormSq (n + 1) (fun ξ => ∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • N s ξ)
      ≤ ∫⁻ ξ, ENNReal.ofReal C * ∫⁻ s in Ioc a t, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 :=
        lintegral_mono hpt
    _ = ENNReal.ofReal C * ∫⁻ s in Ioc a t, hsNormSq n (N s) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hmeas]
        rfl
    _ ≤ ENNReal.ofReal C * ∫⁻ s in Ioc a t, K := by
        gcongr ENNReal.ofReal C * ?_
        exact setLIntegral_mono' measurableSet_Ioc hK
    _ = ENNReal.ofReal C * ENNReal.ofReal (t - a) * K := by
        rw [setLIntegral_const, Real.volume_Ioc]
        ring

end Breakdown.SmoothFlow
