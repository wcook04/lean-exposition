import Breakdown.Uniqueness.RegLocalAuxSymm

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem heatSymbol_sq (τ : ℝ) (ξ : Space) :
    heatSymbol τ ξ ^ 2 = Real.exp (-(8 * π ^ 2 * τ * ‖ξ‖ ^ 2)) := by
  unfold heatSymbol
  rw [sq, ← Real.exp_add]
  congr 1
  ring

private theorem heatSymbol_nonneg (τ : ℝ) (ξ : Space) : 0 ≤ heatSymbol τ ξ :=
  (Real.exp_pos _).le

private theorem integral_heatKernel {a t : ℝ} (x : ℝ) :
    ∫ s in a..t, x * Real.exp (-(8 * π ^ 2 * (t - s) * x)) =
      (1 - Real.exp (-(8 * π ^ 2 * (t - a) * x))) / (8 * π ^ 2) := by
  have hk : (8 * π ^ 2 : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => Real.exp (-(8 * π ^ 2 * (t - s) * x)) / (8 * π ^ 2))]
  · simp only [sub_self, mul_zero, zero_mul, neg_zero, Real.exp_zero]
    ring
  · intro s _
    have h0 : HasDerivAt (fun s : ℝ => -(8 * π ^ 2 * (t - s) * x)) (-(8 * π ^ 2 * (0 - 1) * x)) s :=
      ((((hasDerivAt_const s t).sub (hasDerivAt_id' s)).const_mul (8 * π ^ 2)).mul_const x).neg
    have h1 : HasDerivAt (fun s : ℝ => -(8 * π ^ 2 * (t - s) * x)) (8 * π ^ 2 * x) s :=
      h0.congr_deriv (by ring)
    exact ((h1.exp).div_const (8 * π ^ 2)).congr_deriv (by rw [div_eq_iff hk]; ring)
  · exact (by fun_prop : Continuous fun s : ℝ => x * Real.exp (-(8 * π ^ 2 * (t - s) * x))).intervalIntegrable _ _

theorem lintegral_heatWeight_le {a t : ℝ} (hat : a ≤ t) (ht1 : t ≤ a + 1) (ξ : Space) :
    ∫⁻ s in Ioc a t, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) * heatSymbol (t - s) ξ ^ 2) ≤ 2 := by
  have hpt : ∀ s ∈ Ioc a t, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) * heatSymbol (t - s) ξ ^ 2) ≤
      1 + ENNReal.ofReal (‖ξ‖ ^ 2 * Real.exp (-(8 * π ^ 2 * (t - s) * ‖ξ‖ ^ 2))) := by
    intro s hs
    rw [heatSymbol_sq]
    have hts : 0 ≤ t - s := by linarith [hs.2]
    have hE : Real.exp (-(8 * π ^ 2 * (t - s) * ‖ξ‖ ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 8 * π ^ 2 * (t - s) * ‖ξ‖ ^ 2 := by positivity
      linarith
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg ‖ξ‖, Real.exp_pos (-(8 * π ^ 2 * (t - s) * ‖ξ‖ ^ 2))]
  refine (setLIntegral_mono' measurableSet_Ioc hpt).trans ?_
  rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul, Real.volume_Ioc]
  have h1 : ENNReal.ofReal (t - a) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hint : IntegrableOn (fun s => ‖ξ‖ ^ 2 * Real.exp (-(8 * π ^ 2 * (t - s) * ‖ξ‖ ^ 2))) (Ioc a t) :=
    ((by fun_prop : Continuous fun s : ℝ => ‖ξ‖ ^ 2 * Real.exp (-(8 * π ^ 2 * (t - s) * ‖ξ‖ ^ 2))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun s => by positivity),
    ← intervalIntegral.integral_of_le hat, integral_heatKernel]
  have h2 : ENNReal.ofReal ((1 - Real.exp (-(8 * π ^ 2 * (t - a) * ‖ξ‖ ^ 2))) / (8 * π ^ 2)) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_one (by positivity)]
    have : 1 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [Real.exp_pos (-(8 * π ^ 2 * (t - a) * ‖ξ‖ ^ 2))]
  calc ENNReal.ofReal (t - a) + ENNReal.ofReal ((1 - Real.exp (-(8 * π ^ 2 * (t - a) * ‖ξ‖ ^ 2))) / (8 * π ^ 2))
      ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

private theorem rpow_half_sq (A : ℝ≥0∞) : (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem hsNormSq_heatIntegral_le (n : ℕ) {a t : ℝ} (hat : a ≤ t) (ht1 : t ≤ a + 1)
    (N : ℝ → Space → CSpace) (hN : Measurable (Function.uncurry N)) (K : ℝ≥0∞)
    (hK : ∀ s ∈ Ioc a t, hsNormSq n (N s) ≤ K) :
    hsNormSq (n + 1) (fun ξ => ∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • N s ξ) ≤
      2 * ENNReal.ofReal (t - a) * K := by
  have hNs : ∀ ξ, Measurable (fun s => N s ξ) := fun ξ => hN.comp (measurable_id.prodMk measurable_const)
  have hpt : ∀ ξ, ENNReal.ofReal (hsWeight (n + 1) ξ) *
      ‖∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • N s ξ‖ₑ ^ 2 ≤
      2 * ∫⁻ s in Ioc a t, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 := by
    intro ξ
    have hx : 0 ≤ 1 + ‖ξ‖ ^ 2 := by positivity
    have hw : 0 ≤ hsWeight n ξ := by unfold hsWeight; positivity
    have hw1 : hsWeight (n + 1) ξ = (1 + ‖ξ‖ ^ 2) * hsWeight n ξ := by unfold hsWeight; ring
    have hI : ‖∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • N s ξ‖ₑ ≤
        ∫⁻ s in Ioc a t, ENNReal.ofReal (heatSymbol (t - s) ξ) * ‖N s ξ‖ₑ := by
      rw [intervalIntegral.integral_of_le hat]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun s => ?_
      rw [enorm_smul, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (heatSymbol_nonneg _ _)]
    set f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.sqrt (1 + ‖ξ‖ ^ 2) * heatSymbol (t - s) ξ) with hf
    set g : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.sqrt (hsWeight n ξ)) * ‖N s ξ‖ₑ with hg
    have hfg : ∀ s, ENNReal.ofReal (Real.sqrt (hsWeight (n + 1) ξ)) *
        (ENNReal.ofReal (heatSymbol (t - s) ξ) * ‖N s ξ‖ₑ) = (f * g) s := by
      intro s
      simp only [hf, hg, Pi.mul_apply]
      rw [hw1, Real.sqrt_mul hx, ENNReal.ofReal_mul (Real.sqrt_nonneg _),
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      ring
    have hfm : AEMeasurable f (volume.restrict (Ioc a t)) :=
      (ENNReal.continuous_ofReal.comp (by unfold heatSymbol; fun_prop :
        Continuous fun s : ℝ => Real.sqrt (1 + ‖ξ‖ ^ 2) * heatSymbol (t - s) ξ)).measurable.aemeasurable
    have hgm : AEMeasurable g (volume.restrict (Ioc a t)) :=
      ((hNs ξ).enorm.const_mul _).aemeasurable
    have hCst := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc a t))
      Real.HolderConjugate.two_two hfm hgm
    have hf2 : ∫⁻ s in Ioc a t, f s ^ (2 : ℝ) ≤ 2 := by
      refine le_trans (le_of_eq ?_) (lintegral_heatWeight_le hat ht1 ξ)
      refine lintegral_congr fun s => ?_
      simp only [hf, ENNReal.rpow_two]
      rw [← ENNReal.ofReal_pow (by have := heatSymbol_nonneg (t - s) ξ; positivity), mul_pow,
        Real.sq_sqrt hx]
    have hg2 : ∫⁻ s in Ioc a t, g s ^ (2 : ℝ) =
        ∫⁻ s in Ioc a t, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 := by
      refine lintegral_congr fun s => ?_
      simp only [hg, ENNReal.rpow_two]
      rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hw]
    calc ENNReal.ofReal (hsWeight (n + 1) ξ) *
          ‖∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • N s ξ‖ₑ ^ 2
        = (ENNReal.ofReal (Real.sqrt (hsWeight (n + 1) ξ)) *
          ‖∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • N s ξ‖ₑ) ^ 2 := by
          rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
            Real.sq_sqrt (by unfold hsWeight; positivity)]
      _ ≤ (ENNReal.ofReal (Real.sqrt (hsWeight (n + 1) ξ)) *
          ∫⁻ s in Ioc a t, ENNReal.ofReal (heatSymbol (t - s) ξ) * ‖N s ξ‖ₑ) ^ 2 := by
          gcongr
      _ = (∫⁻ s in Ioc a t, (f * g) s) ^ 2 := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_congr hfg
      _ ≤ ((∫⁻ s in Ioc a t, f s ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ s in Ioc a t, g s ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by
          gcongr
      _ = (∫⁻ s in Ioc a t, f s ^ (2 : ℝ)) * (∫⁻ s in Ioc a t, g s ^ (2 : ℝ)) := by
          rw [mul_pow, rpow_half_sq, rpow_half_sq]
      _ ≤ 2 * ∫⁻ s in Ioc a t, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 := by
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
  calc hsNormSq (n + 1) (fun ξ => ∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • N s ξ)
      ≤ ∫⁻ ξ, 2 * ∫⁻ s in Ioc a t, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 :=
        lintegral_mono hpt
    _ = 2 * ∫⁻ s in Ioc a t, hsNormSq n (N s) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_lintegral_swap hmeas]
        rfl
    _ ≤ 2 * ∫⁻ s in Ioc a t, K := by
        gcongr 2 * ?_
        exact setLIntegral_mono' measurableSet_Ioc hK
    _ = 2 * ENNReal.ofReal (t - a) * K := by
        rw [setLIntegral_const, Real.volume_Ioc]
        ring

end Breakdown.SmoothFlow
