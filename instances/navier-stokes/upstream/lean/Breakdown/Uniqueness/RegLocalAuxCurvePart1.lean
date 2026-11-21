import Breakdown.Uniqueness.RegLocalAuxSymm
import Breakdown.Uniqueness.RegUniqueAux2
import Breakdown.Uniqueness.RegPersistAux

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def varConstIntegral (a : ℝ) (N : ℝ → Space → CSpace) (t : ℝ) (ξ : Space) : CSpace :=
  ∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • N s ξ

private theorem rpow_two_eq (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

private theorem heat_mul (t s : ℝ) (ξ : Space) :
    heatSymbol (t - s) ξ = heatSymbol t ξ * heatSymbol (-s) ξ := by
  unfold heatSymbol
  rw [← Real.exp_add]
  congr 1
  ring

private theorem heat_sq (τ : ℝ) (ξ : Space) :
    heatSymbol τ ξ ^ 2 = Real.exp (-(8 * π ^ 2 * ‖ξ‖ ^ 2) * τ) := by
  unfold heatSymbol
  rw [sq, ← Real.exp_add]
  congr 1
  ring

private theorem integral_exp_le {a t L : ℝ} (hat : a ≤ t) (hL : 0 ≤ L) :
    (1 + L) * ∫ s in a..t, Real.exp (-(8 * π ^ 2 * L) * (t - s)) ≤ (t - a) + 1 := by
  have hc : Continuous (fun s : ℝ => Real.exp (-(8 * π ^ 2 * L) * (t - s))) := by fun_prop
  have hI1 : ∫ s in a..t, Real.exp (-(8 * π ^ 2 * L) * (t - s)) ≤ t - a := by
    have h := intervalIntegral.integral_mono_on hat (hc.intervalIntegrable (μ := volume) a t)
      (continuous_const.intervalIntegrable (μ := volume) a t) (fun s hs => by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ 8 * π ^ 2 * L * (t - s) := by
          have : 0 ≤ t - s := by linarith [hs.2]
          positivity
        linarith)
    simpa using h
  have hI2 : L * ∫ s in a..t, Real.exp (-(8 * π ^ 2 * L) * (t - s)) ≤ 1 := by
    rcases hL.eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]
      norm_num
    · set c := 8 * π ^ 2 * L with hcdef
      have hcpos : 0 < c := by positivity
      have hderiv : ∀ x ∈ uIcc a t, HasDerivAt (fun s => Real.exp (-c * (t - s)) / c)
          (Real.exp (-c * (t - x))) x := by
        intro x _
        have h1 : HasDerivAt (fun s => -c * (t - s)) (-c * (0 - 1)) x :=
          ((hasDerivAt_const x t).sub (hasDerivAt_id x)).const_mul (-c)
        have h2 := h1.exp.div_const c
        have e : Real.exp (-c * (t - x)) * (-c * (0 - 1)) / c = Real.exp (-c * (t - x)) := by
          rw [show -c * (0 - 1) = c by ring, mul_div_assoc, div_self hcpos.ne', mul_one]
        rw [e] at h2
        exact h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hc.intervalIntegrable a t)]
      have hpi : 0 < π ^ 2 := by positivity
      have hexp : 0 < Real.exp (-c * (t - a)) := Real.exp_pos _
      simp only [sub_self, mul_zero, Real.exp_zero]
      rw [hcdef]
      have hL' : L * ((1 / (8 * π ^ 2 * L)) - Real.exp (-(8 * π ^ 2 * L) * (t - a)) / (8 * π ^ 2 * L))
          = (1 - Real.exp (-(8 * π ^ 2 * L) * (t - a))) / (8 * π ^ 2) := by
        field_simp
      rw [hL']
      rw [div_le_one (by positivity)]
      have : 1 ≤ 8 * π ^ 2 := by nlinarith [Real.pi_gt_three]
      linarith [Real.exp_pos (-(8 * π ^ 2 * L) * (t - a))]
  nlinarith

private theorem enorm_ofReal_heat (τ : ℝ) (ξ : Space) :
    ‖(((heatSymbol τ ξ : ℝ) : ℂ))‖ₑ = ENNReal.ofReal (heatSymbol τ ξ) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (heatSymbol_nonneg _ _)]

private theorem lintegral_heat_sq_le {a t : ℝ} (hat : a ≤ t) (ξ : Space) :
    ENNReal.ofReal (1 + ‖ξ‖ ^ 2) * ∫⁻ s in Ioc a t, ‖(((heatSymbol (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2 ≤
      ENNReal.ofReal ((t - a) + 1) := by
  have hpt : ∀ s, ‖(((heatSymbol (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2 =
      ENNReal.ofReal (Real.exp (-(8 * π ^ 2 * ‖ξ‖ ^ 2) * (t - s))) := by
    intro s
    rw [enorm_ofReal_heat, ← ENNReal.ofReal_pow (heatSymbol_nonneg _ _), heat_sq]
  simp only [hpt]
  have hc : Continuous (fun s : ℝ => Real.exp (-(8 * π ^ 2 * ‖ξ‖ ^ 2) * (t - s))) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal ((hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    (Eventually.of_forall fun s => (Real.exp_pos _).le), ← intervalIntegral.integral_of_le hat,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (integral_exp_le hat (by positivity))

private theorem enorm_varConstIntegral_sq_le {a t : ℝ} (hat : a ≤ t) (N : ℝ → Space → CSpace)
    (ξ : Space) (hm : AEMeasurable (fun s => ‖N s ξ‖ₑ) (volume.restrict (Ioc a t))) :
    ‖varConstIntegral a N t ξ‖ₑ ^ 2 ≤
      (∫⁻ s in Ioc a t, ‖(((heatSymbol (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2) * ∫⁻ s in Ioc a t, ‖N s ξ‖ₑ ^ 2 := by
  have h1 : ‖varConstIntegral a N t ξ‖ₑ ≤
      ∫⁻ s in Ioc a t, ‖(((heatSymbol (t - s) ξ : ℝ) : ℂ))‖ₑ * ‖N s ξ‖ₑ := by
    unfold varConstIntegral
    rw [intervalIntegral.integral_of_le hat]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1
    funext s
    rw [enorm_smul]
  have hh : AEMeasurable (fun s => ‖(((heatSymbol (t - s) ξ : ℝ) : ℂ))‖ₑ) (volume.restrict (Ioc a t)) := by
    have : Continuous (fun s => (((heatSymbol (t - s) ξ : ℝ) : ℂ))) := by
      unfold heatSymbol
      fun_prop
    exact this.measurable.enorm.aemeasurable
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc a t)) Real.HolderConjugate.two_two hh hm
  simp only [Pi.mul_apply, rpow_two_eq] at h2
  calc ‖varConstIntegral a N t ξ‖ₑ ^ 2
      ≤ (∫⁻ s in Ioc a t, ‖(((heatSymbol (t - s) ξ : ℝ) : ℂ))‖ₑ * ‖N s ξ‖ₑ) ^ 2 :=
        pow_le_pow_left₀ bot_le h1 2
    _ ≤ ((∫⁻ s in Ioc a t, ‖(((heatSymbol (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ s in Ioc a t, ‖N s ξ‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ bot_le h2 2
    _ = _ := by
      have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      rw [mul_pow, hsq, hsq]

private theorem hsWeight_succ (n : ℕ) (ξ : Space) :
    ENNReal.ofReal (hsWeight (n + 1) ξ) = ENNReal.ofReal (hsWeight n ξ) * ENNReal.ofReal (1 + ‖ξ‖ ^ 2) := by
  unfold hsWeight
  rw [pow_succ, ENNReal.ofReal_mul (by positivity)]

private theorem varConst_weight_le {a b t : ℝ} (ht : t ∈ Icc a b) (n : ℕ) (N : ℝ → Space → CSpace)
    (ξ : Space) (hm : AEMeasurable (fun s => ‖N s ξ‖ₑ) (volume.restrict (Icc a b))) :
    ENNReal.ofReal (hsWeight (n + 1) ξ) * ‖varConstIntegral a N t ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal ((b - a) + 1) * (ENNReal.ofReal (hsWeight n ξ) * ∫⁻ s in Icc a b, ‖N s ξ‖ₑ ^ 2) := by
  have hsub : Ioc a t ⊆ Icc a b := fun x hx => ⟨hx.1.le, hx.2.trans ht.2⟩
  have h2 := enorm_varConstIntegral_sq_le ht.1 N ξ (hm.mono_set hsub)
  have h3 := lintegral_heat_sq_le ht.1 ξ
  have h4 : ENNReal.ofReal ((t - a) + 1) ≤ ENNReal.ofReal ((b - a) + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith [ht.2])
  have h5 : ∫⁻ s in Ioc a t, ‖N s ξ‖ₑ ^ 2 ≤ ∫⁻ s in Icc a b, ‖N s ξ‖ₑ ^ 2 := lintegral_mono_set hsub
  rw [hsWeight_succ, mul_assoc]
  calc ENNReal.ofReal (hsWeight n ξ) * (ENNReal.ofReal (1 + ‖ξ‖ ^ 2) * ‖varConstIntegral a N t ξ‖ₑ ^ 2)
      ≤ ENNReal.ofReal (hsWeight n ξ) * (ENNReal.ofReal (1 + ‖ξ‖ ^ 2) *
          ((∫⁻ s in Ioc a t, ‖(((heatSymbol (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2) * ∫⁻ s in Ioc a t, ‖N s ξ‖ₑ ^ 2)) := by
        gcongr
    _ = ENNReal.ofReal (hsWeight n ξ) * ((ENNReal.ofReal (1 + ‖ξ‖ ^ 2) *
          ∫⁻ s in Ioc a t, ‖(((heatSymbol (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2) * ∫⁻ s in Ioc a t, ‖N s ξ‖ₑ ^ 2) := by
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (hsWeight n ξ) * (ENNReal.ofReal ((b - a) + 1) * ∫⁻ s in Icc a b, ‖N s ξ‖ₑ ^ 2) := by
        gcongr
        exact h3.trans h4
    _ = _ := by rw [mul_left_comm]

private theorem enorm_sub_sq_le (x y : CSpace) : ‖x - y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have e : ∀ z : CSpace, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, e]
  have h := norm_sub_le x y
  have key : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x - y)]
  calc ENNReal.ofReal (‖x - y‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal key
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

private theorem one_le_hsWeight (n : ℕ) (ξ : Space) : 1 ≤ ENNReal.ofReal (hsWeight n ξ) := by
  rw [ENNReal.one_le_ofReal]
  unfold hsWeight
  exact one_le_pow₀ (by nlinarith [sq_nonneg ‖ξ‖])

private theorem measurable_hsWeight (n : ℕ) : Measurable (fun ξ : Space => ENNReal.ofReal (hsWeight n ξ)) := by
  have : Continuous (fun ξ : Space => hsWeight n ξ) := by
    unfold hsWeight
    fun_prop
  exact ENNReal.measurable_ofReal.comp this.measurable

theorem varConstIntegral_isHsCurve (n : ℕ) {a b : ℝ} (N : ℝ → Space → CSpace) (K : ℝ)
    (hN : AEStronglyMeasurable (fun p : Space × ℝ => N p.2 p.1)
      ((volume : Measure Space).prod (volume.restrict (Icc a b))))
    (hK : ∀ s ∈ Icc a b, hsNormSq n (N s) ≤ ENNReal.ofReal K) :
    IsHsCurve (n + 1) (varConstIntegral a N) a b := by
  set J : Space → ℝ≥0∞ := fun ξ => ∫⁻ s in Icc a b, ‖N s ξ‖ₑ ^ 2 with hJ
  have hmξ : ∀ᵐ ξ ∂(volume : Measure Space),
      AEStronglyMeasurable (fun s => N s ξ) (volume.restrict (Icc a b)) := hN.prodMk_left
  have hJm : AEMeasurable J volume := (hN.enorm.pow_const 2).lintegral_prod_right'
  have hwJm : AEMeasurable (fun ξ => ENNReal.ofReal (hsWeight n ξ) * J ξ) volume :=
    (measurable_hsWeight n).aemeasurable.mul hJm
  have hfin : ∫⁻ ξ, ENNReal.ofReal (hsWeight n ξ) * J ξ ≠ ⊤ := by
    have e1 : ∫⁻ ξ, ENNReal.ofReal (hsWeight n ξ) * J ξ =
        ∫⁻ ξ, ∫⁻ s in Icc a b, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 := by
      refine lintegral_congr fun ξ => ?_
      rw [hJ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hprod : AEMeasurable (Function.uncurry fun (ξ : Space) (s : ℝ) =>
        ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2)
        ((volume : Measure Space).prod (volume.restrict (Icc a b))) :=
      ((measurable_hsWeight n).comp measurable_fst).aemeasurable.mul (hN.enorm.pow_const 2)
    rw [e1, lintegral_lintegral_swap hprod]
    have e2 : ∫⁻ s in Icc a b, ∫⁻ ξ, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 ≤
        ∫⁻ s in Icc a b, ENNReal.ofReal K :=
      lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hK))
    refine ne_top_of_le_ne_top ?_ e2
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hbound : ∀ t ∈ Icc a b, ∀ᵐ ξ ∂(volume : Measure Space),
      ENNReal.ofReal (hsWeight (n + 1) ξ) * ‖varConstIntegral a N t ξ‖ₑ ^ 2 ≤
        ENNReal.ofReal ((b - a) + 1) * (ENNReal.ofReal (hsWeight n ξ) * J ξ) := by
    intro t ht
    filter_upwards [hmξ] with ξ hξ
    exact varConst_weight_le ht n N ξ hξ.enorm
  have hmeas : ∀ t ∈ Icc a b, AEStronglyMeasurable (varConstIntegral a N t) volume := by
    intro t ht
    have hsub : Ioc a t ⊆ Icc a b := fun x hx => ⟨hx.1.le, hx.2.trans ht.2⟩
    have e : (volume : Measure Space).prod (volume.restrict (Ioc a t)) =
        ((volume : Measure Space).prod (volume.restrict (Icc a b))).restrict (univ ×ˢ Ioc a t) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.2 hsub]
    have hN' : AEStronglyMeasurable (fun p : Space × ℝ => N p.2 p.1)
        ((volume : Measure Space).prod (volume.restrict (Ioc a t))) := by
      rw [e]
      exact hN.restrict
    have hc : Continuous (fun p : Space × ℝ => ((heatSymbol (t - p.2) p.1 : ℝ) : ℂ)) := by
      unfold heatSymbol
      fun_prop
    have h := (hc.aestronglyMeasurable.smul hN').integral_prod_right'
    have e2 : varConstIntegral a N t = fun ξ => ∫ s in Ioc a t,
        ((heatSymbol (t - s) ξ : ℝ) : ℂ) • N s ξ := by
      funext ξ
      unfold varConstIntegral
      rw [intervalIntegral.integral_of_le ht.1]
    rw [e2]
    exact h
  refine ⟨fun t ht => ⟨hmeas t ht, ?_⟩, fun t₀ ht₀ => ?_⟩
  · unfold hsNormSq
    refine lt_of_le_of_lt (lintegral_mono_ae (hbound t ht)) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfin)
  · have hab : a ≤ b := ht₀.1.trans ht₀.2
    have hlim : ∀ᵐ ξ ∂(volume : Measure Space), Tendsto (fun t => ENNReal.ofReal (hsWeight (n + 1) ξ) *
        ‖(varConstIntegral a N t - varConstIntegral a N t₀) ξ‖ₑ ^ 2) (𝓝[Icc a b] t₀) (𝓝 0) := by
      filter_upwards [hmξ, ae_lt_top' hwJm hfin] with ξ hξ hfξ
      have hJξ : J ξ < ⊤ := by
        refine lt_of_le_of_lt ?_ hfξ
        calc J ξ = 1 * J ξ := (one_mul _).symm
          _ ≤ ENNReal.ofReal (hsWeight n ξ) * J ξ := by gcongr; exact one_le_hsWeight n ξ
      have hL2 : MemLp (fun s => N s ξ) 2 (volume.restrict (Icc a b)) := by
        refine ⟨hξ, ?_⟩
        rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
        simpa [rpow_two_eq] using hJξ
      have hint : IntegrableOn (fun s => N s ξ) (Icc a b) := hL2.integrable one_le_two
      have hcs : Continuous (fun s : ℝ => ((heatSymbol (-s) ξ : ℝ) : ℂ)) := by
        unfold heatSymbol
        fun_prop
      have hint2 : IntegrableOn (fun s => ((heatSymbol (-s) ξ : ℝ) : ℂ) • N s ξ) (uIcc a b) := by
        rw [uIcc_of_le hab]
        exact hint.continuousOn_smul hcs.continuousOn isCompact_Icc
      have hP := intervalIntegral.continuousOn_primitive_interval hint2
      rw [uIcc_of_le hab] at hP
      have hct : Continuous (fun t : ℝ => ((heatSymbol t ξ : ℝ) : ℂ)) := by
        unfold heatSymbol
        fun_prop
      have hfac : ∀ t, varConstIntegral a N t ξ = ((heatSymbol t ξ : ℝ) : ℂ) •
          ∫ s in a..t, ((heatSymbol (-s) ξ : ℝ) : ℂ) • N s ξ := by
        intro t
        unfold varConstIntegral
        rw [← intervalIntegral.integral_smul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        rw [heat_mul, Complex.ofReal_mul, mul_smul]
      have hcw : ContinuousWithinAt (fun t => varConstIntegral a N t ξ) (Icc a b) t₀ := by
        simp only [hfac]
        exact hct.continuousWithinAt.smul (hP t₀ ht₀)
      have h0 : Tendsto (fun t => varConstIntegral a N t ξ - varConstIntegral a N t₀ ξ)
          (𝓝[Icc a b] t₀) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 hcw
      have h1 : Tendsto (fun t => ‖varConstIntegral a N t ξ - varConstIntegral a N t₀ ξ‖ₑ)
          (𝓝[Icc a b] t₀) (𝓝 0) := by
        have h := (continuous_enorm.tendsto (0 : CSpace)).comp h0
        rw [enorm_zero] at h
        exact h
      have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (hsWeight (n + 1) ξ))
        (ENNReal.Tendsto.pow (n := 2) h1) (Or.inr ENNReal.ofReal_ne_top)
      simpa using h2
    have hmain := tendsto_lintegral_filter_of_dominated_convergence'
      (fun ξ => 4 * (ENNReal.ofReal ((b - a) + 1) * (ENNReal.ofReal (hsWeight n ξ) * J ξ)))
      (F := fun t ξ => ENNReal.ofReal (hsWeight (n + 1) ξ) *
        ‖(varConstIntegral a N t - varConstIntegral a N t₀) ξ‖ₑ ^ 2) (f := fun _ => 0) ?_ ?_ ?_ hlim
    · simpa [hsNormSq] using hmain
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (measurable_hsWeight (n + 1)).aemeasurable.mul
        (((hmeas t ht).sub (hmeas t₀ ht₀)).enorm.pow_const 2)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [hbound t ht, hbound t₀ ht₀] with ξ h1 h2
      calc ENNReal.ofReal (hsWeight (n + 1) ξ) * ‖(varConstIntegral a N t - varConstIntegral a N t₀) ξ‖ₑ ^ 2
          ≤ ENNReal.ofReal (hsWeight (n + 1) ξ) * (2 * ‖varConstIntegral a N t ξ‖ₑ ^ 2 +
              2 * ‖varConstIntegral a N t₀ ξ‖ₑ ^ 2) := by
            gcongr
            exact enorm_sub_sq_le _ _
        _ = 2 * (ENNReal.ofReal (hsWeight (n + 1) ξ) * ‖varConstIntegral a N t ξ‖ₑ ^ 2) +
              2 * (ENNReal.ofReal (hsWeight (n + 1) ξ) * ‖varConstIntegral a N t₀ ξ‖ₑ ^ 2) := by
            rw [mul_add, mul_left_comm, mul_left_comm (ENNReal.ofReal _) 2]
        _ ≤ 2 * (ENNReal.ofReal ((b - a) + 1) * (ENNReal.ofReal (hsWeight n ξ) * J ξ)) +
              2 * (ENNReal.ofReal ((b - a) + 1) * (ENNReal.ofReal (hsWeight n ξ) * J ξ)) := by
            gcongr
        _ = _ := by
            rw [← add_mul]
            norm_num
    · rw [lintegral_const_mul' 4 _ (by norm_num), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)

end Breakdown.SmoothFlow
