import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegLocalAuxEstPart2
import Breakdown.Uniqueness.RegLocalAuxEstPart3
import Breakdown.Uniqueness.RegLocalAuxEstPart4

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem pmap_enorm_add_sq_le (x y : CSpace) :
    ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _)]
  have h1 := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [norm_nonneg (x + y), norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖)]
  calc ENNReal.ofReal (‖x + y‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h2
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

private theorem pmap_measurable_weight (m : ℕ) :
    Measurable (fun ξ : Space => ENNReal.ofReal (hsWeight m ξ)) :=
  (by fun_prop : Continuous fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ m).measurable.ennreal_ofReal

private theorem pmap_hsNormSq_add_le (m : ℕ) {f g : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) :
    hsNormSq m (f + g) ≤ 2 * hsNormSq m f + 2 * hsNormSq m g := by
  unfold hsNormSq
  calc ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * ‖(f + g) ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, (2 * (ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2) +
          2 * (ENNReal.ofReal (hsWeight m ξ) * ‖g ξ‖ₑ ^ 2)) := by
        refine lintegral_mono fun ξ => ?_
        calc ENNReal.ofReal (hsWeight m ξ) * ‖(f + g) ξ‖ₑ ^ 2
            ≤ ENNReal.ofReal (hsWeight m ξ) * (2 * ‖f ξ‖ₑ ^ 2 + 2 * ‖g ξ‖ₑ ^ 2) :=
              mul_le_mul_right (pmap_enorm_add_sq_le (f ξ) (g ξ)) _
          _ = _ := by ring
    _ = _ := by
        rw [lintegral_add_left' ?_, lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]
        exact (((pmap_measurable_weight m).aemeasurable.mul
          (hf.enorm.pow_const 2))).const_mul _

private theorem pmap_symbol_le_one (α : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (ξ : Space) :
    powerHeatSymbol α τ ξ ≤ 1 := by
  unfold powerHeatSymbol
  refine Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hτ (Real.rpow_nonneg ?_ _)))
  have := Real.pi_pos
  positivity

private theorem pmap_hsNormSq_smul_le (α : ℝ) (m : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (f : Space → CSpace) :
    hsNormSq m (fun ξ => ((powerHeatSymbol α τ ξ : ℝ) : ℂ) • f ξ) ≤ hsNormSq m f := by
  unfold hsNormSq
  refine lintegral_mono fun ξ => mul_le_mul_right ?_ _
  have h1 : ‖(((powerHeatSymbol α τ ξ : ℝ) : ℂ))‖ₑ ≤ 1 := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < powerHeatSymbol α τ ξ := Real.exp_pos _
    rw [abs_of_pos hpos]
    exact ENNReal.ofReal_le_one.mpr (pmap_symbol_le_one α hτ ξ)
  rw [enorm_smul]
  calc (‖(((powerHeatSymbol α τ ξ : ℝ) : ℂ))‖ₑ * ‖f ξ‖ₑ) ^ 2 ≤ (1 * ‖f ξ‖ₑ) ^ 2 := by gcongr
    _ = ‖f ξ‖ₑ ^ 2 := by rw [one_mul]

private theorem pmap_ofReal_sq_le (B : ℝ) : ENNReal.ofReal B ^ 2 ≤ ENNReal.ofReal (B ^ 2) := by
  rcases le_or_gt 0 B with h | h
  · rw [ENNReal.ofReal_pow h]
  · rw [ENNReal.ofReal_of_nonpos h.le]
    simp

private theorem pmap_measurable_symbol (α τ : ℝ) :
    Measurable fun ξ : Space => ((powerHeatSymbol α τ ξ : ℝ) : ℂ) := by
  unfold powerHeatSymbol
  fun_prop

private theorem pmap_const_le (C₀ x y : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal C₀ * ENNReal.ofReal x * ENNReal.ofReal y ≤
      ENNReal.ofReal ((|C₀| + 1) * x * y) := by
  have hD : 0 ≤ |C₀| + 1 := by positivity
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (|C₀| + 1) * x), ENNReal.ofReal_mul hD]
  gcongr
  exact (le_abs_self C₀).trans (by linarith)

theorem powerMildMapEst_of (α : ℝ) (hα : 1 < α) (h1 : PowerHeatIntegralStatement α)
    (h2 : PowerHeatBasicStatement α) : PowerMildMapEstStatement α := by
  obtain ⟨C₀, hC₀⟩ := h1
  have hD : 0 ≤ |C₀| + 1 := by positivity
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · obtain ⟨C₁, hC₁, hN⟩ := hsNormSq_nonlinSymbol_le m hm
    refine ⟨2 * (|C₀| + 1) * C₁, by positivity, ?_⟩
    intro a δ B F₀ G hδ hδ1 hF₀ hG hB t ht
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hab : a ≤ a + δ := by linarith
    obtain ⟨u, hu, hueq⟩ := exists_measurable_nonlin_curve hab (fun s hs => (hG.1 s hs).1)
      (continuousOn_nonlinSymbol_curve (by omega) hG)
    have hsub : ∀ s ∈ Icc a t, s ∈ Icc a (a + δ) := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
    have hsplit : powerMildMap α a F₀ G t =
        (fun ξ => ((powerHeatSymbol α (t - a) ξ : ℝ) : ℂ) • F₀ ξ) +
        fun ξ => ∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • u s ξ := by
      funext ξ
      simp only [powerMildMap, Pi.add_apply]
      congr 1
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [hueq s (hsub s hs)]
    have hmeas0 : AEStronglyMeasurable
        (fun ξ => ((powerHeatSymbol α (t - a) ξ : ℝ) : ℂ) • F₀ ξ) volume :=
      (pmap_measurable_symbol α (t - a)).aestronglyMeasurable.smul hF₀
    have hK : ∀ s ∈ Ioc a t, hsNormSq n (u s) ≤ ENNReal.ofReal (C₁ * B ^ 2) := by
      intro s hs
      have hs' := hsub s (Ioc_subset_Icc_self hs)
      rw [hueq s hs', ENNReal.ofReal_mul hC₁.le]
      have := hN (G s) (hG.1 s hs').1
      simp only [Nat.add_sub_cancel] at this
      refine this.trans (mul_le_mul_right ?_ _)
      exact (pow_le_pow_left₀ zero_le (hB s hs') 2).trans (pmap_ofReal_sq_le B)
    have hta : 0 ≤ t - a := by linarith [ht.1]
    have hbase := hC₀ n a t ht.1 (by linarith [ht.2]) u hu _ hK
    have hcore' := hbase.trans (pmap_const_le C₀ (t - a) (C₁ * B ^ 2) hta)
    rw [hsplit]
    refine (pmap_hsNormSq_add_le _ hmeas0).trans (add_le_add
      (mul_le_mul_right (pmap_hsNormSq_smul_le α _ hta F₀) 2) ?_)
    refine (mul_le_mul_right hcore' 2).trans ?_
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hDCB : 0 ≤ (|C₀| + 1) * (C₁ * B ^ 2) := mul_nonneg hD (mul_nonneg hC₁.le (sq_nonneg B))
    have := mul_le_mul_of_nonneg_left (show t - a ≤ δ by linarith [ht.2]) hDCB
    nlinarith [this]
  · obtain ⟨C₃, hC₃, hDiff⟩ := hsNormSq_nonlinSymbol_sub_le m hm
    refine ⟨2 * (|C₀| + 1) * C₃, by positivity, ?_⟩
    intro a δ B F₀ G H hδ hδ1 hF₀ hF₀m hG hH hBG hBH t ht
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hab : a ≤ a + δ := by linarith
    have hcG := continuousOn_nonlinSymbol_curve (by omega) hG
    have hcH := continuousOn_nonlinSymbol_curve (by omega) hH
    obtain ⟨u, hu, hueq⟩ := exists_measurable_nonlin_curve hab (fun s hs => (hG.1 s hs).1) hcG
    obtain ⟨v, hv, hveq⟩ := exists_measurable_nonlin_curve hab (fun s hs => (hH.1 s hs).1) hcH
    have hsub : ∀ s ∈ Icc a t, s ∈ Icc a (a + δ) := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
    have hint : ∀ K : ℝ → Space → CSpace,
        (∀ ξ, ContinuousOn (fun s => nonlinSymbol (K s) ξ) (Icc a (a + δ))) → ∀ ξ,
        IntervalIntegrable
          (fun s => ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (K s) ξ)
          volume a t := by
      intro K hK ξ
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le ht.1]
      exact ContinuousOn.smul (f := fun s => ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))
        (g := fun s => nonlinSymbol (K s) ξ)
        (Complex.continuous_ofReal.comp (h2.2.1 t ξ)).continuousOn
        ((hK ξ).mono fun s hs => hsub s hs)
    have hdiff : powerMildMap α a F₀ G t - powerMildMap α a F₀ H t =
        fun ξ => ∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • (u s ξ - v s ξ) := by
      funext ξ
      simp only [Pi.sub_apply, powerMildMap, add_sub_add_left_eq_sub]
      rw [← intervalIntegral.integral_sub (hint G hcG ξ) (hint H hcH ξ)]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [hueq s (hsub s hs), hveq s (hsub s hs), smul_sub]
    have hK : ∀ s ∈ Ioc a t, hsNormSq n (fun ξ => u s ξ - v s ξ) ≤
        ENNReal.ofReal C₃ * (ENNReal.ofReal B + ENNReal.ofReal B) *
          ⨆ s ∈ Icc a (a + δ), hsNormSq (n + 1) (G s - H s) := by
      intro s hs
      have hs' := hsub s (Ioc_subset_Icc_self hs)
      have heq : (fun ξ => u s ξ - v s ξ) = nonlinSymbol (G s) - nonlinSymbol (H s) := by
        funext ξ
        simp [hueq s hs', hveq s hs']
      rw [heq]
      have := hDiff (G s) (H s) (hG.1 s hs').1 (hH.1 s hs').1 (hG.1 s hs').2 (hH.1 s hs').2
      simp only [Nat.add_sub_cancel] at this
      refine this.trans ?_
      gcongr
      · exact hBG s hs'
      · exact hBH s hs'
      · exact le_iSup₂ (f := fun s _ => hsNormSq (n + 1) (G s - H s)) s hs'
    have hmeasN : Measurable (Function.uncurry fun s ξ => u s ξ - v s ξ) := hu.sub hv
    have hbase := hC₀ n a t ht.1 (by linarith [ht.2]) _ hmeasN _ hK
    have hta : 0 ≤ t - a := by linarith [ht.1]
    have hconst : ENNReal.ofReal C₀ * ENNReal.ofReal (t - a) *
        (ENNReal.ofReal C₃ * (ENNReal.ofReal B + ENNReal.ofReal B)) ≤
        ENNReal.ofReal (2 * (|C₀| + 1) * C₃ * δ * B) := by
      rcases le_or_gt 0 B with hB | hB
      · rw [← ENNReal.ofReal_add hB hB, ← ENNReal.ofReal_mul hC₃.le]
        refine (pmap_const_le C₀ (t - a) (C₃ * (B + B)) hta).trans ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hDCB : 0 ≤ (|C₀| + 1) * (C₃ * (B + B)) := by positivity
        have := mul_le_mul_of_nonneg_left (show t - a ≤ δ by linarith [ht.2]) hDCB
        nlinarith [this]
      · simp [ENNReal.ofReal_of_nonpos hB.le]
    rw [hdiff]
    refine hbase.trans ?_
    calc ENNReal.ofReal C₀ * ENNReal.ofReal (t - a) *
          (ENNReal.ofReal C₃ * (ENNReal.ofReal B + ENNReal.ofReal B) *
          ⨆ s ∈ Icc a (a + δ), hsNormSq (n + 1) (G s - H s))
        = ENNReal.ofReal C₀ * ENNReal.ofReal (t - a) *
          (ENNReal.ofReal C₃ * (ENNReal.ofReal B + ENNReal.ofReal B)) *
          ⨆ s ∈ Icc a (a + δ), hsNormSq (n + 1) (G s - H s) := by ring
      _ ≤ _ := mul_le_mul_left hconst _

end Breakdown.SmoothFlow
