import Breakdown.Uniqueness.RegLocalAuxEstPart1
import Breakdown.Uniqueness.RegLocalAuxEstPart2
import Breakdown.Uniqueness.RegLocalAuxEstPart3
import Breakdown.Uniqueness.RegLocalAuxEstPart4

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem enorm_add_sq_le' (x y : CSpace) :
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

private theorem measurable_hsWeight_ofReal (m : ℕ) :
    Measurable (fun ξ : Space => ENNReal.ofReal (hsWeight m ξ)) :=
  (by fun_prop : Continuous fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ m).measurable.ennreal_ofReal

private theorem hsNormSq_add_le_left (m : ℕ) {f g : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) :
    hsNormSq m (f + g) ≤ 2 * hsNormSq m f + 2 * hsNormSq m g := by
  unfold hsNormSq
  calc ∫⁻ ξ, ENNReal.ofReal (hsWeight m ξ) * ‖(f + g) ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, (2 * (ENNReal.ofReal (hsWeight m ξ) * ‖f ξ‖ₑ ^ 2) +
          2 * (ENNReal.ofReal (hsWeight m ξ) * ‖g ξ‖ₑ ^ 2)) := by
        refine lintegral_mono fun ξ => ?_
        calc ENNReal.ofReal (hsWeight m ξ) * ‖(f + g) ξ‖ₑ ^ 2
            ≤ ENNReal.ofReal (hsWeight m ξ) * (2 * ‖f ξ‖ₑ ^ 2 + 2 * ‖g ξ‖ₑ ^ 2) :=
              mul_le_mul_right (enorm_add_sq_le' (f ξ) (g ξ)) _
          _ = _ := by ring
    _ = _ := by
        rw [lintegral_add_left' ?_, lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]
        exact (((measurable_hsWeight_ofReal m).aemeasurable.mul
          (hf.enorm.pow_const 2))).const_mul _

private theorem hsNormSq_heat_smul_le (m : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) (f : Space → CSpace) :
    hsNormSq m (fun ξ => ((heatSymbol τ ξ : ℝ) : ℂ) • f ξ) ≤ hsNormSq m f := by
  unfold hsNormSq
  refine lintegral_mono fun ξ => mul_le_mul_right ?_ _
  have h1 : ‖(((heatSymbol τ ξ : ℝ) : ℂ))‖ₑ ≤ 1 := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    simp only [heatSymbol]
    rw [abs_of_pos (Real.exp_pos _)]
    refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_))
    have := Real.pi_pos
    positivity
  rw [enorm_smul]
  calc (‖(((heatSymbol τ ξ : ℝ) : ℂ))‖ₑ * ‖f ξ‖ₑ) ^ 2 ≤ (1 * ‖f ξ‖ₑ) ^ 2 := by gcongr
    _ = ‖f ξ‖ₑ ^ 2 := by rw [one_mul]

private theorem ofReal_sq_le' (B : ℝ) : ENNReal.ofReal B ^ 2 ≤ ENNReal.ofReal (B ^ 2) := by
  rcases le_or_gt 0 B with h | h
  · rw [ENNReal.ofReal_pow h]
  · rw [ENNReal.ofReal_of_nonpos h.le]
    simp

private theorem continuous_heat_time (t : ℝ) (ξ : Space) :
    Continuous fun s : ℝ => ((heatSymbol (t - s) ξ : ℝ) : ℂ) := by
  unfold heatSymbol
  fun_prop

theorem varConstMap_bound (m : ℕ) (hm : 3 ≤ m) : ∃ C : ℝ, 0 < C ∧
    ∀ (a δ B : ℝ) (F₀ : Space → CSpace) (G : ℝ → Space → CSpace), 0 < δ → δ ≤ 1 →
      AEStronglyMeasurable F₀ volume → IsHsCurve m G a (a + δ) →
      (∀ t ∈ Icc a (a + δ), hsNormSq m (G t) ≤ ENNReal.ofReal B) →
      ∀ t ∈ Icc a (a + δ),
        hsNormSq m (varConstMap a F₀ G t) ≤ 2 * hsNormSq m F₀ + ENNReal.ofReal (C * δ * B ^ 2) := by
  obtain ⟨C₁, hC₁, hN⟩ := hsNormSq_nonlinSymbol_le m hm
  refine ⟨4 * C₁, by positivity, ?_⟩
  intro a δ B F₀ G hδ hδ1 hF₀ hG hB t ht
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hab : a ≤ a + δ := by linarith
  obtain ⟨u, hu, hueq⟩ := exists_measurable_nonlin_curve hab (fun s hs => (hG.1 s hs).1)
    (continuousOn_nonlinSymbol_curve (by omega) hG)
  have hsub : ∀ s ∈ Icc a t, s ∈ Icc a (a + δ) := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hsplit : varConstMap a F₀ G t = (fun ξ => ((heatSymbol (t - a) ξ : ℝ) : ℂ) • F₀ ξ) +
      fun ξ => ∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • u s ξ := by
    funext ξ
    simp only [varConstMap, Pi.add_apply]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [hueq s (hsub s hs)]
  have hmeas0 : AEStronglyMeasurable (fun ξ => ((heatSymbol (t - a) ξ : ℝ) : ℂ) • F₀ ξ) volume := by
    have hc0 : Continuous fun ξ : Space => ((heatSymbol (t - a) ξ : ℝ) : ℂ) := by
      unfold heatSymbol
      fun_prop
    exact hc0.aestronglyMeasurable.smul hF₀
  have hK : ∀ s ∈ Ioc a t, hsNormSq n (u s) ≤ ENNReal.ofReal C₁ * ENNReal.ofReal (B ^ 2) := by
    intro s hs
    have hs' := hsub s (Ioc_subset_Icc_self hs)
    rw [hueq s hs']
    have := hN (G s) (hG.1 s hs').1
    simp only [Nat.add_sub_cancel] at this
    refine this.trans (mul_le_mul_right ?_ _)
    exact (pow_le_pow_left₀ zero_le (hB s hs') 2).trans (ofReal_sq_le' B)
  have hta : 0 ≤ t - a := by linarith [ht.1]
  have hbase := hsNormSq_heatIntegral_le n ht.1 (by linarith [ht.2]) u hu _ hK
  rw [hsplit]
  refine (hsNormSq_add_le_left _ hmeas0).trans (add_le_add
    (mul_le_mul_right (hsNormSq_heat_smul_le _ hta F₀) 2) ?_)
  refine (mul_le_mul_right hbase 2).trans ?_
  rw [← ENNReal.ofReal_mul hC₁.le, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := mul_nonneg hC₁.le (sq_nonneg B)
  nlinarith [ht.2]

theorem varConstMap_contract (m : ℕ) (hm : 3 ≤ m) : ∃ C : ℝ, 0 < C ∧
    ∀ (a δ B : ℝ) (F₀ : Space → CSpace) (G H : ℝ → Space → CSpace), 0 < δ → δ ≤ 1 →
      AEStronglyMeasurable F₀ volume → hsNormSq m F₀ < ⊤ →
      IsHsCurve m G a (a + δ) → IsHsCurve m H a (a + δ) →
      (∀ t ∈ Icc a (a + δ), hsNormSq m (G t) ≤ ENNReal.ofReal B) →
      (∀ t ∈ Icc a (a + δ), hsNormSq m (H t) ≤ ENNReal.ofReal B) →
      ∀ t ∈ Icc a (a + δ),
        hsNormSq m (varConstMap a F₀ G t - varConstMap a F₀ H t) ≤
          ENNReal.ofReal (C * δ * B) * ⨆ s ∈ Icc a (a + δ), hsNormSq m (G s - H s) := by
  obtain ⟨C₃, hC₃, hD⟩ := hsNormSq_nonlinSymbol_sub_le m hm
  refine ⟨4 * C₃, by positivity, ?_⟩
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
      IntervalIntegrable (fun s => ((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (K s) ξ)
        volume a t := by
    intro K hK ξ
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    exact ContinuousOn.smul (f := fun s => ((heatSymbol (t - s) ξ : ℝ) : ℂ))
      (g := fun s => nonlinSymbol (K s) ξ) (continuous_heat_time t ξ).continuousOn
      ((hK ξ).mono fun s hs => hsub s hs)
  have hdiff : varConstMap a F₀ G t - varConstMap a F₀ H t =
      fun ξ => ∫ s in a..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • (u s ξ - v s ξ) := by
    funext ξ
    simp only [Pi.sub_apply, varConstMap, add_sub_add_left_eq_sub]
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
    have := hD (G s) (H s) (hG.1 s hs').1 (hH.1 s hs').1 (hG.1 s hs').2 (hH.1 s hs').2
    simp only [Nat.add_sub_cancel] at this
    refine this.trans ?_
    gcongr
    · exact hBG s hs'
    · exact hBH s hs'
    · exact le_iSup₂ (f := fun s _ => hsNormSq (n + 1) (G s - H s)) s hs'
  have hmeasN : Measurable (Function.uncurry fun s ξ => u s ξ - v s ξ) := hu.sub hv
  have hbase := hsNormSq_heatIntegral_le n ht.1 (by linarith [ht.2]) _ hmeasN _ hK
  have hconst : 2 * ENNReal.ofReal (t - a) * (ENNReal.ofReal C₃ * (ENNReal.ofReal B + ENNReal.ofReal B)) ≤
      ENNReal.ofReal (4 * C₃ * δ * B) := by
    rcases le_or_gt 0 B with hB | hB
    · rw [← ENNReal.ofReal_add hB hB, ← ENNReal.ofReal_mul hC₃.le, ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by nlinarith [ht.1])]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [ht.1, ht.2, mul_nonneg hC₃.le hB])
    · simp [ENNReal.ofReal_of_nonpos hB.le]
  rw [hdiff]
  refine hbase.trans ?_
  calc 2 * ENNReal.ofReal (t - a) * (ENNReal.ofReal C₃ * (ENNReal.ofReal B + ENNReal.ofReal B) *
        ⨆ s ∈ Icc a (a + δ), hsNormSq (n + 1) (G s - H s))
      = 2 * ENNReal.ofReal (t - a) * (ENNReal.ofReal C₃ * (ENNReal.ofReal B + ENNReal.ofReal B)) *
        ⨆ s ∈ Icc a (a + δ), hsNormSq (n + 1) (G s - H s) := by ring
    _ ≤ _ := mul_le_mul_left hconst _

end Breakdown.SmoothFlow
