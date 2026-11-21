import Breakdown.Uniqueness.StressFarAux2

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Internal.FarStress

theorem far_base_le {r A c₁ c₂ S : ℝ} {w : Space → Space} {e g : Space → ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hc₁ : 0 ≤ c₁) (hS : 0 ≤ S)
    (hw : Continuous w) (he : Continuous e) (hgc : Continuous g)
    (he0 : ∀ x, 0 ≤ e x) (he1 : ∀ x, e x ≤ 1)
    (hslope : ∀ x y, |e x - e y| ≤ c₁ * ‖x - y‖ / r)
    (hg : ∀ y, |g y| ≤ c₂ / r * ‖w y‖)
    (hE : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal (A ^ 2))
    (hS6 : ∫⁻ x, ENNReal.ofReal (e x ^ 2 * ‖w x‖) ^ (6 : ℝ) ≤ ENNReal.ofReal (S ^ 6))
    (hc₂ : 0 ≤ c₂) :
    ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) *
        ∫⁻ y, ENNReal.ofReal (‖x - y‖⁻¹ ^ 3 * |e y ^ 3 - e x ^ 3|) * ENNReal.ofReal |g y| ≤
      ENNReal.ofReal (A ^ 2) *
          (ENNReal.ofReal (3 / 2 * c₁ / r) *
              (ENNReal.ofReal (20 * π / 3 * r ^ (3 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
                ENNReal.ofReal (c₂ * S / r)) +
            ENNReal.ofReal (4 * π / 3 * r⁻¹ ^ 3) ^ (1 / 2 : ℝ) * ENNReal.ofReal (c₂ * A / r)) +
        ENNReal.ofReal (3 / 2 * c₁ / r) *
          (ENNReal.ofReal (S * A) * ENNReal.ofReal (20 * π / 3 * r ^ (3 / 5 : ℝ)) ^ (5 / 6 : ℝ) *
            ENNReal.ofReal (c₂ * A / r)) := by
  have hY := productBound_weight_le hA hS hw.measurable he.measurable hE hS6
  have hG2' := lintegral_flux_sq_le (g := g) hg hE
  have h6' := lintegral_weighted_flux_six_le (g := g) hg hS6
  set K := ENNReal.ofReal (3 / 2 * c₁ / r) with hK
  set P1 := ENNReal.ofReal (20 * π / 3 * r ^ (3 / 5 : ℝ)) ^ (5 / 6 : ℝ) with hP1
  set P3 := ENNReal.ofReal (4 * π / 3 * r⁻¹ ^ 3) ^ (1 / 2 : ℝ) with hP3
  set G : Space → ℝ≥0∞ := fun y => ENNReal.ofReal |g y| with hG
  set Ea : Space → ℝ≥0∞ := fun y => ENNReal.ofReal (e y ^ 2) with hEa
  set W : Space → ℝ≥0∞ := fun x => ENNReal.ofReal (‖w x‖ ^ 2) with hW
  have hGm : Measurable G := ENNReal.measurable_ofReal.comp hgc.measurable.abs
  have hEam : Measurable Ea := ENNReal.measurable_ofReal.comp (he.measurable.pow_const 2)
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp (hw.measurable.norm.pow_const 2)
  have hNm := measurable_nearKernel r
  have hFm := measurable_farKernel r
  have hG2 : (∫⁻ y, G y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (c₂ * A / r) := by
    calc _ ≤ ENNReal.ofReal ((c₂ * A / r) ^ 2) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hG2' (by norm_num)
      _ = _ := ofReal_sq_rpow_half (by positivity)
  have hN : (∫⁻ z, nearKernel r z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ P1 :=
    ENNReal.rpow_le_rpow (lintegral_nearKernel_rpow_le hr) (by norm_num)
  have hF : (∫⁻ z, farKernel r z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ P3 :=
    ENNReal.rpow_le_rpow (lintegral_farKernel_sq_le hr) (by norm_num)
  have hB1 : ∀ x, ∫⁻ y, nearKernel r (x - y) * (Ea y * G y) ≤
      P1 * ENNReal.ofReal (c₂ * S / r) := by
    intro x
    have hm : AEMeasurable (fun y => Ea y * G y) volume := (hEam.mul hGm).aemeasurable
    refine (lintegral_translate_lpProd_six hNm hm x).trans ?_
    have h6 : ∫⁻ y, (Ea y * G y) ^ (6 : ℝ) ≤ ENNReal.ofReal ((c₂ * S / r) ^ 6) := by
      refine le_trans (le_of_eq ?_) h6'
      congr 1
      funext y
      simp only [Ea, G]
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    have h6r : (∫⁻ y, (Ea y * G y) ^ (6 : ℝ)) ^ (1 / 6 : ℝ) ≤ ENNReal.ofReal (c₂ * S / r) := by
      calc _ ≤ ENNReal.ofReal ((c₂ * S / r) ^ 6) ^ (1 / 6 : ℝ) :=
            ENNReal.rpow_le_rpow h6 (by norm_num)
        _ = _ := ofReal_pow_six_rpow (by positivity)
    exact mul_le_mul' hN h6r
  have hB3 : ∀ x, ∫⁻ y, farKernel r (x - y) * G y ≤ P3 * ENNReal.ofReal (c₂ * A / r) := by
    intro x
    exact (lintegral_translate_lpProd_two hFm hGm.aemeasurable x).trans (mul_le_mul' hF hG2)
  set B := K * (P1 * ENNReal.ofReal (c₂ * S / r)) + P3 * ENNReal.ofReal (c₂ * A / r) with hB
  have hinner : ∀ x, ∫⁻ y, ENNReal.ofReal (‖x - y‖⁻¹ ^ 3 * |e y ^ 3 - e x ^ 3|) * G y ≤
      K * Ea x * (∫⁻ y, nearKernel r (x - y) * G y) + B := by
    intro x
    have hsub : Measurable (fun y : Space => x - y) := measurable_id.const_sub x
    have hm1 : Measurable (fun y => K * Ea x * (nearKernel r (x - y) * G y)) :=
      measurable_const.mul ((hNm.comp hsub).mul hGm)
    have hm3 : Measurable (fun y => farKernel r (x - y) * G y) := (hFm.comp hsub).mul hGm
    calc _ ≤ ∫⁻ y, (K * Ea x * (nearKernel r (x - y) * G y) +
              K * (nearKernel r (x - y) * (Ea y * G y))) + farKernel r (x - y) * G y := by
          apply lintegral_mono
          intro y
          have h := kernel_weight_le hr hc₁ (x - y) (he0 x) (he1 x) (he0 y) (he1 y)
            (by rw [abs_sub_comm]; exact hslope x y)
          calc ENNReal.ofReal (‖x - y‖⁻¹ ^ 3 * |e y ^ 3 - e x ^ 3|) * G y
              ≤ (K * nearKernel r (x - y) * Ea x + K * nearKernel r (x - y) * Ea y +
                  farKernel r (x - y)) * G y := by gcongr
            _ = _ := by ring
      _ = K * Ea x * (∫⁻ y, nearKernel r (x - y) * G y) +
            K * (∫⁻ y, nearKernel r (x - y) * (Ea y * G y)) +
              ∫⁻ y, farKernel r (x - y) * G y := by
          rw [lintegral_add_right _ hm3, lintegral_add_left hm1,
            lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          rw [add_assoc]
          exact add_le_add le_rfl (add_le_add (mul_le_mul' le_rfl (hB1 x)) (hB3 x))
  have hproductBound : ∫⁻ x, ∫⁻ y, (W x * Ea x) * nearKernel r (x - y) * G y ≤
      ENNReal.ofReal (S * A) * P1 * ENNReal.ofReal (c₂ * A / r) := by
    refine (lintegral_productBound_trilinear (a := fun x => W x * Ea x) (hWm.mul hEam).aemeasurable
      hGm.aemeasurable hNm.aemeasurable).trans ?_
    exact mul_le_mul' (mul_le_mul' hY hN) hG2
  calc ∫⁻ x, W x * ∫⁻ y, ENNReal.ofReal (‖x - y‖⁻¹ ^ 3 * |e y ^ 3 - e x ^ 3|) * G y
      ≤ ∫⁻ x, W x * B + K * (∫⁻ y, (W x * Ea x) * nearKernel r (x - y) * G y) := by
        apply lintegral_mono
        intro x
        have hne : W x * Ea x ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        calc W x * ∫⁻ y, ENNReal.ofReal (‖x - y‖⁻¹ ^ 3 * |e y ^ 3 - e x ^ 3|) * G y
            ≤ W x * (K * Ea x * (∫⁻ y, nearKernel r (x - y) * G y) + B) :=
              mul_le_mul' le_rfl (hinner x)
          _ = W x * B + K * ((W x * Ea x) * ∫⁻ y, nearKernel r (x - y) * G y) := by ring
          _ = _ := by
            rw [← lintegral_const_mul' _ _ hne]
            simp_rw [mul_assoc (W x * Ea x)]
    _ = (∫⁻ x, W x) * B + K * ∫⁻ x, ∫⁻ y, (W x * Ea x) * nearKernel r (x - y) * G y := by
        rw [lintegral_add_left (hWm.mul_const B), lintegral_mul_const _ hWm,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
        gcongr

end Breakdown.Internal.FarStress
