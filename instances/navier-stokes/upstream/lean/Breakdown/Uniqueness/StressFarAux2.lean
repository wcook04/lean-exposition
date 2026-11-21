import Breakdown.Uniqueness.StressFarAux

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Internal.FarStress

theorem ofReal_rpow_two_eq {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal t ^ (2 : ℝ) = ENNReal.ofReal (t ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg ht (by norm_num), Real.rpow_two]

theorem ofReal_rpow_six_eq {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal t ^ (6 : ℝ) = ENNReal.ofReal (t ^ 6) := by
  rw [ENNReal.ofReal_rpow_of_nonneg ht (by norm_num), show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

theorem ofReal_pow_rpow {t : ℝ} (ht : 0 ≤ t) (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (t ^ n) ^ p = ENNReal.ofReal (t ^ ((n : ℝ) * p)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg ht n) hp, ← Real.rpow_natCast, ← Real.rpow_mul ht]

variable {r A c₂ S : ℝ} {w : Space → Space} {e g : Space → ℝ}

theorem lintegral_flux_sq_le
    (hg : ∀ y, |g y| ≤ c₂ / r * ‖w y‖)
    (hE : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal (A ^ 2)) :
    ∫⁻ y, ENNReal.ofReal |g y| ^ (2 : ℝ) ≤ ENNReal.ofReal ((c₂ * A / r) ^ 2) := by
  have hpt : ∀ y, ENNReal.ofReal |g y| ^ (2 : ℝ) ≤
      ENNReal.ofReal ((c₂ / r) ^ 2) * ENNReal.ofReal (‖w y‖ ^ 2) := by
    intro y
    rw [ofReal_rpow_two_eq (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hg y) 2
  calc ∫⁻ y, ENNReal.ofReal |g y| ^ (2 : ℝ)
      ≤ ∫⁻ y, ENNReal.ofReal ((c₂ / r) ^ 2) * ENNReal.ofReal (‖w y‖ ^ 2) :=
        lintegral_mono fun y => hpt y
    _ = ENNReal.ofReal ((c₂ / r) ^ 2) * ∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((c₂ / r) ^ 2) * ENNReal.ofReal (A ^ 2) := by gcongr
    _ = ENNReal.ofReal ((c₂ * A / r) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

theorem lintegral_weighted_flux_six_le
    (hg : ∀ y, |g y| ≤ c₂ / r * ‖w y‖)
    (hS6 : ∫⁻ x, ENNReal.ofReal (e x ^ 2 * ‖w x‖) ^ (6 : ℝ) ≤ ENNReal.ofReal (S ^ 6)) :
    ∫⁻ y, ENNReal.ofReal (e y ^ 2 * |g y|) ^ (6 : ℝ) ≤ ENNReal.ofReal ((c₂ * S / r) ^ 6) := by
  have hpt : ∀ y, ENNReal.ofReal (e y ^ 2 * |g y|) ^ (6 : ℝ) ≤
      ENNReal.ofReal ((c₂ / r) ^ 6) * ENNReal.ofReal (e y ^ 2 * ‖w y‖) ^ (6 : ℝ) := by
    intro y
    rw [ofReal_rpow_six_eq (by positivity), ofReal_rpow_six_eq (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have he : 0 ≤ e y ^ 2 := sq_nonneg _
    calc e y ^ 2 * |g y| ≤ e y ^ 2 * (c₂ / r * ‖w y‖) := mul_le_mul_of_nonneg_left (hg y) he
      _ = c₂ / r * (e y ^ 2 * ‖w y‖) := by ring
  calc ∫⁻ y, ENNReal.ofReal (e y ^ 2 * |g y|) ^ (6 : ℝ)
      ≤ ∫⁻ y, ENNReal.ofReal ((c₂ / r) ^ 6) * ENNReal.ofReal (e y ^ 2 * ‖w y‖) ^ (6 : ℝ) :=
        lintegral_mono fun y => hpt y
    _ = ENNReal.ofReal ((c₂ / r) ^ 6) * ∫⁻ y, ENNReal.ofReal (e y ^ 2 * ‖w y‖) ^ (6 : ℝ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((c₂ / r) ^ 6) * ENNReal.ofReal (S ^ 6) := by gcongr
    _ = ENNReal.ofReal ((c₂ * S / r) ^ 6) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

theorem productBound_weight_le (hA : 0 ≤ A) (hS : 0 ≤ S) (hw : Measurable w) (he : Measurable e)
    (hE : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal (A ^ 2))
    (hS6 : ∫⁻ x, ENNReal.ofReal (e x ^ 2 * ‖w x‖) ^ (6 : ℝ) ≤ ENNReal.ofReal (S ^ 6)) :
    (∫⁻ x, (ENNReal.ofReal (‖w x‖ ^ 2) * ENNReal.ofReal (e x ^ 2)) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
      ENNReal.ofReal (S * A) := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hfm : AEMeasurable (fun x => ENNReal.ofReal (e x ^ 2 * ‖w x‖) ^ (3 / 2 : ℝ)) volume :=
    ((ENNReal.measurable_ofReal.comp ((he.pow_const 2).mul hw.norm)).pow_const _).aemeasurable
  have hkm : AEMeasurable (fun x => ENNReal.ofReal ‖w x‖ ^ (3 / 2 : ℝ)) volume :=
    ((ENNReal.measurable_ofReal.comp hw.norm).pow_const _).aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hfm hkm
  simp only [Pi.mul_apply] at h
  have e1 : ∀ x, ENNReal.ofReal (e x ^ 2 * ‖w x‖) ^ (3 / 2 : ℝ) * ENNReal.ofReal ‖w x‖ ^ (3 / 2 : ℝ) =
      (ENNReal.ofReal (‖w x‖ ^ 2) * ENNReal.ofReal (e x ^ 2)) ^ (3 / 2 : ℝ) := by
    intro x
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ e x ^ 2 * ‖w x‖),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ‖w x‖ ^ 2)]
    congr 2
    ring
  have e2 : ∀ x, (ENNReal.ofReal (e x ^ 2 * ‖w x‖) ^ (3 / 2 : ℝ)) ^ (4 : ℝ) =
      ENNReal.ofReal (e x ^ 2 * ‖w x‖) ^ (6 : ℝ) := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (ENNReal.ofReal ‖w x‖ ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ) =
      ENNReal.ofReal (‖w x‖ ^ 2) := by
    intro x
    rw [← ENNReal.rpow_mul, ← ofReal_rpow_two_eq (norm_nonneg _)]
    norm_num
  simp only [e1, e2, e3] at h
  have hS' : (∫⁻ x, ENNReal.ofReal (e x ^ 2 * ‖w x‖) ^ (6 : ℝ)) ^ (1 / 4 : ℝ) ≤
      ENNReal.ofReal (S ^ (3 / 2 : ℝ)) := by
    calc _ ≤ ENNReal.ofReal (S ^ 6) ^ (1 / 4 : ℝ) := ENNReal.rpow_le_rpow hS6 (by norm_num)
      _ = _ := by rw [ofReal_pow_rpow hS 6 (by norm_num)]; norm_num
  have hA' : (∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2)) ^ (1 / (4 / 3) : ℝ) ≤
      ENNReal.ofReal (A ^ (3 / 2 : ℝ)) := by
    calc _ ≤ ENNReal.ofReal (A ^ 2) ^ (1 / (4 / 3) : ℝ) := ENNReal.rpow_le_rpow hE (by norm_num)
      _ = _ := by rw [ofReal_pow_rpow hA 2 (by norm_num)]; norm_num
  have hprod := h.trans (mul_le_mul' hS' hA')
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hS hA] at hprod
  calc _ ≤ ENNReal.ofReal ((S * A) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) :=
        ENNReal.rpow_le_rpow hprod (by norm_num)
    _ = _ := ofReal_rpow_three_halves (by positivity)

end Breakdown.Internal.FarStress
