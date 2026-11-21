import Breakdown.Uniqueness.ProductBound

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Internal.FarStress

def nearKernel (r : ℝ) (z : Space) : ℝ≥0∞ :=
  (Metric.ball (0 : Space) r).indicator (fun z => ENNReal.ofReal (‖z‖⁻¹ ^ 2)) z

def farKernel (r : ℝ) (z : Space) : ℝ≥0∞ :=
  (Metric.ball (0 : Space) r)ᶜ.indicator (fun z => ENNReal.ofReal (‖z‖⁻¹ ^ 3)) z

theorem measurable_nearKernel (r : ℝ) : Measurable (nearKernel r) := by
  unfold nearKernel
  exact Measurable.indicator (by fun_prop) measurableSet_ball

theorem measurable_farKernel (r : ℝ) : Measurable (farKernel r) := by
  unfold farKernel
  exact Measurable.indicator (by fun_prop) measurableSet_ball.compl

theorem lintegral_nearKernel_rpow_le {r : ℝ} (hr : 0 < r) :
    ∫⁻ z, nearKernel r z ^ (6 / 5 : ℝ) ≤ ENNReal.ofReal (20 * π / 3 * r ^ (3 / 5 : ℝ)) := by
  have h : (fun z => nearKernel r z ^ (6 / 5 : ℝ)) =
      (Metric.ball (0 : Space) r).indicator
        (fun z => ENNReal.ofReal (‖z‖⁻¹ ^ 2) ^ (6 / 5 : ℝ)) := by
    funext z
    by_cases hz : z ∈ Metric.ball (0 : Space) r
    · simp only [nearKernel, Set.indicator_of_mem hz]
    · simp only [nearKernel, Set.indicator_of_notMem hz]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
  rw [h, lintegral_indicator measurableSet_ball]
  exact lintegral_inner_kernel_le hr

theorem lintegral_farKernel_sq_le {r : ℝ} (hr : 0 < r) :
    ∫⁻ z, farKernel r z ^ (2 : ℝ) ≤ ENNReal.ofReal (4 * π / 3 * r⁻¹ ^ 3) := by
  have h : (fun z => farKernel r z ^ (2 : ℝ)) =
      (Metric.ball (0 : Space) r)ᶜ.indicator
        (fun z => ENNReal.ofReal (‖z‖⁻¹ ^ 3) ^ (2 : ℝ)) := by
    funext z
    by_cases hz : z ∈ (Metric.ball (0 : Space) r)ᶜ
    · simp only [farKernel, Set.indicator_of_mem hz]
    · simp only [farKernel, Set.indicator_of_notMem hz]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
  rw [h, lintegral_indicator measurableSet_ball.compl]
  exact lintegral_outer_kernel_le hr

theorem lintegral_translate_lpProd_six {k f : Space → ℝ≥0∞} (hk : Measurable k)
    (hf : AEMeasurable f volume) (x : Space) :
    ∫⁻ y, k (x - y) * f y ≤
      (∫⁻ z, k z ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) * (∫⁻ y, f y ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by
  have hpq : (6 / 5 : ℝ).HolderConjugate 6 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hkx : AEMeasurable (fun y => k (x - y)) volume :=
    (hk.comp (measurable_id.const_sub x)).aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hkx hf
  have e : ∫⁻ y, k (x - y) ^ (6 / 5 : ℝ) = ∫⁻ z, k z ^ (6 / 5 : ℝ) :=
    lintegral_sub_left_eq_self (fun z => k z ^ (6 / 5 : ℝ)) x
  simp only [Pi.mul_apply] at h
  rw [e, show (1 / (6 / 5 : ℝ)) = 5 / 6 by norm_num] at h
  exact h

theorem lintegral_translate_lpProd_two {k f : Space → ℝ≥0∞} (hk : Measurable k)
    (hf : AEMeasurable f volume) (x : Space) :
    ∫⁻ y, k (x - y) * f y ≤
      (∫⁻ z, k z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∫⁻ y, f y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hkx : AEMeasurable (fun y => k (x - y)) volume :=
    (hk.comp (measurable_id.const_sub x)).aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hkx hf
  have e : ∫⁻ y, k (x - y) ^ (2 : ℝ) = ∫⁻ z, k z ^ (2 : ℝ) :=
    lintegral_sub_left_eq_self (fun z => k z ^ (2 : ℝ)) x
  simp only [Pi.mul_apply] at h
  rw [e] at h
  exact h

theorem ofReal_sq_rpow_half {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (t ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal t := by
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg t) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq ht]

theorem ofReal_pow_six_rpow {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (t ^ 6) ^ (1 / 6 : ℝ) = ENNReal.ofReal t := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul ht]
  norm_num

theorem ofReal_rpow_three_halves {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (t ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = ENNReal.ofReal t := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul ht]
  norm_num

theorem abs_cube_sub_le_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |b ^ 3 - a ^ 3| ≤ 1 := by
  have h1 : a ^ 3 ≤ 1 := pow_le_one₀ ha0 ha1
  have h2 : b ^ 3 ≤ 1 := pow_le_one₀ hb0 hb1
  have h3 : 0 ≤ a ^ 3 := by positivity
  have h4 : 0 ≤ b ^ 3 := by positivity
  rw [abs_le]
  constructor <;> linarith

theorem abs_cube_sub_le {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    |b ^ 3 - a ^ 3| ≤ 3 / 2 * |b - a| * (a ^ 2 + b ^ 2) := by
  have e : b ^ 3 - a ^ 3 = (b - a) * (a ^ 2 + a * b + b ^ 2) := by ring
  have hq : 0 ≤ a ^ 2 + a * b + b ^ 2 := by positivity
  rw [e, abs_mul, abs_of_nonneg hq]
  have hab : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]
  have hd : 0 ≤ |b - a| := abs_nonneg _
  nlinarith

theorem kernel_weight_le {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) {a b : ℝ} (z : Space)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hslope : |b - a| ≤ c * ‖z‖ / r) :
    ENNReal.ofReal (‖z‖⁻¹ ^ 3 * |b ^ 3 - a ^ 3|) ≤
      ENNReal.ofReal (3 / 2 * c / r) * nearKernel r z * ENNReal.ofReal (a ^ 2) +
        ENNReal.ofReal (3 / 2 * c / r) * nearKernel r z * ENNReal.ofReal (b ^ 2) +
          farKernel r z := by
  by_cases hz : ‖z‖ < r
  · have hm : z ∈ Metric.ball (0 : Space) r := mem_ball_zero_iff.mpr hz
    have hm' : z ∉ (Metric.ball (0 : Space) r)ᶜ := fun h => h hm
    simp only [nearKernel, farKernel, Set.indicator_of_mem hm, Set.indicator_of_notMem hm',
      add_zero]
    have hK : 0 ≤ 3 / 2 * c / r := by positivity
    have hn2 : (0 : ℝ) ≤ ‖z‖⁻¹ ^ 2 := by positivity
    have hKn : (0 : ℝ) ≤ 3 / 2 * c / r * ‖z‖⁻¹ ^ 2 := by positivity
    have e : ENNReal.ofReal (3 / 2 * c / r) * ENNReal.ofReal (‖z‖⁻¹ ^ 2) * ENNReal.ofReal (a ^ 2) +
        ENNReal.ofReal (3 / 2 * c / r) * ENNReal.ofReal (‖z‖⁻¹ ^ 2) * ENNReal.ofReal (b ^ 2) =
        ENNReal.ofReal (3 / 2 * c / r * ‖z‖⁻¹ ^ 2 * a ^ 2 + 3 / 2 * c / r * ‖z‖⁻¹ ^ 2 * b ^ 2) := by
      rw [ENNReal.ofReal_add (mul_nonneg hKn (sq_nonneg a)) (mul_nonneg hKn (sq_nonneg b)),
        ENNReal.ofReal_mul hKn, ENNReal.ofReal_mul hKn, ENNReal.ofReal_mul hK]
    rw [e]
    apply ENNReal.ofReal_le_ofReal
    by_cases h0 : z = 0
    · simp [h0]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr h0
    have hc3 := abs_cube_sub_le ha0 hb0 (a := a) (b := b)
    have hinv : 0 ≤ ‖z‖⁻¹ ^ 3 := by positivity
    calc ‖z‖⁻¹ ^ 3 * |b ^ 3 - a ^ 3| ≤ ‖z‖⁻¹ ^ 3 * (3 / 2 * (c * ‖z‖ / r) * (a ^ 2 + b ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hinv
          apply hc3.trans
          gcongr
      _ = 3 / 2 * c / r * ‖z‖⁻¹ ^ 2 * a ^ 2 + 3 / 2 * c / r * ‖z‖⁻¹ ^ 2 * b ^ 2 := by
          field_simp
  · have hm : z ∉ Metric.ball (0 : Space) r := fun h => hz (mem_ball_zero_iff.mp h)
    have hm' : z ∈ (Metric.ball (0 : Space) r)ᶜ := hm
    simp only [nearKernel, farKernel, Set.indicator_of_mem hm', Set.indicator_of_notMem hm,
      mul_zero, zero_mul, zero_add]
    apply ENNReal.ofReal_le_ofReal
    have hinv : 0 ≤ ‖z‖⁻¹ ^ 3 := by positivity
    calc ‖z‖⁻¹ ^ 3 * |b ^ 3 - a ^ 3| ≤ ‖z‖⁻¹ ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left (abs_cube_sub_le_one ha0 ha1 hb0 hb1) hinv
      _ = ‖z‖⁻¹ ^ 3 := mul_one _

end Breakdown.Internal.FarStress
