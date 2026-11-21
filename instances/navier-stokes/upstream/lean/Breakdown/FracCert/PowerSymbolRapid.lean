import Breakdown.FracCert.PowerSymbolSplit
import Breakdown.Frac.OpExports
import Breakdown.Frac.NNiceField
import Breakdown.FreqTr.NiceApprox

open scoped ContDiff SchwartzMap
open MeasureTheory Real Filter Topology
open Breakdown.Freq.Internal.NiceApprox

noncomputable section

namespace Breakdown.SteadyCert.PowerSymbolRapid.Internal

def edgeWeight (α : ℝ) (z : Space) : ℝ :=
  min (‖z‖ ^ (3 - (3 + 2 * α))) (‖z‖ ^ (2 - (3 + 2 * α)))

theorem edgeWeight_nonneg (α : ℝ) (z : Space) : 0 ≤ edgeWeight α z :=
  le_min (rpow_nonneg (norm_nonneg _) _) (rpow_nonneg (norm_nonneg _) _)

theorem one_add_le_of_far (x z : Space) (hz : 1 ≤ ‖z‖) :
    1 + ‖x‖ ≤ 2 * ‖z‖ * (1 + ‖x + z‖) := by
  have h : ‖x‖ ≤ ‖x + z‖ + ‖z‖ := by
    have := norm_sub_le (x + z) z
    simpa using this
  have h0 := norm_nonneg (x + z)
  nlinarith

theorem one_add_le_of_near (x y : Space) (h : ‖y - x‖ ≤ 1) : 1 + ‖x‖ ≤ 2 * (1 + ‖y‖) := by
  have : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by
    have := norm_sub_le y (y - x)
    simpa using this
  have := norm_nonneg y
  linarith

theorem weight_shift {a c : ℝ} (ha : 0 < a) (h : a ≤ 2 * c) :
    c ^ (-(10 : ℝ)) ≤ 2 ^ (10 : ℝ) * a ^ (-(10 : ℝ)) := by
  have hc : 0 < c := by linarith
  have h1 : (2 * c) ^ (-(10 : ℝ)) ≤ a ^ (-(10 : ℝ)) :=
    rpow_le_rpow_of_nonpos ha h (by norm_num)
  rw [mul_rpow (by norm_num) hc.le] at h1
  have h2 : (2 : ℝ) ^ (10 : ℝ) * (2 : ℝ) ^ (-(10 : ℝ)) = 1 := by
    rw [← rpow_add (by norm_num)]; norm_num
  have h3 : (0 : ℝ) ≤ 2 ^ (10 : ℝ) := by positivity
  calc c ^ (-(10 : ℝ)) = 2 ^ (10 : ℝ) * (2 ^ (-(10 : ℝ)) * c ^ (-(10 : ℝ))) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ 2 ^ (10 : ℝ) * a ^ (-(10 : ℝ)) := mul_le_mul_of_nonneg_left h1 h3

theorem far_weight (α : ℝ) (hα2 : α < 3 / 2) (hα1 : 1 < α) {a b t : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ht : 1 ≤ t) (h : a ≤ 2 * t * b) :
    t ^ (-(3 + 2 * α)) * b ^ (-(10 : ℝ)) ≤
      2 ^ (3 + 2 * α) * (a ^ (-(3 + 2 * α)) * b ^ (-(4 : ℝ))) := by
  set s := 3 + 2 * α with hs
  have hs0 : 0 ≤ s := by linarith
  have key : a ^ s * b ^ (4 : ℝ) ≤ 2 ^ s * t ^ s * b ^ (10 : ℝ) := by
    calc a ^ s * b ^ (4 : ℝ) ≤ (2 * t * b) ^ s * b ^ (4 : ℝ) := by
          gcongr
      _ = 2 ^ s * t ^ s * (b ^ s * b ^ (4 : ℝ)) := by
          rw [mul_rpow (by positivity) (by linarith), mul_rpow (by norm_num) (by linarith)]; ring
      _ ≤ 2 ^ s * t ^ s * (b ^ (6 : ℝ) * b ^ (4 : ℝ)) := by
          gcongr
          linarith
      _ = 2 ^ s * t ^ s * b ^ (10 : ℝ) := by
          rw [← rpow_add (by linarith)]; norm_num
  have hta : 0 < t ^ s := rpow_pos_of_pos (by linarith) _
  have haa : 0 < a ^ s := rpow_pos_of_pos (by linarith) _
  have hb4 : 0 < b ^ (4 : ℝ) := rpow_pos_of_pos (by linarith) _
  have hb10 : 0 < b ^ (10 : ℝ) := rpow_pos_of_pos (by linarith) _
  rw [rpow_neg (by linarith), rpow_neg (by linarith), rpow_neg (by linarith), rpow_neg (by linarith),
    ← mul_inv, ← mul_inv, ← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem pointwise_bound (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2) (f : Space → Space)
    (hf : ContDiff ℝ 3 f) (B : ℝ) (hB : 0 ≤ B)
    (h0 : ∀ y, ‖f y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ)))
    (h1 : ∀ y, ‖fderiv ℝ f y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ)))
    (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ)))
    (h3 : ∀ y, ‖iteratedFDeriv ℝ 3 f y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ))) (x z : Space) :
    ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖ ≤
      (2 ^ (10 : ℝ) + 3 + 2 ^ (3 + 2 * α)) * B *
        ((1 + ‖x‖) ^ (-(3 + 2 * α)) * (edgeWeight α z + (1 + ‖x + z‖) ^ (-(4 : ℝ)))) := by
  set s := 3 + 2 * α with hs
  have hx1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  set W := (1 + ‖x‖) ^ (-s) with hW
  have hW0 : 0 ≤ W := rpow_nonneg (by linarith) _
  have hE0 := edgeWeight_nonneg α z
  have hQ0 : 0 ≤ (1 + ‖x + z‖) ^ (-(4 : ℝ)) := rpow_nonneg (by linarith [norm_nonneg (x + z)]) _
  have hK0 : 0 ≤ ‖z‖ ^ (-s) := rpow_nonneg (norm_nonneg _) _
  have h10 : (1 + ‖x‖) ^ (-(10 : ℝ)) ≤ W := rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hp10 : (0 : ℝ) ≤ 2 ^ (10 : ℝ) := by positivity
  have hps : (0 : ℝ) ≤ 2 ^ s := by positivity
  have hBW : 0 ≤ B * W := mul_nonneg hB hW0
  rcases le_total ‖z‖ 1 with hz | hz
  · have hC : ∀ y ∈ Metric.closedBall x ‖z‖, ‖iteratedFDeriv ℝ 3 f y‖ ≤
        B * (2 ^ (10 : ℝ) * (1 + ‖x‖) ^ (-(10 : ℝ))) := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      refine (h3 y).trans (mul_le_mul_of_nonneg_left ?_ hB)
      exact weight_shift (by linarith) (one_add_le_of_near x y (hy.trans hz))
    have hR := remainderBound f hf x z _ hC
    have hnear : ‖z‖ ^ (-s) * ‖secondOrderRemainder f x z‖ ≤
        B * (2 ^ (10 : ℝ) * (1 + ‖x‖) ^ (-(10 : ℝ))) * edgeWeight α z := by
      rcases (norm_nonneg z).eq_or_lt with h | h
      · rw [← h, zero_rpow (by linarith), zero_mul]
        exact mul_nonneg (mul_nonneg hB (mul_nonneg hp10 (rpow_nonneg (by linarith) _))) hE0
      · have he : ‖z‖ ^ (-s) * ‖z‖ ^ 3 = ‖z‖ ^ (3 - s) := by
          rw [← rpow_natCast, ← rpow_add h]; norm_num; ring_nf
        have hmin : ‖z‖ ^ (3 - s) ≤ edgeWeight α z :=
          le_min le_rfl (rpow_le_rpow_of_exponent_ge h hz (by linarith))
        calc ‖z‖ ^ (-s) * ‖secondOrderRemainder f x z‖
            ≤ ‖z‖ ^ (-s) * (B * (2 ^ (10 : ℝ) * (1 + ‖x‖) ^ (-(10 : ℝ))) * ‖z‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hR hK0
          _ = B * (2 ^ (10 : ℝ) * (1 + ‖x‖) ^ (-(10 : ℝ))) * (‖z‖ ^ (-s) * ‖z‖ ^ 3) := by ring
          _ ≤ B * (2 ^ (10 : ℝ) * (1 + ‖x‖) ^ (-(10 : ℝ))) * edgeWeight α z := by
              rw [he]
              exact mul_le_mul_of_nonneg_left hmin
                (mul_nonneg hB (mul_nonneg hp10 (rpow_nonneg (by linarith) _)))
    have hA : B * (2 ^ (10 : ℝ) * (1 + ‖x‖) ^ (-(10 : ℝ))) * edgeWeight α z ≤
        2 ^ (10 : ℝ) * (B * W) * edgeWeight α z := by
      have : B * (2 ^ (10 : ℝ) * (1 + ‖x‖) ^ (-(10 : ℝ))) ≤ 2 ^ (10 : ℝ) * (B * W) := by
        nlinarith [mul_le_mul_of_nonneg_left h10 (mul_nonneg hB hp10)]
      exact mul_le_mul_of_nonneg_right this hE0
    have hfin : 2 ^ (10 : ℝ) * (B * W) * edgeWeight α z ≤
        (2 ^ (10 : ℝ) + 3 + 2 ^ s) * B * (W * (edgeWeight α z + (1 + ‖x + z‖) ^ (-(4 : ℝ)))) := by
      have e1 := mul_nonneg (mul_nonneg hBW hE0) (by linarith : (0 : ℝ) ≤ 3 + 2 ^ s)
      have e2 := mul_nonneg (mul_nonneg hBW hQ0) (by linarith : (0 : ℝ) ≤ 2 ^ (10 : ℝ) + 3 + 2 ^ s)
      nlinarith
    linarith
  · have hR := FracInternal.NiceField.remainder_far_bound f x z hz
    have hz0 : 0 < ‖z‖ := by linarith
    have hsum : ‖f x‖ + ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖ ≤ 3 * (B * W) := by
      have := h0 x; have := h1 x; have := h2 x
      have := mul_le_mul_of_nonneg_left h10 hB
      linarith
    have he : ‖z‖ ^ (-s) * ‖z‖ ^ 2 = ‖z‖ ^ (2 - s) := by
      rw [← rpow_natCast, ← rpow_add hz0]; norm_num; ring_nf
    have hmin : ‖z‖ ^ (2 - s) = edgeWeight α z := by
      unfold edgeWeight
      rw [min_eq_right (rpow_le_rpow_of_exponent_le hz (by linarith))]
    have hfar1 : ‖z‖ ^ (-s) * ‖f (x + z)‖ ≤ 2 ^ s * (B * (W * (1 + ‖x + z‖) ^ (-(4 : ℝ)))) := by
      have hw := far_weight α hα2 hα1 hx1 (by linarith [norm_nonneg (x + z)]) hz
        (one_add_le_of_far x z hz)
      calc ‖z‖ ^ (-s) * ‖f (x + z)‖ ≤ ‖z‖ ^ (-s) * (B * (1 + ‖x + z‖) ^ (-(10 : ℝ))) :=
            mul_le_mul_of_nonneg_left (h0 _) hK0
        _ = B * (‖z‖ ^ (-s) * (1 + ‖x + z‖) ^ (-(10 : ℝ))) := by ring
        _ ≤ B * (2 ^ s * (W * (1 + ‖x + z‖) ^ (-(4 : ℝ)))) := mul_le_mul_of_nonneg_left hw hB
        _ = 2 ^ s * (B * (W * (1 + ‖x + z‖) ^ (-(4 : ℝ)))) := by ring
    have hfar2 : ‖z‖ ^ (-s) * ((‖f x‖ + ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖) * ‖z‖ ^ 2) ≤
        3 * (B * W) * edgeWeight α z := by
      calc ‖z‖ ^ (-s) * ((‖f x‖ + ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖) * ‖z‖ ^ 2)
          = (‖f x‖ + ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖) * (‖z‖ ^ (-s) * ‖z‖ ^ 2) := by ring
        _ ≤ 3 * (B * W) * edgeWeight α z := by
            rw [he, hmin]; exact mul_le_mul_of_nonneg_right hsum hE0
    have htot : ‖z‖ ^ (-s) * ‖secondOrderRemainder f x z‖ ≤
        2 ^ s * (B * (W * (1 + ‖x + z‖) ^ (-(4 : ℝ)))) + 3 * (B * W) * edgeWeight α z := by
      have := mul_le_mul_of_nonneg_left hR hK0
      rw [mul_add] at this
      linarith
    have e1 := mul_nonneg (mul_nonneg hBW hE0) (by linarith : (0 : ℝ) ≤ 2 ^ (10 : ℝ) + 2 ^ s)
    have e2 := mul_nonneg (mul_nonneg hBW hQ0) (by linarith : (0 : ℝ) ≤ 2 ^ (10 : ℝ) + 3)
    nlinarith

end Breakdown.SteadyCert.PowerSymbolRapid.Internal

namespace Breakdown.SteadyCert.PowerSymbolRapid.Internal

theorem integrable_near_far {f : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    {a b C : ℝ} (ha : a < 3) (hb : 3 < b) (hnear : ∀ z : Space, ‖z‖ ≤ 1 → ‖f z‖ ≤ C * ‖z‖ ^ (-a))
    (hfar : ∀ z : Space, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ (-b)) : Integrable f := by
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hC : 0 ≤ C := by
    have hn : ‖(EuclideanSpace.single 0 1 : Space)‖ = 1 := by simp
    have := hfar (EuclideanSpace.single 0 1) hn.ge
    rw [hn, one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hball : IntegrableOn f (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := C) (by rw [hfin]; norm_num)
      (by rw [hfin]; exact_mod_cast ha) ?_ hf
    refine (ae_restrict_mem measurableSet_ball).mono fun z hz => hnear z ?_
    have : ‖z‖ < 1 := by simpa using hz
    exact this.le
  have hcomp : IntegrableOn f (Metric.ball (0 : Space) 1)ᶜ volume := by
    have hint : Integrable (fun z : Space => (1 + ‖z‖) ^ (-b)) :=
      integrable_one_add_norm (by rw [hfin]; exact_mod_cast hb)
    refine Integrable.mono' ((hint.const_mul (C * 2 ^ b)).integrableOn) hf.restrict ?_
    refine (ae_restrict_mem measurableSet_ball.compl).mono fun z hz => ?_
    have hz1 : 1 ≤ ‖z‖ := by simpa using hz
    have hzpos : 0 < ‖z‖ := by linarith
    have key : ‖z‖ ^ (-b) ≤ 2 ^ b * (1 + ‖z‖) ^ (-b) := by
      rw [rpow_neg hzpos.le, rpow_neg (by positivity), ← div_eq_mul_inv,
        inv_le_iff_one_le_mul₀ (by positivity), div_mul_eq_mul_div, one_le_div (by positivity),
        ← mul_rpow (by norm_num) hzpos.le]
      exact rpow_le_rpow (by positivity) (by linarith) (by linarith)
    calc ‖f z‖ ≤ C * ‖z‖ ^ (-b) := hfar z hz1
      _ ≤ C * (2 ^ b * (1 + ‖z‖) ^ (-b)) := mul_le_mul_of_nonneg_left key hC
      _ = C * 2 ^ b * (1 + ‖z‖) ^ (-b) := by ring
  have := hball.union hcomp
  rwa [Set.union_compl_self, integrableOn_univ] at this

theorem edgeWeight_integrable (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2) :
    Integrable (edgeWeight α) := by
  have hm : AEStronglyMeasurable (edgeWeight α) volume :=
    ((measurable_norm.pow_const _).min (measurable_norm.pow_const _)).aestronglyMeasurable
  refine integrable_near_far hm (a := 2 * α) (b := 1 + 2 * α) (C := 1) (by linarith) (by linarith)
    (fun z _ => ?_) (fun z _ => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (edgeWeight_nonneg α z), one_mul]
    refine (min_le_left _ _).trans (le_of_eq ?_)
    congr 1; ring
  · rw [Real.norm_eq_abs, abs_of_nonneg (edgeWeight_nonneg α z), one_mul]
    refine (min_le_right _ _).trans (le_of_eq ?_)
    congr 1; ring

def domFun (α : ℝ) (x z : Space) : ℝ :=
  (1 + ‖x‖) ^ (-(3 + 2 * α)) * (edgeWeight α z + (1 + ‖x + z‖) ^ (-(4 : ℝ)))

def domTotal (α : ℝ) : ℝ :=
  (∫ z, edgeWeight α z) + ∫ z : Space, (1 + ‖z‖) ^ (-(4 : ℝ))

theorem integrable_four : Integrable (fun z : Space => (1 + ‖z‖) ^ (-(4 : ℝ))) :=
  integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)

theorem domFun_integrable (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2) (x : Space) :
    Integrable (domFun α x) :=
  ((edgeWeight_integrable α hα1 hα2).add
    (integrable_four.comp_add_left x)).const_mul _

theorem domFun_integral (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2) (x : Space) :
    ∫ z, domFun α x z = (1 + ‖x‖) ^ (-(3 + 2 * α)) * domTotal α := by
  unfold domFun domTotal
  rw [integral_const_mul, integral_add (edgeWeight_integrable α hα1 hα2)
    (integrable_four.comp_add_left x),
    integral_add_left_eq_self (fun z : Space => (1 + ‖z‖) ^ (-(4 : ℝ))) x]

theorem kernel_norm (α : ℝ) (v z : Space) :
    ‖‖z‖ ^ (-(3 + 2 * α)) • v‖ = ‖z‖ ^ (-(3 + 2 * α)) * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (norm_nonneg _) _)]

theorem power_bound (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2) (f : Space → Space)
    (hf : ContDiff ℝ 3 f) (B : ℝ) (hB : 0 ≤ B)
    (h0 : ∀ y, ‖f y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ)))
    (h1 : ∀ y, ‖fderiv ℝ f y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ)))
    (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ)))
    (h3 : ∀ y, ‖iteratedFDeriv ℝ 3 f y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ))) (x : Space) :
    ‖fractionalPowerAt α f x‖ ≤
      |(fractionalNormalizer α)⁻¹| * ((2 ^ (10 : ℝ) + 3 + 2 ^ (3 + 2 * α)) * B) * domTotal α *
        (1 + ‖x‖) ^ (-(3 + 2 * α)) := by
  unfold fractionalPowerAt
  rw [norm_smul, Real.norm_eq_abs]
  have hc : 0 ≤ (2 ^ (10 : ℝ) + 3 + 2 ^ (3 + 2 * α)) * B := by positivity
  have key : ‖∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder f x z‖ ≤
      (2 ^ (10 : ℝ) + 3 + 2 ^ (3 + 2 * α)) * B * ((1 + ‖x‖) ^ (-(3 + 2 * α)) * domTotal α) := by
    calc ‖∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder f x z‖
        ≤ ∫ z : Space, ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder f x z‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ z, (2 ^ (10 : ℝ) + 3 + 2 ^ (3 + 2 * α)) * B * domFun α x z := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
            ((domFun_integrable α hα1 hα2 x).const_mul _) (Filter.Eventually.of_forall fun z => ?_)
          dsimp only
          rw [kernel_norm]
          exact pointwise_bound α hα1 hα2 f hf B hB h0 h1 h2 h3 x z
      _ = _ := by rw [integral_const_mul, domFun_integral α hα1 hα2 x]
  calc |(fractionalNormalizer α)⁻¹| * ‖∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder f x z‖
      ≤ |(fractionalNormalizer α)⁻¹| *
          ((2 ^ (10 : ℝ) + 3 + 2 ^ (3 + 2 * α)) * B * ((1 + ‖x‖) ^ (-(3 + 2 * α)) * domTotal α)) :=
        mul_le_mul_of_nonneg_left key (abs_nonneg _)
    _ = _ := by ring

end Breakdown.SteadyCert.PowerSymbolRapid.Internal

namespace Breakdown.SteadyCert.PowerSymbolRapid.Internal

theorem le_weight {a S : ℝ} (y : Space) (h : (1 + ‖y‖) ^ 10 * a ≤ S) :
    a ≤ S * (1 + ‖y‖) ^ (-(10 : ℝ)) := by
  have hp : 0 < (1 + ‖y‖) ^ 10 := by positivity
  have e : (1 + ‖y‖) ^ (-(10 : ℝ)) = ((1 + ‖y‖) ^ 10)⁻¹ := by
    rw [rpow_neg (by positivity)]
    norm_cast
  rw [e, ← div_eq_mul_inv, le_div_iff₀ hp]
  linarith [mul_comm ((1 + ‖y‖) ^ 10) a]

theorem nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

theorem bump_bound : ∃ Bb : ℕ → ℝ, (∀ i, 0 ≤ Bb i) ∧ ∀ R : ℝ, 1 ≤ R → ∀ (i : ℕ) (y : Space),
    ‖iteratedFDeriv ℝ i (fun y : Space => stdBump (R⁻¹ • y)) y‖ ≤ Bb i := by
  have hB : ∀ i : ℕ, ∃ B : ℝ, ∀ z, ‖iteratedFDeriv ℝ i stdBump z‖ ≤ B := fun i =>
    (stdBump.contDiff.continuous_iteratedFDeriv (nat_le_top i)).norm.bounded_above_of_compact_support
      (stdBump.hasCompactSupport.iteratedFDeriv i).norm |>.imp fun B hB z => by
        simpa using hB z
  choose B hB using hB
  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  refine ⟨B, hB0, fun R hR i y => ?_⟩
  set L : Space →L[ℝ] Space := R⁻¹ • ContinuousLinearMap.id ℝ Space with hLdef
  have e : (fun y : Space => stdBump (R⁻¹ • y)) = ⇑stdBump ∘ ⇑L := rfl
  rw [e, L.iteratedFDeriv_comp_right stdBump.contDiff y (nat_le_top i)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hL : ‖L‖ ≤ 1 := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR0)]
    calc R⁻¹ * ‖ContinuousLinearMap.id ℝ Space‖ ≤ 1 * 1 :=
          mul_le_mul (inv_le_one_of_one_le₀ hR) ContinuousLinearMap.norm_id_le (norm_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  calc ‖iteratedFDeriv ℝ i stdBump (L y)‖ * ∏ _j : Fin i, ‖L‖ ≤ B i * 1 :=
        mul_le_mul (hB i _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL))
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) (hB0 i)
    _ = B i := mul_one _

theorem cut_weight (A : 𝓢(Space, Space)) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ y,
    ‖iteratedFDeriv ℝ n (cutField A R) y‖ ≤ C * (1 + ‖y‖) ^ (-(10 : ℝ)) := by
  have hA : ContDiff ℝ ∞ (A : Space → Space) := A.smooth ⊤
  obtain ⟨Bb, hBb0, hBb⟩ := bump_bound
  have hS : ∀ j : ℕ, ∃ S : ℝ, ∀ y, (1 + ‖y‖) ^ 10 * ‖iteratedFDeriv ℝ j A y‖ ≤ S := fun j =>
    ⟨_, fun y => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (10, j)) le_rfl le_rfl A y⟩
  choose S hS using hS
  have hS0 : ∀ j, 0 ≤ S j := fun j =>
    (mul_nonneg (by positivity) (norm_nonneg _)).trans (hS j 0)
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Bb i * S (n - i),
    Finset.sum_nonneg fun i _ => by have := hBb0 i; have := hS0 (n - i); positivity, fun R hR y => ?_⟩
  have hw : 0 ≤ (1 + ‖y‖) ^ (-(10 : ℝ)) := rpow_nonneg (by positivity) _
  have hAb : ∀ j, ‖iteratedFDeriv ℝ j A y‖ ≤ S j * (1 + ‖y‖) ^ (-(10 : ℝ)) := fun j =>
    le_weight y (hS j y)
  have hχc : ContDiff ℝ ∞ (fun y : Space => stdBump (R⁻¹ • y)) :=
    stdBump.contDiff.comp (contDiff_id.const_smul R⁻¹)
  have hcut : cutField A R = fun x => stdBump (R⁻¹ • x) • A x := rfl
  rw [hcut]
  refine (norm_iteratedFDeriv_smul_le hχc hA y (nat_le_top n)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : Space => stdBump (R⁻¹ • y)) y‖ *
        ‖iteratedFDeriv ℝ (n - i) A y‖
      ≤ (n.choose i : ℝ) * Bb i * (S (n - i) * (1 + ‖y‖) ^ (-(10 : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hBb R hR i y) (Nat.cast_nonneg _)) (hAb _)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hBb0 i))
    _ = (n.choose i : ℝ) * Bb i * S (n - i) * (1 + ‖y‖) ^ (-(10 : ℝ)) := by ring

theorem cut_hyps (A : 𝓢(Space, Space)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R →
    (∀ y, ‖cutField A R y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ))) ∧
    (∀ y, ‖fderiv ℝ (cutField A R) y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ))) ∧
    (∀ y, ‖iteratedFDeriv ℝ 2 (cutField A R) y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ))) ∧
    (∀ y, ‖iteratedFDeriv ℝ 3 (cutField A R) y‖ ≤ B * (1 + ‖y‖) ^ (-(10 : ℝ))) := by
  obtain ⟨C0, h00, hc0⟩ := cut_weight A 0
  obtain ⟨C1, h01, hc1⟩ := cut_weight A 1
  obtain ⟨C2, h02, hc2⟩ := cut_weight A 2
  obtain ⟨C3, h03, hc3⟩ := cut_weight A 3
  refine ⟨C0 + C1 + C2 + C3, by positivity, fun R hR => ⟨fun y => ?_, fun y => ?_, fun y => ?_,
    fun y => ?_⟩⟩ <;>
  · have hw : 0 ≤ (1 + ‖y‖) ^ (-(10 : ℝ)) := rpow_nonneg (by positivity) _
    first
    | (have := hc0 R hR y; rw [norm_iteratedFDeriv_zero] at this; nlinarith)
    | (have := hc1 R hR y; rw [norm_iteratedFDeriv_one] at this; nlinarith)
    | (have := hc2 R hR y; nlinarith)
    | (have := hc3 R hR y; nlinarith)

theorem remainder_eventually (A : 𝓢(Space, Space)) (x z : Space) :
    ∀ᶠ n : ℕ in atTop, secondOrderRemainder (cutField A ((n : ℝ) + 1)) x z =
      secondOrderRemainder A x z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ + ‖z‖)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hR : 0 < (n : ℝ) + 1 := by positivity
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hx : x ∈ Metric.ball (0 : Space) ((n : ℝ) + 1) := by
    rw [mem_ball_zero_iff]; linarith [norm_nonneg z]
  have hxz : x + z ∈ Metric.ball (0 : Space) ((n : ℝ) + 1) := by
    rw [mem_ball_zero_iff]; linarith [norm_add_le x z]
  have hev : cutField A ((n : ℝ) + 1) =ᶠ[𝓝 x] A := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact sub_eq_zero.mp (cutField_sub_zero_on A hR y hy)
  unfold secondOrderRemainder
  rw [hev.fderiv_eq, (hev.iteratedFDeriv ℝ 2).eq_of_nhds, hev.eq_of_nhds,
    sub_eq_zero.mp (cutField_sub_zero_on A hR _ hxz)]

theorem continuous_remainder (f : Space → Space) (hf : Continuous f) (x : Space) :
    Continuous (fun z => secondOrderRemainder f x z) := by
  unfold secondOrderRemainder
  have hsh : Continuous (fun z : Space => f (x + z)) := hf.comp (continuous_const.add continuous_id)
  exact ((hsh.sub continuous_const).sub (fderiv ℝ f x).continuous).sub
    (show Continuous fun z : Space => (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z] from by fun_prop)

theorem power_tendsto (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2) (A : 𝓢(Space, Space)) (x : Space) :
    Tendsto (fun n : ℕ => fractionalPowerAt α (cutField A ((n : ℝ) + 1)) x) atTop
      (𝓝 (fractionalPowerAt α A x)) := by
  obtain ⟨B, hB, hb⟩ := cut_hyps A
  have hA : ContDiff ℝ ∞ (A : Space → Space) := A.smooth ⊤
  unfold fractionalPowerAt
  refine Tendsto.const_smul ?_ _
  refine tendsto_integral_of_dominated_convergence
    (fun z => (2 ^ (10 : ℝ) + 3 + 2 ^ (3 + 2 * α)) * B * domFun α x z) (fun n => ?_)
    ((domFun_integrable α hα1 hα2 x).const_mul _) (fun n => ?_) ?_
  · exact ((measurable_norm.pow_const _).aestronglyMeasurable).smul
      (continuous_remainder _ (contDiff_cutField hA _).continuous x).aestronglyMeasurable
  · have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨e0, e1, e2, e3⟩ := hb _ hR
    refine Eventually.of_forall fun z => ?_
    rw [kernel_norm]
    exact pointwise_bound α hα1 hα2 _ ((contDiff_cutField hA _).of_le (nat_le_top 3)) B hB
      e0 e1 e2 e3 x z
  · refine Eventually.of_forall fun z => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [remainder_eventually A x z] with n hn
    rw [hn]

end Breakdown.SteadyCert.PowerSymbolRapid.Internal

namespace Breakdown.SteadyCert.PowerSymbolRapid.Internal

theorem power_continuous (α : ℝ) (hα1 : 1 < α) (hα2 : α < 3 / 2) (f : Space → Space)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Continuous (fractionalPowerAt α f) :=
  FracInternal.NiceField.continuous_fracPower α hα1 hα2 (hc.toSchwartzMap hf)

theorem domTotal_nonneg (α : ℝ) : 0 ≤ domTotal α :=
  add_nonneg (integral_nonneg fun z => edgeWeight_nonneg α z)
    (integral_nonneg fun z => rpow_nonneg (by positivity) _)

theorem product_integrable (α : ℝ) (hα1 : 1 < α) (v : Space → Space) (hvm : AEStronglyMeasurable v volume)
    (hv : MemLp v 6 volume) (K : ℝ) (hK : 0 ≤ K) :
    Integrable (fun x => ‖v x‖ * (K * (1 + ‖x‖) ^ (-(3 + 2 * α)))) := by
  have hpq : (6 : ℝ).HolderConjugate (6 / 5) := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hv6 : Integrable (fun x => ‖v x‖ ^ (6 : ℝ)) := by
    have := hv.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  have hg : Integrable (fun x : Space => K ^ (6 / 5 : ℝ) * (1 + ‖x‖) ^ (-((3 + 2 * α) * (6 / 5)))) :=
    (integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; push_cast; nlinarith)).const_mul _
  refine Integrable.mono' ((hv6.div_const 6).add (hg.div_const (6 / 5))) ?_ ?_
  · exact hvm.norm.mul (Continuous.aestronglyMeasurable (continuous_const.mul
      ((continuous_const.add continuous_norm).rpow_const fun x => Or.inl (by positivity : (0 : ℝ) < 1 + ‖x‖).ne')))
  · refine Eventually.of_forall fun x => ?_
    have hw : 0 ≤ (1 + ‖x‖) ^ (-(3 + 2 * α)) := rpow_nonneg (by positivity) _
    have hb : 0 ≤ K * (1 + ‖x‖) ^ (-(3 + 2 * α)) := mul_nonneg hK hw
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hb)]
    have hy := young_inequality_of_nonneg (norm_nonneg (v x)) hb hpq
    have e : (K * (1 + ‖x‖) ^ (-(3 + 2 * α))) ^ (6 / 5 : ℝ) =
        K ^ (6 / 5 : ℝ) * (1 + ‖x‖) ^ (-((3 + 2 * α) * (6 / 5))) := by
      rw [mul_rpow hK hw, ← rpow_mul (by positivity)]
      ring_nf
    rw [e] at hy
    exact hy

end Breakdown.SteadyCert.PowerSymbolRapid.Internal

namespace Breakdown.SteadyCert

open PowerSymbolRapid.Internal

theorem rapidWeakPower : RapidWeakPowerStatement := by
  intro α hα1 hα2 v P hvm hv6 hW φ
  obtain ⟨hP2, hP⟩ := hW
  have hφ : ContDiff ℝ ∞ (φ : Space → Space) := φ.smooth ⊤
  have hR : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have heq : ∀ n : ℕ, ∫ y, inner ℝ (P y) (cutField φ ((n : ℝ) + 1) y) =
      ∫ y, inner ℝ (v y) (fractionalPowerAt α (cutField φ ((n : ℝ) + 1)) y) :=
    fun n => hP _ ⟨contDiff_cutField hφ _, hasCompactSupport_cutField _ (hR n).ne'⟩
  have hL : Tendsto (fun n : ℕ => ∫ y, inner ℝ (P y) (cutField φ ((n : ℝ) + 1) y)) atTop
      (𝓝 (∫ y, inner ℝ (P y) (φ y))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖P y‖ * ‖φ y‖) (fun n => ?_)
      (hP2.norm.integrable_mul (φ.memLp 2).norm) (fun n => ?_) ?_
    · exact hP2.1.inner (contDiff_cutField hφ _).continuous.aestronglyMeasurable
    · refine Eventually.of_forall fun y => ?_
      refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      show ‖stdBump (((n : ℝ) + 1)⁻¹ • y) • φ y‖ ≤ ‖φ y‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg stdBump.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) stdBump.le_one
    · refine Eventually.of_forall fun y => tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_gt ‖y‖
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hy : y ∈ Metric.ball (0 : Space) ((n : ℝ) + 1) := by
        rw [mem_ball_zero_iff]; linarith
      rw [sub_eq_zero.mp (cutField_sub_zero_on φ (hR n) y hy)]
  obtain ⟨B, hB, hb⟩ := cut_hyps φ
  have hK0 : 0 ≤ |(fractionalNormalizer α)⁻¹| * ((2 ^ (10 : ℝ) + 3 + 2 ^ (3 + 2 * α)) * B) *
      domTotal α := by
    have := domTotal_nonneg α
    positivity
  have hRt : Tendsto (fun n : ℕ => ∫ y, inner ℝ (v y) (fractionalPowerAt α (cutField φ ((n : ℝ) + 1)) y))
      atTop (𝓝 (∫ y, inner ℝ (v y) (fractionalPowerAt α φ y))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖v x‖ * (|(fractionalNormalizer α)⁻¹| * ((2 ^ (10 : ℝ) + 3 + 2 ^ (3 + 2 * α)) * B) *
        domTotal α * (1 + ‖x‖) ^ (-(3 + 2 * α)))) (fun n => ?_)
      (product_integrable α hα1 v hvm hv6 _ hK0) (fun n => ?_) ?_
    · exact hvm.inner (power_continuous α hα1 hα2 _ (contDiff_cutField hφ _)
        (hasCompactSupport_cutField _ (hR n).ne')).aestronglyMeasurable
    · have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      obtain ⟨e0, e1, e2, e3⟩ := hb _ h1
      refine Eventually.of_forall fun x =>
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact power_bound α hα1 hα2 _ ((contDiff_cutField hφ _).of_le (nat_le_top 3)) B hB
        e0 e1 e2 e3 x
    · exact Eventually.of_forall fun x => tendsto_const_nhds.inner (power_tendsto α hα1 hα2 φ x)
  rw [show (fun n : ℕ => ∫ y, inner ℝ (P y) (cutField φ ((n : ℝ) + 1) y)) =
      (fun n : ℕ => ∫ y, inner ℝ (v y) (fractionalPowerAt α (cutField φ ((n : ℝ) + 1)) y)) from
      funext heq] at hL
  exact tendsto_nhds_unique hL hRt

end Breakdown.SteadyCert
