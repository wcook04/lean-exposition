import Breakdown.FracCert.HeldStateLimitBParts
import Breakdown.Frac.SpaceDecay

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace WeakPowerLimitInternal

theorem weighted_power_memLp {α : ℝ} (h1 : 1 < α) (h2 : α < 3 / 2) {φ : Space → Space}
    (hφ : IsTestVectorField φ) :
    MemLp (fun y => ‖y‖ • fractionalPowerAt α φ y) 2 volume := by
  obtain ⟨hc, C, hC⟩ := fracCompactDecay α h1 h2 φ hφ.1 hφ.2
  have hr : ((Module.finrank ℝ Space : ℕ) : ℝ) < (2 + 2 * α) * 2 := by
    rw [finrank_euclideanSpace_fin]; push_cast; nlinarith
  have hint := integrable_one_add_norm (E := Space) (μ := volume) hr
  have hm : AEStronglyMeasurable (fun x : Space => |C| * (1 + ‖x‖) ^ (-(2 + 2 * α))) volume :=
    (continuous_const.mul (Continuous.rpow_const (continuous_const.add continuous_norm)
      fun x => Or.inl (by show (1 : ℝ) + ‖x‖ ≠ 0; positivity))).aestronglyMeasurable
  have hdom : MemLp (fun x : Space => |C| * (1 + ‖x‖) ^ (-(2 + 2 * α))) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine (hint.const_mul (|C| ^ 2)).congr (ae_of_all _ fun x => ?_)
    have hx : (0 : ℝ) < 1 + ‖x‖ := by positivity
    show |C| ^ 2 * (1 + ‖x‖) ^ (-((2 + 2 * α) * 2)) = ‖|C| * (1 + ‖x‖) ^ (-(2 + 2 * α))‖ ^ 2
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.rpow_pos_of_pos hx _), mul_pow,
      ← Real.rpow_natCast ((1 + ‖x‖) ^ (-(2 + 2 * α))) 2, ← Real.rpow_mul hx.le]
    congr 2
    push_cast
    ring
  refine hdom.of_le (continuous_norm.smul hc).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hx : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hb : ‖fractionalPowerAt α φ x‖ ≤ |C| * (1 + ‖x‖) ^ (-(3 + 2 * α)) :=
    (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx.le _))
  have hsplit : (1 + ‖x‖) ^ (-(2 + 2 * α)) = (1 + ‖x‖) * (1 + ‖x‖) ^ (-(3 + 2 * α)) := by
    rw [show -(2 + 2 * α) = 1 + -(3 + 2 * α) by ring, Real.rpow_add hx, Real.rpow_one]
  rw [norm_smul, norm_norm, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hx.le _)), hsplit]
  have hp : 0 ≤ (1 + ‖x‖) ^ (-(3 + 2 * α)) := Real.rpow_nonneg hx.le _
  have hn : ‖x‖ ≤ 1 + ‖x‖ := by linarith
  calc ‖x‖ * ‖fractionalPowerAt α φ x‖ ≤ (1 + ‖x‖) * (|C| * (1 + ‖x‖) ^ (-(3 + 2 * α))) :=
        mul_le_mul hn hb (norm_nonneg _) hx.le
    _ = |C| * ((1 + ‖x‖) * (1 + ‖x‖) ^ (-(3 + 2 * α))) := by ring

theorem ae_nonzero : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
  exact measure_singleton (μ := (volume : Measure Space)) (0 : Space)

end WeakPowerLimitInternal

open WeakPowerLimitInternal in
theorem weakPowerLimit_holds : WeakPowerLimitStatement := by
  intro α h1 h2 u P w₀ P₀ hP _hu _hw₀ hP₀ hlimw hlimP
  refine ⟨hP₀, fun φ hφ => ?_⟩
  have h32 : α < 3 / 2 := by linarith
  have hW := weighted_power_memLp h1 h32 hφ
  have hφ2 : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  have en : ∀ n, ∫ y, inner ℝ (P n y) (φ y) =
      ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (‖y‖ • fractionalPowerAt α φ y) := by
    intro n
    rw [(hP n).2 φ hφ]
    refine integral_congr_ae ?_
    filter_upwards [ae_nonzero] with y hy
    have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    rw [real_inner_smul_left, real_inner_smul_right, inv_mul_cancel_left₀ hy']
  have e0 : ∫ y, inner ℝ (‖y‖ • w₀ y) (fractionalPowerAt α φ y) =
      ∫ y, inner ℝ (w₀ y) (‖y‖ • fractionalPowerAt α φ y) := by
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [real_inner_smul_left, real_inner_smul_right]
  rw [e0]
  exact tendsto_nhds_unique (hlimP φ hφ2) ((hlimw _ hW).congr fun n => (en n).symm)

end SteadyCert

end Breakdown
