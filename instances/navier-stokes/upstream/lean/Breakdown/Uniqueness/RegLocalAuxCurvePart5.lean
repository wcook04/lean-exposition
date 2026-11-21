import Breakdown.Uniqueness.RegLocalAuxCurvePart4

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem rpow_two_eq' (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

private theorem eLpNorm_two_eq {f : Space → ℂ} :
    eLpNorm f 2 volume = (∫⁻ η, ‖f η‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp

private theorem memLp_two_of {q : Space → ℂ} (hq : AEStronglyMeasurable q volume)
    (hq2 : ∫⁻ η, ‖q η‖ₑ ^ 2 ≠ ⊤) : MemLp q 2 volume := by
  refine ⟨hq, ?_⟩
  rw [eLpNorm_two_eq]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hq2

private theorem lintegral_sq_ne_top_of_memLp {g : Space → ℂ} (hg : MemLp g 2 volume) :
    ∫⁻ η, ‖g η‖ₑ ^ 2 ≠ ⊤ := by
  have h := hg.2
  rw [eLpNorm_two_eq] at h
  intro htop
  rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at h
  exact lt_irrefl _ h

private theorem convC_eq_convolution (p g : Space → ℂ) :
    convC p g = convolution p g (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext ξ
  rfl

theorem continuous_convC {p q : Space → ℂ} (hp : AEStronglyMeasurable p volume)
    (hq : AEStronglyMeasurable q volume) (hp2 : ∫⁻ η, ‖p η‖ₑ ^ 2 ≠ ⊤) (hq2 : ∫⁻ η, ‖q η‖ₑ ^ 2 ≠ ⊤) :
    Continuous (convC p q) := by
  have hpL := memLp_two_of hp hp2
  have hqL := memLp_two_of hq hq2
  have hloc : LocallyIntegrable p volume := hpL.locallyIntegrable (by norm_num)
  set P : ℝ≥0∞ := (∫⁻ η, ‖p η‖ₑ ^ 2) ^ (1 / 2 : ℝ) with hP
  have hPtop : P ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hp2).ne
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  have hpos : 0 < ε / (2 * (P.toReal + 1)) := by positivity
  obtain ⟨g, hgc, hgq, hgcont, hgL⟩ :=
    hqL.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) (ENNReal.ofReal_pos.2 hpos).ne'
  refine ⟨convC p g, ?_, fun y => hεu ?_⟩
  · rw [convC_eq_convolution]
    exact hgc.continuous_convolution_right (L := ContinuousLinearMap.mul ℂ ℂ) hloc hgcont
  · rw [← edist_lt_ofReal, edist_eq_enorm_sub,
      convC_sub_right hp hq hgcont.aestronglyMeasurable hp2 hq2 (lintegral_sq_ne_top_of_memLp hgL) y]
    refine lt_of_le_of_lt (enorm_convC_le hp (hq.sub hgcont.aestronglyMeasurable) y) ?_
    have e : (∫⁻ η, ‖(q - g) η‖ₑ ^ 2) ^ (1 / 2 : ℝ) = eLpNorm (q - g) 2 volume :=
      eLpNorm_two_eq.symm
    rw [e]
    calc P * eLpNorm (q - g) 2 volume ≤ ENNReal.ofReal P.toReal * ENNReal.ofReal (ε / (2 * (P.toReal + 1))) := by
          rw [ENNReal.ofReal_toReal hPtop]
          gcongr
      _ = ENNReal.ofReal (P.toReal * (ε / (2 * (P.toReal + 1)))) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      _ < ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_lt_ofReal_iff hε]
          have hP0 : 0 ≤ P.toReal := ENNReal.toReal_nonneg
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith

end Breakdown.SmoothFlow
