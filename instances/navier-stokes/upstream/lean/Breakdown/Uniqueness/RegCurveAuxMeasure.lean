import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def weightedVolume (k : ℕ) : Measure Space :=
  volume.withDensity (fun ξ => ENNReal.ofReal ((1 + ‖ξ‖) ^ k))

theorem lintegral_weightedVolume (k : ℕ) (g : Space → ℝ≥0∞) :
    ∫⁻ ξ, g ξ ∂weightedVolume k = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * g ξ := by
  unfold weightedVolume
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rfl

theorem memLp_weightedVolume_of_hsNormSq {k : ℕ} {f : Space → CSpace}
    (hm : AEStronglyMeasurable f volume) (hs : hsNormSq (k + 2) f < ⊤) :
    MemLp f 1 (weightedVolume k) := by
  obtain ⟨C, hC⟩ := weightedFreqL1_le k
  refine ⟨hm.mono_ac (withDensity_absolutelyContinuous _ _), ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm, lintegral_weightedVolume]
  exact lt_of_le_of_lt (hC f)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hs.ne))

end Breakdown.SmoothFlow
