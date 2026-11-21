import Breakdown.Uniqueness.RegPhysAuxProduct

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem memLp_weight_of_hsNormSq {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hf : ∀ m, hsNormSq m f < ⊤) (k : ℕ) : MemLp f 1 (weightL1Measure k) := by
  obtain ⟨C, hC⟩ := weightedFreqL1_le k
  rw [memLp_weight_iff hm]
  refine lt_of_le_of_lt (hC f) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hf (k + 2)).ne

theorem advectionAt_physField_eq {f : Space → CSpace} (hm : AEStronglyMeasurable f volume)
    (hs : IsSolenoidalSymbol f) (hf : ∀ m, hsNormSq m f < ⊤) :
    (fun x => advectionAt (physField f) x) = physField (advectionSymbol f) :=
  funext fun x => advectionAt_physField (memLp_weight_of_hsNormSq hm hf) hs x


end Breakdown.SmoothFlow
