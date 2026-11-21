import Breakdown.Uniqueness.RegPhysAuxDeriv
import Breakdown.Uniqueness.RegPhysAuxProductPart2

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem memLp_advectionSymbol {f : Space → CSpace} (hf : ∀ k, MemLp f 1 (weightL1Measure k)) (k : ℕ) :
    MemLp (advectionSymbol f) 1 (weightL1Measure k) :=
  Internal.ConvProduct.memLp_advectionSymbol_aux hf k

theorem advectionAt_physField {f : Space → CSpace} (hf : ∀ k, MemLp f 1 (weightL1Measure k))
    (hsol : IsSolenoidalSymbol f) (x : Space) :
    advectionAt (physField f) x = physField (advectionSymbol f) x := by
  unfold advectionAt
  rw [fderiv_physField_apply (hf 1)]
  exact Internal.ConvProduct.physField_freqInner_eq hf hsol x

end Breakdown.SmoothFlow
