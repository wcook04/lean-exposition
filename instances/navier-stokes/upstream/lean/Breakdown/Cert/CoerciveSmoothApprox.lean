import Breakdown.Cert.CoerciveSmoothApproxClass
import Breakdown.Cert.CoerciveSmoothApproxLimits

open scoped ContDiff ENNReal Topology Convolution
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

open Internal.SmoothApprox in
theorem smoothApproximationHolds_proof : SmoothApproximationHolds := by
  intro Γ P v G H g hv
  exact ⟨fun n => mollify n v, fun n => mollify_isSmoothPerturbation hv n,
    mollify_gradient_tendsto hv, mollify_secondDeriv_tendsto hv, mollify_weighted_tendsto hv,
    mollify_transport_tendsto hv⟩

end Coercive

end Breakdown
