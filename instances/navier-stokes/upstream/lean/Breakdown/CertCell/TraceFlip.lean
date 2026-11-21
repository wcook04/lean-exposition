import Breakdown.CertCell.BridgeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

theorem traceFlip : TraceFlipHolds := by
  intro f fz h s
  unfold upperTrace lowerTrace
  have key : (fun z : ℝ => -(s * fz (-z)) * ((1 - z / h : ℝ) : ℂ) - s * f (-z) / (h : ℂ))
      = fun z : ℝ => -(s * (fz (-z) * ((1 + (-z) / h : ℝ) : ℂ) + f (-z) / (h : ℂ))) := by
    funext z
    push_cast
    ring
  rw [key, intervalIntegral.integral_neg, neg_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_neg (fun w : ℝ => fz w * ((1 + w / h : ℝ) : ℂ) + f w / (h : ℂ)),
    neg_zero]

end Bridge

end CertCell

end Breakdown
