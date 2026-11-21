import Breakdown.CertCell.BridgeTraceStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open CellCert.CellFormula

theorem potentialNegation : PotentialNegationHolds := by
  unfold PotentialNegationHolds IsPotentialOf
  intro Q q hq
  obtain ⟨hmeas, hsq, hweak⟩ := hq
  refine ⟨hmeas.neg, ?_, ?_⟩
  · have hfun : (fun y => (-q y) ^ 2) = (fun y => q y ^ 2) := by
      funext y
      exact neg_sq (q y)
    rw [hfun]
    exact hsq
  · intro φ hφ j
    have h := hweak φ hφ j
    simp only [mul_neg, inner_neg_left, integral_neg, neg_neg]
    rw [h, neg_neg]

end SideTrace

end CertCell

end Breakdown
