import Breakdown.Uniqueness.Blowup
import Breakdown.Uniqueness.Scaling

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

theorem breakdownOnSpace_of_exports (hT : TransferHolds) (hP : ProfileOrbitHolds)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Realization X) (vel : X →L[ℝ] Lp (α := Space) Space 6) (hF : FieldReading Rlz vel)
    (hR : MildRegular Rlz vel) : PeriodicSimilarityProfileExists → BreakdownOnSpace := fun hW =>
  breakdownOnSpace_of_unit_viscosity (noBoundedSmoothSolution_of_exports hT hP Rlz vel hF hR hW)

end Breakdown
