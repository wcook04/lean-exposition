import Breakdown.CellReduction.PotThetaSmooth
import Breakdown.CellReduction.PotPhiDecay

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect

theorem phiPotentialRegular_of (hoff : ScalarSmoothAwayFromOrigin) (hnear : ScalarSmoothNearOrigin)
    (hdec : ScalarDecayOrder 1) : PhiPotentialRegular := by
  intro P F hP hF
  have hpick := isPotentialPick_phi hF
  obtain ⟨C, hb, hs⟩ := potentialDecay_of_scalarParts hoff hnear hdec hP hpick
  refine ⟨C, vectorPotential_contDiff_of hoff hnear hP hpick,
    fun σ j => vectorPotential_weakSecond_of hoff hnear hP hpick σ j, fun σ y => ?_, fun σ => ?_⟩
  · simpa only [pow_one, Nat.reduceAdd] using hb σ y
  · simpa only [Nat.reduceAdd] using hs σ

end PotentialShape

end Breakdown
