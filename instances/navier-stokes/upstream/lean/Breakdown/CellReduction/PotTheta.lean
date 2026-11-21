import Breakdown.CellReduction.PotThetaSmooth
import Breakdown.CellReduction.PotPhiDecay

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect

theorem thetaPotentialRegular_of (hoff : ScalarSmoothAwayFromOrigin) (hnear : ScalarSmoothNearOrigin)
    (hdec : ScalarDecayOrder 2) : ThetaPotentialRegular := by
  intro P F hP hF
  have hpick := isPotentialPick_theta hF
  obtain ⟨C, hb, ha⟩ := potentialDecay_of_pick hdec hP hpick
    (fun κ hκ c σ => (component_smooth_of hoff hnear hP hpick hκ c σ).1.differentiable one_ne_zero)
    (fun κ hκ c σ => ae_differentiableAt_of_slopeOn (component_smooth_of hoff hnear hP hpick hκ c σ).2)
  exact ⟨C, vectorPotential_contDiff_of hoff hnear hP hpick,
    fun σ j => vectorPotential_weakSecond_of hoff hnear hP hpick σ j, hb, ha⟩

end PotentialShape

end Breakdown
