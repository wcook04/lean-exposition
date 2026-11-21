import Breakdown.Cert.CoerciveSmoothEpsSetting
import Breakdown.Cert.CoerciveSmoothEpsSumSecondPartialsModes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

theorem epsSumSecondPartials_lower (hSsp : WeightedSumSecondPartialsPairingHolds) {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ}
    {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}
    (hS : EpsSetting m P b w W w₀ epsSup epsGradSup ratio v) (ι : ℤ × ℤ) (σ : ℝ) :
    -(∫ y, epsGradTerm m v ι σ y) ≤ ∫ y, epsIntegrand m v (negSumSecondPartialsOfField v) ι σ y := by
  obtain ⟨K, hK⟩ := hS.admissible.epsW_increment (m.classOf ι)
  exact Internal.SmoothEpsSumSecondPartials.mode_lower hSsp hS.smooth hK
    (fun y => hS.admissible.epsW_le (m.classOf ι) y) (fun y => hS.admissible.epsW_grad_le (m.classOf ι) y) ι σ

end SmoothEpsInternal

end Coercive

end Breakdown
