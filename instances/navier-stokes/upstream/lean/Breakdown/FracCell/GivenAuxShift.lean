import Breakdown.FracCell.GivenAuxShiftParts
import Breakdown.FracCell.GivenProfileBounds
import Breakdown.FracCell.GivenAuxAdjoint

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

theorem shiftWeighted_of_given {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (A : AuxData k)
    (hA : IsAuxData D.chart A) (j : Fin k) (p : Fin k → ℝ) (i : Fin k) :
    Integrable (fun y => ‖D.tangentField i y‖ ^ 2 * ‖A.adjointField D.chart j p y‖ ^ 2) ∧
      Integrable (fun y => ‖y‖ ^ 2 * ‖fderiv ℝ (D.tangentField i) y‖ ^ 2 * ‖A.adjointField D.chart j p y‖ ^ 2) := by
  obtain ⟨hU, -, C, hb⟩ := shift_regular_of D hD i
  exact FracInternal.weighted_pair_integrable (D.tangentField i) hU C hb _
    (adjointRegular_of_given D.chart hD.chart A hA j p).1

end GivenFields

end CellCert

end Breakdown
