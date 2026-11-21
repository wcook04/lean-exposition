import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FracCert.InverseSquare

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

theorem inverseSquareConst_two (m : ℕ) : InverseSquareConstStatement m 2 := by
  refine ⟨by norm_num, ?_⟩
  intro v G K hv
  obtain ⟨hint, hle⟩ := inverseSquareBound v G hv.measurable_velocity hv.velocity_six hv.gradient_two
    hv.weak_gradient
  refine ⟨hint, ?_⟩
  calc (∫ y, ‖v y‖ ^ 2 / ‖y‖ ^ 2) ≤ 4 * ∫ y, entrySq (G y) := hle
    _ = (2 : ℝ) ^ 2 * ∫ y, entrySq (G y) := by norm_num

end Reduction

end CellCert

end Breakdown
