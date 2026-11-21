import Breakdown.FracCell.ReductionLossDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

theorem strainLoss_of_opNorm {k N : ℕ} (c : FracCellData k N) (L : ℝ) (hL : ∀ y, ‖c.strainError y‖ ≤ L)
    (hle : L ≤ c.strainLoss) :
    ∀ y (u : Space), inner ℝ u (c.strainError y u) ≤ c.strainLoss * ‖u‖ ^ 2 := by
  intro y u
  have h1 : inner ℝ u (c.strainError y u) ≤ ‖u‖ * ‖c.strainError y u‖ := real_inner_le_norm _ _
  have h2 : ‖c.strainError y u‖ ≤ ‖c.strainError y‖ * ‖u‖ := (c.strainError y).le_opNorm u
  have h3 : ‖c.strainError y‖ * ‖u‖ ≤ c.strainLoss * ‖u‖ :=
    mul_le_mul_of_nonneg_right ((hL y).trans hle) (norm_nonneg u)
  calc inner ℝ u (c.strainError y u) ≤ ‖u‖ * ‖c.strainError y u‖ := h1
    _ ≤ ‖u‖ * (c.strainLoss * ‖u‖) := mul_le_mul_of_nonneg_left (h2.trans h3) (norm_nonneg u)
    _ = c.strainLoss * ‖u‖ ^ 2 := by ring

end Reduction

end CellCert

end Breakdown
