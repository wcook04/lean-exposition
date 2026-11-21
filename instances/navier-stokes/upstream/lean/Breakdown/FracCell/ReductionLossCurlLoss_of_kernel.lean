import Breakdown.FracCell.ReductionLossDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

theorem curlLoss_of_kernel (hK : KernelPotentialStatement) {k N : ℕ} (c : FracCellData k N) (Λ : ℝ)
    (hV : KernelBound (fun y => c.cellWeight y * ‖c.curlError y‖ ^ 2) Λ) (hbound : Real.sqrt Λ ≤ c.curlLoss) :
    ∀ v G H, IsSecondOrderField c.order v G H →
      Real.sqrt (∫ y, c.cellWeight y * ‖c.curlError y‖ ^ 2 * ‖v y‖ ^ 2) ≤ c.curlLoss * Real.sqrt (∫ y, entrySq (G y)) := by
  intro v G H hs
  have hp : IsGradientPair v G :=
    ⟨hs.measurable_velocity, hs.velocity_six, hs.measurable_gradient, hs.gradient_two, hs.weak_gradient⟩
  have hle := (hK _ Λ hV v G hp).2
  have hE : 0 ≤ ∫ y, entrySq (G y) :=
    integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  calc Real.sqrt (∫ y, c.cellWeight y * ‖c.curlError y‖ ^ 2 * ‖v y‖ ^ 2)
      ≤ Real.sqrt (Λ * ∫ y, entrySq (G y)) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt Λ * Real.sqrt (∫ y, entrySq (G y)) := Real.sqrt_mul' _ hE
    _ ≤ c.curlLoss * Real.sqrt (∫ y, entrySq (G y)) :=
      mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg _)

end Reduction

end CellCert

end Breakdown
