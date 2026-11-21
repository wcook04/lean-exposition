import Breakdown.FracCell.ReductionLossDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

theorem curlGradLoss_of_kernel (hK : KernelPotentialStatement) {k N : ℕ} (c : FracCellData k N) (Λ : ℝ)
    (hV : KernelBound (fun y => ‖c.curlGradError y‖ ^ 2) Λ) (hbound : Real.sqrt Λ ≤ c.curlGradLoss) :
    ∀ v G H, IsSecondOrderField c.order v G H →
      Real.sqrt (∫ y, ‖c.curlGradError y‖ ^ 2 * ‖v y‖ ^ 2) ≤ c.curlGradLoss * Real.sqrt (∫ y, entrySq (G y)) := by
  intro v G H hv
  have hpair : IsGradientPair v G :=
    ⟨hv.measurable_velocity, hv.velocity_six, hv.measurable_gradient, hv.gradient_two, hv.weak_gradient⟩
  obtain ⟨_, hle⟩ := hK _ Λ hV v G hpair
  have hE : 0 ≤ ∫ y, entrySq (G y) :=
    integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  calc Real.sqrt (∫ y, ‖c.curlGradError y‖ ^ 2 * ‖v y‖ ^ 2)
      ≤ Real.sqrt (Λ * ∫ y, entrySq (G y)) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt Λ * Real.sqrt (∫ y, entrySq (G y)) := Real.sqrt_mul' _ hE
    _ ≤ c.curlGradLoss * Real.sqrt (∫ y, entrySq (G y)) :=
        mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg _)

end Reduction

end CellCert

end Breakdown
