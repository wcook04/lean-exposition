import Breakdown.CellReduction.AdjointRemainderAzimuthalParts

open scoped ENNReal ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

open CellCert.Reduction FracInternal.FrameInverseSquareParts

theorem modeWeight_eq_abs (k : ℤ) : modeWeight k = ((|k| : ℤ) : ℝ) + 1 / 2 := by
  simp [modeWeight, Int.cast_abs]

theorem smoothModeInverseSquare : SmoothModeInverseSquareHolds := by
  intro u hu hs k
  obtain ⟨⟨hac, has⟩, -, hfr⟩ := frameModeCalculus' u hu hs k
  set a : ℝ × ℝ → ℂ := fun p => angularMode (horizontalPart u) k p.1 p.2 with ha
  have h1 := halfPlaneBound' a k _ hac has (Or.inl rfl)
  have hS : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  calc ENNReal.ofReal (modeWeight k ^ 2) * modeInverseSquare (horizontalPart u) k
      = ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), ENNReal.ofReal (2 * Real.pi * q.1 *
          ((((|k| : ℤ) : ℝ) + 1 / 2) ^ 2 * ‖a q‖ ^ 2) / (q.1 ^ 2 + q.2 ^ 2)) := by
        unfold modeInverseSquare
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun q => ?_
        rw [← ENNReal.ofReal_mul (sq_nonneg _), modeWeight_eq_abs]
        congr 1
        simp only [ha]
        ring
    _ ≤ _ := h1
    _ ≤ modeGradientSide (fun y => fderiv ℝ u y) k := by
        unfold modeGradientSide
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hS] with q hq
        have hρ : 0 < q.1 := hq.1
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hfr q.1 q.2 hρ]
        refine mul_le_mul_of_nonneg_left ?_ (mul_pos (mul_pos two_pos Real.pi_pos) hρ).le
        have hv : 0 ≤ ‖fderiv ℝ (fun p : ℝ × ℝ => angularMode (verticalPart u) k p.1 p.2) (q.1, q.2) (1, 0)‖ ^ 2 +
            ‖fderiv ℝ (fun p : ℝ × ℝ => angularMode (verticalPart u) k p.1 p.2) (q.1, q.2) (0, 1)‖ ^ 2 +
            (k : ℝ) ^ 2 * ‖angularMode (verticalPart u) k q.1 q.2‖ ^ 2 / q.1 ^ 2 := by positivity
        simp only [Prod.mk.eta] at hv ⊢
        linarith

end AzimuthalParts

end AdjointDefect

end Breakdown
