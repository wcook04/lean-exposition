import Breakdown.CertCell.BridgeStatements
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveRotation

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.ShiftRotate

open Coercive Coercive.Internal.ModeRotation

theorem expFactor_sub_time (ι : ℤ × ℤ) (τ s φ : ℝ) :
    expFactor ι (τ - s) φ = Complex.exp (((2 * Real.pi * ι.1 * s : ℝ) : ℂ) * Complex.I) * expFactor ι τ φ := by
  unfold expFactor
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expFactor_add_one (ι : ℤ × ℤ) (τ φ : ℝ) : expFactor ι (τ + 1) φ = expFactor ι τ φ := by
  unfold expFactor
  have h : -(((2 * Real.pi * ι.1 * (τ + 1) + ι.2 * φ : ℝ) : ℂ) * Complex.I) =
      -(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I) +
        ((-ι.1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem modeVel_time_shift (v : ℝ → Space → Space) (hv : IsTimePeriodic v) (ι : ℤ × ℤ) (σ s : ℝ)
    (y : Space) :
    modeVel ι v (σ + s) y = fun i =>
      Complex.exp (((2 * Real.pi * ι.1 * s : ℝ) : ℂ) * Complex.I) * modeVel ι v σ y i := by
  funext i
  let h : ℝ → ℂ := fun u => ∫ φ in (0 : ℝ)..(2 * Real.pi),
    expFactor ι (u - s) φ * ((axialRot (-φ) (v (σ + u) (axialRot φ y)) i : ℝ) : ℂ)
  have hper : Function.Periodic h 1 := by
    intro u
    refine intervalIntegral.integral_congr fun φ _ => ?_
    rw [show u + 1 - s = (u - s) + 1 by ring, expFactor_add_one, show σ + (u + 1) = (σ + u) + 1 by ring,
      hv]
  have hh : ∀ u, h u = Complex.exp (((2 * Real.pi * ι.1 * s : ℝ) : ℂ) * Complex.I) *
      ∫ φ in (0 : ℝ)..(2 * Real.pi),
        expFactor ι u φ * ((axialRot (-φ) (v (σ + u) (axialRot φ y)) i : ℝ) : ℂ) := by
    intro u
    simp only [h]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    rw [expFactor_sub_time]
    ring
  calc modeVel ι v (σ + s) y i
      = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, h (τ + s) := by
        unfold modeVel
        rw [modeAverage_eq]
        congr 1
        refine intervalIntegral.integral_congr fun τ _ => ?_
        refine intervalIntegral.integral_congr fun φ _ => ?_
        rw [add_sub_cancel_right, show σ + (τ + s) = σ + s + τ by ring]
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ u in (0 : ℝ)..1, h u := by
        rw [intervalIntegral.integral_comp_add_right h s, zero_add, add_comm (1 : ℝ) s,
          hper.intervalIntegral_add_eq s 0, zero_add]
    _ = _ := by
        simp_rw [hh]
        rw [intervalIntegral.integral_const_mul]
        unfold modeVel
        rw [modeAverage_eq]
        ring

theorem integrable_box_of_integrableOn {v : ℝ → Space → Space} {σ : ℝ} {y : Space}
    (hi : IntegrableOn (fun p : ℝ × ℝ => v (σ + p.1) (axialRot p.2 y))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) :
    Integrable (fun p : ℝ × ℝ => v ((σ, y).1 + p.1) (axialRot p.2 (σ, y).2)) boxMeasure := by
  have e : boxMeasure = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [e]
  exact hi.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

end Internal.ShiftRotate

open Coercive Coercive.Internal.ModeRotation Internal.ShiftRotate in
theorem modeShiftRotate : ModeShiftRotateHolds := by
  intro v hv ξ σ s φ y hi
  have hrot := modeVel_rotation_of axialRotationHolds_proof ξ φ (z := (σ, y))
    (integrable_box_of_integrableOn hi)
  funext i
  rw [modeVel_time_shift v hv ξ σ s (axialRot φ y)]
  simp only at hrot
  rw [hrot]
  unfold rotC
  dsimp only
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Bridge

end CertCell

end Breakdown
