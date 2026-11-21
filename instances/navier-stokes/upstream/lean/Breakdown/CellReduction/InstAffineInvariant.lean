import Breakdown.CellReduction.InstanceStatements
import Breakdown.CertCell.CellLayerClosed
import Breakdown.CertCell.InstanceLinkActuators

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal.AffineInvariant

open CertCell.Instance.Internal.ActuatorSymmetry

theorem rotate_iterate_everywhere (f : ℝ → Space → Space) (θ : ℝ)
    (hrot : ∀ σ y, f (σ + 1 / 2) (axialRot θ y) = axialRot θ (f σ y)) (a : ℕ) :
    ∀ σ y, f (σ + (a : ℝ) / 2) (axialRot ((a : ℝ) * θ) y) = axialRot ((a : ℝ) * θ) (f σ y) := by
  induction a with
  | zero =>
    intro σ y
    simp [axialRot_zero_angle]
  | succ n ih =>
    intro σ y
    have e1 : σ + ((n + 1 : ℕ) : ℝ) / 2 = σ + 1 / 2 + (n : ℝ) / 2 := by
      push_cast
      ring
    have e2 : ∀ v, axialRot (((n + 1 : ℕ) : ℝ) * θ) v = axialRot ((n : ℝ) * θ) (axialRot θ v) := by
      intro v
      rw [axialRot_axialRot]
      congr 1
      push_cast
      ring
    rw [e1, e2, e2, ih (σ + 1 / 2) (axialRot θ y), hrot]

theorem turn_flip_shift (f : ℝ → Space → Space) (θ : ℝ) (hper : IsTimePeriodic f)
    (hflip : ∀ σ y, f σ (flipPoint y) = flipPoint (f σ y))
    (hrot : ∀ σ y, f (σ + 1 / 2) (axialRot θ y) = axialRot θ (f σ y)) (a : ℕ) (b : Bool) (j : ℤ) (σ : ℝ)
    (y : Space) :
    f (σ + ((a : ℝ) / 2 + (j : ℝ))) (axialRot ((a : ℝ) * θ) (if b then flipPoint y else y)) =
      axialRot ((a : ℝ) * θ) (if b then flipPoint (f σ y) else f σ y) := by
  have hR := rotate_iterate_everywhere f θ hrot a
  have e : σ + ((a : ℝ) / 2 + (j : ℝ)) = (σ + (a : ℝ) / 2) + (j : ℝ) := by ring
  rw [e, periodic_int_shift hper j]
  cases b
  · rw [if_neg (by decide), if_neg (by decide)]
    exact hR σ y
  · rw [if_pos rfl, if_pos rfl, hR, hflip]

end Internal.AffineInvariant

open Internal.AffineInvariant in
theorem affineFieldInvariant_holds : AffineFieldInvariantHolds := by
  intro k C nE nM D P g centre gt tangent q hgen haz hP hg hgt hc ht γ hγ σ y
  obtain ⟨a, b, j, hγ1, hγ2⟩ := hgen γ hγ
  have key : ∀ (h : OriginProfile) (T : TimeFieldData), IsOriginProfile h → IsTimeFieldData T →
      shapeInfoField (withOrigin P h) T (σ + γ.2) (γ.1 y) = γ.1 (shapeInfoField (withOrigin P h) T σ y) := by
    intro h T hh hT
    have hP' : IsShapeParams (withOrigin P h) :=
      ⟨hP.chartLength_pos, hP.azimuthOrder_pos, hP.phase, hh⟩
    obtain ⟨hfl, hrot, -⟩ := shapeParts_closed.field_class (withOrigin P h) T hP' hT
    have hper := (shapeParts_closed.field_smooth (withOrigin P h) T hP' hT).2.1
    have e : (withOrigin P h).azimuthOrder = D.azimuthOrder := haz
    rw [e] at hrot
    rw [hγ1 y, hγ1, hγ2]
    exact turn_flip_shift _ _ hper hfl hrot a b j σ y
  simp only [affineField, map_add, map_sum, map_smul]
  rw [key g centre hg hc]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key (gt i) (tangent i) (hgt i) (ht i)]

end Instantiation

end CellReduction

end Breakdown
