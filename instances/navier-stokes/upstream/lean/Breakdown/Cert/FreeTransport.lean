import Breakdown.Cert.FreeTransportMild

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.FreePerturbation

theorem integral_inner_transportPart {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {f : HH} {g : ℝ → Space → Space} (hg : IsTransportPart f u g)
    (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestVector φ) :
    ∫ z : ℝ × Space, inner ℝ (g z.1 z.2) (φ z.1 z.2) =
      (∫ z : ℝ × Space, inner ℝ (fullField g H z.1 z.2) (φ z.1 z.2))
        - ∫ z : ℝ × Space, matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2) := by
  have hF := isPeriodicField_fullField hr hg
  have hφc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
  have i1 := integrable_inner_of_periodic hF.1 hF.2.1 hF.2.2 hφc hφ.2
  have i2 := integrable_inner_of_periodic (F := fun σ y => secondDerivTrace (H σ y))
    (continuous_secondDerivTrace.comp_aestronglyMeasurable hr.measurable_second)
    (fun σ y => by simp only [hr.periodic_second σ y]) (sumSecondPartials_finite_of_reading hr) hφc hφ.2
  have e0 : (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (φ z.1 z.2)) =
      fun z => inner ℝ (fullField g H z.1 z.2) (φ z.1 z.2)
        + inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2) := by
    funext z
    rw [← inner_add_left]
    simp only [fullField, sub_add_cancel]
  rw [e0, integral_add i1 i2, (integral_matInner_eq hr φ hφ).2, sub_neg_eq_add]

theorem transport_of_reading (hInv : FreeInvHolds) (_hProj : ProjectionHolds) (hB : PropagatorBoundHolds)
    (hG : GradInvHolds) (_hGr : GraphClosedHolds) {P : ℝ} (hP : 0 < P)
    (f : HH) {v : VelField} {G : GradField} {H : SecondField} (hr : IsReadingOf (freeInv P f) v G H)
    {g : ℝ → Space → Space} (hg : IsTransportPart f (freeInv P f) g) (φ : ℝ → Space → Space)
    (hφ : IsSpaceTimeTestVector φ) :
    ∫ z : ℝ × Space, inner ℝ (v z.1 z.2) (-(1 / P) • deriv (fun s => φ s z.2) z.1 - φ z.1 z.2
      - (1 / 2 : ℝ) • fderiv ℝ (φ z.1) z.2 z.2) = ∫ z : ℝ × Space, inner ℝ (g z.1 z.2) (φ z.1 z.2) := by
  have hF := isPeriodicField_fullField hr hg
  have hFs := fullField_slices hr hg
  have key := mild_transport hInv hB hG hP f hr hF hFs φ hφ
  rw [integral_inner_transportPart hr hg φ hφ]
  exact key

end Internal.FreePerturbation

end Breakdown.Cert
