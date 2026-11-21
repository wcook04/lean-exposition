import Breakdown.CellReduction.InstanceStatements
import Breakdown.CertCell.ShapeTypeTwoDecayPhase

open scoped ContDiff Topology
open Filter

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

variable {P : ShapeParams} {moving : ℝ → ℝ} {a r : ℝ}

theorem moved_radialPhase_eventuallyEq (hm : ∀ s, s ≤ r ^ 2 → moving s = 0) {s : ℝ} (hs : s < r ^ 2) :
    (movedParams P moving a).radialPhase =ᶠ[𝓝 s] P.radialPhase := by
  filter_upwards [Iio_mem_nhds hs] with u hu
  simp [movedParams, hm u (le_of_lt hu)]

theorem norm_sq_lt_of_norm_lt {y : Space} (hy : ‖y‖ < r) : ‖y‖ ^ 2 < r ^ 2 := by
  nlinarith [norm_nonneg y]

theorem moved_phaseSlope_eq (hL : 0 < P.chartLength) (hm : ∀ s, s ≤ r ^ 2 → moving s = 0) {y : Space}
    (hy : ‖y‖ < r) :
    phaseSlope (movedParams P moving a) (chartCoord P y) = phaseSlope P (chartCoord P y) := by
  have hc : chartRadius (movedParams P moving a) (chartCoord P y) = ‖y‖ :=
    CertCell.GivenShape.Internal.chartRadius_chartCoord P hL y
  have hc' : chartRadius P (chartCoord P y) = ‖y‖ :=
    CertCell.GivenShape.Internal.chartRadius_chartCoord P hL y
  unfold phaseSlope
  rw [hc, hc', (moved_radialPhase_eventuallyEq (a := a) hm (norm_sq_lt_of_norm_lt hy)).deriv_eq]

theorem moved_reducedComps_eq (κ : FieldKey) (A : KeyAmp) (t x : ℝ)
    (h : phaseSlope (movedParams P moving a) t = phaseSlope P t) :
    reducedComps (movedParams P moving a) κ A t x = reducedComps P κ A t x := by
  simp only [reducedComps, shiftedScale, h]
  rfl

theorem moved_keyPhase_eq (hm : ∀ s, s ≤ r ^ 2 → moving s = 0) (κ : FieldKey) (σ : ℝ) {y : Space}
    (hy : ‖y‖ < r) : keyPhase (movedParams P moving a) κ σ y = keyPhase P κ σ y := by
  simp only [keyPhase, movedParams, hm _ (le_of_lt (norm_sq_lt_of_norm_lt hy)), mul_zero, add_zero]

theorem moved_keyVector_eq (hL : 0 < P.chartLength) (hm : ∀ s, s ≤ r ^ 2 → moving s = 0) (κ : FieldKey)
    (A : KeyAmp) (σ : ℝ) {y : Space} (hy : ‖y‖ < r) :
    keyVector (movedParams P moving a) κ A σ y = keyVector P κ A σ y := by
  have hc : chartCoord (movedParams P moving a) y = chartCoord P y := rfl
  have hr : ∀ x, reducedComps (movedParams P moving a) κ A (chartCoord P y) x =
      reducedComps P κ A (chartCoord P y) x := fun x =>
    moved_reducedComps_eq κ A _ x (moved_phaseSlope_eq hL hm hy)
  funext i
  unfold keyVector
  rw [moved_keyPhase_eq hm κ σ hy, hc, hr]

theorem ball_mem_nhds {y : Space} (hy : ‖y‖ < r) : Metric.ball (0 : Space) r ∈ 𝓝 y :=
  Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy)

theorem moved_keyVector_eventuallyEq (hL : 0 < P.chartLength) (hm : ∀ s, s ≤ r ^ 2 → moving s = 0)
    (κ : FieldKey) (A : KeyAmp) (σ : ℝ) {y : Space} (hy : ‖y‖ < r) :
    keyVector (movedParams P moving a) κ A σ =ᶠ[𝓝 y] keyVector P κ A σ := by
  filter_upwards [ball_mem_nhds hy] with x hx
  exact moved_keyVector_eq hL hm κ A σ (mem_ball_zero_iff.mp hx)

theorem moved_keySecondDeriv_eq (hL : 0 < P.chartLength) (hm : ∀ s, s ≤ r ^ 2 → moving s = 0)
    (κ : FieldKey) (A : KeyAmp) (σ : ℝ) {y : Space} (hy : ‖y‖ < r) :
    keyHess (movedParams P moving a) κ A σ y = keyHess P κ A σ y := by
  unfold keyHess
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [ball_mem_nhds hy] with x hx
  exact (moved_keyVector_eventuallyEq hL hm κ A σ (mem_ball_zero_iff.mp hx)).fderiv_eq

theorem moved_field_eq (hL : 0 < P.chartLength) (hm : ∀ s, s ≤ r ^ 2 → moving s = 0)
    (D : TimeFieldData) (σ : ℝ) {y : Space} (hy : ‖y‖ < r) :
    shapeInfoField (movedParams P moving a) D σ y = shapeInfoField P D σ y := by
  unfold shapeInfoField complexField
  congr 1
  exact Finset.sum_congr rfl fun κ _ => moved_keyVector_eq hL hm κ (D.amp κ) σ hy

theorem moved_field_eventuallyEq (hL : 0 < P.chartLength) (hm : ∀ s, s ≤ r ^ 2 → moving s = 0)
    (D : TimeFieldData) (σ : ℝ) {y : Space} (hy : ‖y‖ < r) :
    shapeInfoField (movedParams P moving a) D σ =ᶠ[𝓝 y] shapeInfoField P D σ := by
  filter_upwards [ball_mem_nhds hy] with x hx
  exact moved_field_eq hL hm D σ (mem_ball_zero_iff.mp hx)

theorem moved_secondDeriv_eq (hL : 0 < P.chartLength) (hm : ∀ s, s ≤ r ^ 2 → moving s = 0)
    (D : TimeFieldData) (σ : ℝ) {y : Space} (hy : ‖y‖ < r) :
    shapeHess (movedParams P moving a) D σ y = shapeHess P D σ y := by
  unfold shapeHess
  exact Finset.sum_congr rfl fun κ _ => by rw [moved_keySecondDeriv_eq hL hm κ (D.amp κ) σ hy]

theorem moved_pressure_eq (hm : ∀ s, s ≤ r ^ 2 → moving s = 0)
    (E : PressureFieldData) (σ : ℝ) {y : Space} (hy : ‖y‖ < r) :
    shapePressure (movedParams P moving a) E σ y = shapePressure P E σ y := by
  have hc : chartCoord (movedParams P moving a) y = chartCoord P y := rfl
  unfold shapePressure
  congr 1
  refine Finset.sum_congr rfl fun κ _ => ?_
  unfold pressureKeyValue
  rw [moved_keyPhase_eq hm κ σ hy, hc]

theorem moved_pressure_eventuallyEq (hm : ∀ s, s ≤ r ^ 2 → moving s = 0)
    (E : PressureFieldData) (σ : ℝ) {y : Space} (hy : ‖y‖ < r) :
    shapePressure (movedParams P moving a) E σ =ᶠ[𝓝 y] shapePressure P E σ := by
  filter_upwards [ball_mem_nhds hy] with x hx
  exact moved_pressure_eq hm E σ (mem_ball_zero_iff.mp hx)

end Internal

theorem ballAgreement_holds : BallAgreementHolds := by
  intro P moving a r D E hP _ hm _ _ σ y hy
  have hL := hP.chartLength_pos
  exact ⟨Internal.moved_field_eq hL hm D σ hy, (Internal.moved_field_eventuallyEq hL hm D σ hy).fderiv_eq,
    Internal.moved_secondDeriv_eq hL hm D σ hy, Internal.moved_pressure_eq hm E σ hy,
    (Internal.moved_pressure_eventuallyEq hm E σ hy).gradient_eq⟩

end Instantiation

end CellReduction

end Breakdown
