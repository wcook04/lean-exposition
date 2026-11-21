import TorusEuler.EndpointSmoothSlices

/-! Energy cancellation for periodic velocity fields on the centered cell. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

/-- The pressure gradient has zero energy pairing with a periodic divergence-free field. -/
theorem integral_inner_gradient_centeredCell_eq_zero
    {w : Vec3 → Vec3} {q : Vec3 → ℝ}
    (hw : ContDiff ℝ 1 w) (hq : ContDiff ℝ 1 q)
    (hwp : SpatiallyPeriodic w) (hqp : SpatiallyPeriodic q) (hdiv : ∀ x, divergence w x = 0) :
    (∫ x in centeredCell, ⟪w x, gradient q x⟫_ℝ) = 0 := by
  simp_rw [real_inner_comm (gradient q _) (w _)]
  rw [integral_gradient_pair_centeredCell hq hw hqp hwp]
  simp only [hdiv, mul_zero, integral_zero, neg_zero]

/-- Advection by a periodic divergence-free field has zero energy pairing. -/
theorem integral_inner_advection_centeredCell_eq_zero {w v : Vec3 → Vec3}
    (hw : ContDiff ℝ 1 w) (hv : ContDiff ℝ 1 v)
    (hwp : SpatiallyPeriodic w) (hvp : SpatiallyPeriodic v) (hdiv : ∀ x, divergence v x = 0) :
    (∫ x in centeredCell, ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) = 0 := by
  let q : Vec3 → ℝ := fun x => ⟪w x, w x⟫_ℝ
  have hq := hw.inner ℝ hw
  have hqp : SpatiallyPeriodic q := by
    intro n x
    change ⟪w (x + latticeVector n), w (x + latticeVector n)⟫_ℝ = ⟪w x, w x⟫_ℝ
    rw [hwp n x]
  have hpoint (x : Vec3) :
      ⟪v x, gradient q x⟫_ℝ = 2 * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ := by
    have hd := hw.differentiable (by norm_num) x
    rw [real_inner_comm (gradient q x), inner_gradient_left]
    change fderiv ℝ (fun y => ⟪w y, w y⟫_ℝ) x (v x) = _
    rw [fderiv_inner_apply ℝ hd hd, real_inner_comm (w x), two_mul]
  have hz : (∫ x in centeredCell, ⟪v x, gradient q x⟫_ℝ) = 0 :=
    integral_inner_gradient_centeredCell_eq_zero hv hq hvp hqp hdiv
  simp_rw [hpoint] at hz
  rw [integral_const_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The cell integral of squared speed detects the zero periodic continuous field. -/
theorem eq_zero_of_integral_norm_sq_centeredCell_eq_zero {w : Vec3 → Vec3}
    (hwp : SpatiallyPeriodic w) (hw : Continuous w)
    (hzero : (∫ x in centeredCell, ‖w x‖ ^ 2) = 0) : ∀ x, w x = 0 := by
  obtain ⟨g, hg, _⟩ := hwp.existsUnique_torusFunction
  have hgc : Continuous g := isOpenQuotientMap_toUnitTorus.continuous_comp_iff.mp (by
    change Continuous (fun x => g (toUnitTorus x))
    simpa only [hg] using hw)
  have hnc : Continuous (fun a => ‖g a‖ ^ 2) := hgc.norm.pow 2
  have hInt : Integrable (fun a => ‖g a‖ ^ 2) unitTorusMeasure := by
    rw [← integrableOn_univ]
    exact hnc.continuousOn.integrableOn_compact isCompact_univ
  have hsq : (∫ a, ‖g a‖ ^ 2 ∂unitTorusMeasure) = 0 := by
    rw [torusIntegral_eq_centeredCell]
    simpa only [hg] using hzero
  have hae := (integral_eq_zero_iff_of_nonneg (fun a => sq_nonneg ‖g a‖) hInt).mp hsq
  have heq : (fun a => ‖g a‖ ^ 2) = (0 : UnitAddTorus (Fin 3) → ℝ) :=
    (Continuous.ae_eq_iff_eq unitTorusMeasure hnc continuous_const).mp hae
  intro x
  have hx : ‖w x‖ ^ 2 = 0 := by
    simpa only [hg, Pi.zero_apply] using congrFun heq (toUnitTorus x)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

end TorusEuler
