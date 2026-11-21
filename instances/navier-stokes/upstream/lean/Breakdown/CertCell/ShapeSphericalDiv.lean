import Breakdown.CertCell.ShapeSphericalDivFrame

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (radialVec polarVecQ azimVecQ heightRatio qOf radialScale heightDeriv)

def framedField (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (U : ℝ → ℝ → Fin 3 → ℂ) (y : Space) : Fin 3 → ℂ :=
  fun i => keyPhase P κ σ y *
    (U (chartCoord P y) (heightRatio y) 0 * (radialVec y i : ℂ) +
      U (chartCoord P y) (heightRatio y) 1 * (polarVecQ y i : ℂ) +
      U (chartCoord P y) (heightRatio y) 2 * (azimVecQ y i : ℂ))


open SphericalDivInternal

theorem framedField_eq_frameSum (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (U : ℝ → ℝ → Fin 3 → ℂ) :
    framedField P κ σ U = fun z =>
      (keyPhase P κ σ z * U (chartCoord P z) (heightRatio z) 0) • liftVec (radialField z) +
      (keyPhase P κ σ z * U (chartCoord P z) (heightRatio z) 1) • liftVec (polarField z) +
      (keyPhase P κ σ z * U (chartCoord P z) (heightRatio z) 2) • liftVec (azimField z) := by
  funext z i
  simp only [framedField, Pi.add_apply, Pi.smul_apply, smul_eq_mul, liftVec_apply, radialField_apply,
    polarField_apply, azimField_apply]
  ring

theorem complexDivergence_framedField_offAxis (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (σ : ℝ)
    (U : ℝ → ℝ → Fin 3 → ℂ) {y : Space} (hy : y 0 ≠ 0 ∨ y 1 ≠ 0)
    (hU : ∀ c, DifferentiableAt ℝ (fun z : ℝ × ℝ => U z.1 z.2 c) (chartCoord P y, heightRatio y)) :
    complexDivergence (framedField P κ σ U) y =
      keyPhase P κ σ y / (‖y‖ : ℂ) *
        (shiftedScale P κ.phaseIndex (fun t x => U t x 0) (chartCoord P y) (heightRatio y) +
          2 * U (chartCoord P y) (heightRatio y) 0 -
          heightDeriv (fun t x => polarFactor x * U t x 1) (chartCoord P y) (heightRatio y) +
          Complex.I * (labelAzimuth P.azimuthOrder κ.label : ℂ) * U (chartCoord P y) (heightRatio y) 2) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
  have hL := hP.chartLength_pos
  have hL0 : P.chartLength ≠ 0 := hL.ne'
  have hne : ‖y‖ + P.chartLength ≠ 0 := by positivity
  have hρ : y 0 ^ 2 + y 1 ^ 2 ≠ 0 := by
    rcases hy with h | h
    · positivity
    · positivity
  have hr2 := coords_sq y
  obtain ⟨LG, hG, hGv⟩ := keyPhase_hasFDerivAt P hP κ σ hy
  obtain ⟨LT, hT, hTv⟩ := chartCoord_hasFDerivAt P hL hy0
  obtain ⟨LX, hX, hXv⟩ := heightRatio_hasFDerivAt hy0
  obtain ⟨L0, h0, h0v⟩ := comp_hasFDerivAt_chart U 0 hT hX (hU 0)
  obtain ⟨L1, h1, h1v⟩ := comp_hasFDerivAt_chart U 1 hT hX (hU 1)
  obtain ⟨L2, h2, h2v⟩ := comp_hasFDerivAt_chart U 2 hT hX (hU 2)
  have hW0 : HasFDerivAt (fun z => liftVec (radialField z)) (liftVec.comp (fderiv ℝ radialField y)) y :=
    liftVec.hasFDerivAt.comp y (radialField_diff hy0).hasFDerivAt
  have hW1 : HasFDerivAt (fun z => liftVec (polarField z)) (liftVec.comp (fderiv ℝ polarField y)) y :=
    liftVec.hasFDerivAt.comp y (polarField_diff hy0).hasFDerivAt
  have hW2 : HasFDerivAt (fun z => liftVec (azimField z)) (liftVec.comp (fderiv ℝ azimField y)) y :=
    liftVec.hasFDerivAt.comp y (azimField_diff hy0).hasFDerivAt
  have hsum : HasFDerivAt (fun z =>
      (keyPhase P κ σ z * U (chartCoord P z) (heightRatio z) 0) • liftVec (radialField z) +
      (keyPhase P κ σ z * U (chartCoord P z) (heightRatio z) 1) • liftVec (polarField z) +
      (keyPhase P κ σ z * U (chartCoord P z) (heightRatio z) 2) • liftVec (azimField z)) _ y :=
    (((hG.mul h0).smul hW0).add ((hG.mul h1).smul hW1)).add ((hG.mul h2).smul hW2)
  have e0 : (∑ i : Fin 3, fderiv ℝ radialField y (unitVector i) i) = 2 / ‖y‖ := div_radialField hy0
  have e1 : (∑ i : Fin 3, fderiv ℝ polarField y (unitVector i) i) = 2 * y 2 / ‖y‖ ^ 2 := div_polarField hy0
  have e2 : (∑ i : Fin 3, fderiv ℝ azimField y (unitVector i) i) = 0 := div_azimField hy0
  have c0 : radialField y 0 = y 0 / ‖y‖ := by rw [radialField_apply]; rfl
  have c1 : radialField y 1 = y 1 / ‖y‖ := by rw [radialField_apply]; rfl
  have c2 : radialField y 2 = y 2 / ‖y‖ := by rw [radialField_apply]; rfl
  have p0 : polarField y 0 = y 2 / ‖y‖ * y 0 / ‖y‖ := by rw [polarField_apply]; rfl
  have p1 : polarField y 1 = y 2 / ‖y‖ * y 1 / ‖y‖ := by rw [polarField_apply]; rfl
  have p2 : polarField y 2 = -(1 - (y 2 / ‖y‖) ^ 2) := by rw [polarField_apply]; rfl
  have a0 : azimField y 0 = -(y 1) / ‖y‖ := by rw [azimField_apply]; rfl
  have a1 : azimField y 1 = y 0 / ‖y‖ := by rw [azimField_apply]; rfl
  have a2 : azimField y 2 = 0 := by rw [azimField_apply]; rfl
  have iR : y 0 * radialField y 0 + y 1 * radialField y 1 + y 2 * radialField y 2 = ‖y‖ := by
    rw [c0, c1, c2]
    field_simp
    linear_combination hr2
  have iP : y 0 * polarField y 0 + y 1 * polarField y 1 + y 2 * polarField y 2 = 0 := by
    rw [p0, p1, p2]
    field_simp
    linear_combination y 2 * hr2
  have iA : y 0 * azimField y 0 + y 1 * azimField y 1 + y 2 * azimField y 2 = 0 := by
    rw [a0, a1, a2]
    ring
  have wR : y 0 * radialField y 1 - y 1 * radialField y 0 = 0 := by
    rw [c0, c1]
    ring
  have wP : y 0 * polarField y 1 - y 1 * polarField y 0 = 0 := by
    rw [p0, p1]
    ring
  have wA : y 0 * azimField y 1 - y 1 * azimField y 0 = (y 0 ^ 2 + y 1 ^ 2) / ‖y‖ := by
    rw [a0, a1]
    ring
  have hRad : chartRadius P (chartCoord P y) = ‖y‖ := by
    unfold chartRadius chartCoord
    field_simp
    simp [hL0]
  have htc : chartCoord P y * (1 - chartCoord P y) = ‖y‖ * P.chartLength / (‖y‖ + P.chartLength) ^ 2 := by
    unfold chartCoord
    field_simp
    ring
  have hdx : DifferentiableAt ℝ (fun x' => U (chartCoord P y) x' 1) (heightRatio y) :=
    (hU 1).comp (heightRatio y) ((hasDerivAt_const (heightRatio y) (chartCoord P y)).prodMk
      (hasDerivAt_id (heightRatio y))).differentiableAt
  have hq : HasDerivAt (fun x' : ℝ => polarFactor x') ((-(2 * heightRatio y) : ℝ) : ℂ) (heightRatio y) := by
    have := ((hasDerivAt_pow 2 (heightRatio y)).const_sub 1).ofReal_comp
    unfold polarFactor
    convert this using 2
    push_cast
    ring
  have hhd : heightDeriv (fun t x => polarFactor x * U t x 1) (chartCoord P y) (heightRatio y) =
      ((-(2 * heightRatio y) : ℝ) : ℂ) * U (chartCoord P y) (heightRatio y) 1 +
        polarFactor (heightRatio y) * deriv (fun x' => U (chartCoord P y) x' 1) (heightRatio y) := by
    unfold heightDeriv
    rw [deriv_fun_mul hq.differentiableAt hdx, hq.deriv]
  rw [framedField_eq_frameSum]
  unfold complexDivergence
  rw [hsum.fderiv, sum_three_apply, cdiv_term, cdiv_term, cdiv_term, e0, e1, e2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.mul_apply]
  rw [hGv, hGv, hGv, h0v, h1v, h2v, hTv, hTv, hTv, hXv, hXv, hXv, iR, iP, iA, wR, wP, wA]
  unfold shiftedScale radialScale phaseSlope
  rw [hhd, hRad, htc]
  unfold polarFactor heightRatio
  rw [c2, p2, a2]
  have hnC : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hneC : (‖y‖ : ℂ) + P.chartLength ≠ 0 := by exact_mod_cast hne
  have hρC : (y 0 : ℂ) ^ 2 + (y 1 : ℂ) ^ 2 ≠ 0 := by
    have h := Complex.ofReal_ne_zero.2 hρ
    push_cast at h
    exact h
  push_cast
  field_simp
  ring

theorem complexDivergence_framedField (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (σ : ℝ)
    (U : ℝ → ℝ → Fin 3 → ℂ) {y : Space} (hy : y 1 ≠ 0)
    (hU : ∀ c, DifferentiableAt ℝ (fun z : ℝ × ℝ => U z.1 z.2 c) (chartCoord P y, heightRatio y)) :
    complexDivergence (framedField P κ σ U) y =
      keyPhase P κ σ y / (‖y‖ : ℂ) *
        (shiftedScale P κ.phaseIndex (fun t x => U t x 0) (chartCoord P y) (heightRatio y) +
          2 * U (chartCoord P y) (heightRatio y) 0 -
          heightDeriv (fun t x => polarFactor x * U t x 1) (chartCoord P y) (heightRatio y) +
          Complex.I * (labelAzimuth P.azimuthOrder κ.label : ℂ) * U (chartCoord P y) (heightRatio y) 2) :=
  complexDivergence_framedField_offAxis P hP κ σ U (Or.inr hy) hU

theorem framedField_differentiableAt (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (σ : ℝ)
    (U : ℝ → ℝ → Fin 3 → ℂ) {y : Space} (hy : y 0 ≠ 0 ∨ y 1 ≠ 0)
    (hU : ∀ c, DifferentiableAt ℝ (fun z : ℝ × ℝ => U z.1 z.2 c) (chartCoord P y, heightRatio y)) :
    DifferentiableAt ℝ (framedField P κ σ U) y := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  obtain ⟨LG, hG, -⟩ := keyPhase_hasFDerivAt P hP κ σ hy
  obtain ⟨LT, hT, -⟩ := chartCoord_hasFDerivAt P hP.chartLength_pos hy0
  obtain ⟨LX, hX, -⟩ := heightRatio_hasFDerivAt hy0
  obtain ⟨L0, h0, -⟩ := comp_hasFDerivAt_chart U 0 hT hX (hU 0)
  obtain ⟨L1, h1, -⟩ := comp_hasFDerivAt_chart U 1 hT hX (hU 1)
  obtain ⟨L2, h2, -⟩ := comp_hasFDerivAt_chart U 2 hT hX (hU 2)
  have hW0 : HasFDerivAt (fun z => liftVec (radialField z)) (liftVec.comp (fderiv ℝ radialField y)) y :=
    liftVec.hasFDerivAt.comp y (radialField_diff hy0).hasFDerivAt
  have hW1 : HasFDerivAt (fun z => liftVec (polarField z)) (liftVec.comp (fderiv ℝ polarField y)) y :=
    liftVec.hasFDerivAt.comp y (polarField_diff hy0).hasFDerivAt
  have hW2 : HasFDerivAt (fun z => liftVec (azimField z)) (liftVec.comp (fderiv ℝ azimField y)) y :=
    liftVec.hasFDerivAt.comp y (azimField_diff hy0).hasFDerivAt
  rw [framedField_eq_frameSum]
  exact ((((hG.mul h0).smul hW0).add ((hG.mul h1).smul hW1)).add ((hG.mul h2).smul hW2)).differentiableAt

theorem complexDivergence_keyVector_offAxis (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (A : KeyAmp)
    (σ : ℝ) {y : Space} (hy : y 0 ≠ 0 ∨ y 1 ≠ 0)
    (hU : ∀ c, DifferentiableAt ℝ (fun z : ℝ × ℝ => reducedComps P κ A z.1 z.2 c) (chartCoord P y, heightRatio y)) :
    complexDivergence (keyVector P κ A σ) y =
      keyPhase P κ σ y / (‖y‖ : ℂ) *
        (shiftedScale P κ.phaseIndex (fun t x => reducedComps P κ A t x 0) (chartCoord P y) (heightRatio y) +
          2 * reducedComps P κ A (chartCoord P y) (heightRatio y) 0 -
          heightDeriv (fun t x => polarFactor x * reducedComps P κ A t x 1) (chartCoord P y) (heightRatio y) +
          Complex.I * (labelAzimuth P.azimuthOrder κ.label : ℂ) * reducedComps P κ A (chartCoord P y) (heightRatio y) 2) :=
  complexDivergence_framedField_offAxis P hP κ σ (reducedComps P κ A) hy hU

end GivenShape

end CertCell

end Breakdown
