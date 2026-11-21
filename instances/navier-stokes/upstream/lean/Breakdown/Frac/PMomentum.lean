import Breakdown.Frac.StProfile
import Breakdown.Frac.OpCovariance
import Breakdown.Frac.PAxial

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown


namespace FracInternal

namespace Momentum

open FracInternal.Axial

theorem turn_rot_comm (h : AxialRotationSpec) (θ : ℝ) (y : Space) :
    axialTurn (axialRotation θ y) = axialRotation θ (axialTurn y) := by
  rw [h.1, h.1]
  apply space_coord_ext
  · simp only [turn_zero_coord, axialFormula_zero_coord, axialFormula_one_coord, turn_one_coord]
    ring
  · simp only [turn_one_coord, axialFormula_zero_coord, axialFormula_one_coord, turn_zero_coord]
    ring
  · simp only [turn_two_coord, axialFormula_two_coord]

def rotMap (θ : ℝ) : Space →L[ℝ] Space :=
  ((axialRotation θ).toContinuousLinearEquiv : Space →L[ℝ] Space)

theorem rotMap_apply (θ : ℝ) (y : Space) : rotMap θ y = axialRotation θ y := rfl

def axisPart : Space →L[ℝ] Space := (1 / 2 : ℝ) • (rotMap 0 + rotMap π)

def cosPart : Space →L[ℝ] Space := rotMap 0 - axisPart

def sinPart : Space →L[ℝ] Space := rotMap (π / 2) - axisPart

theorem rotMap_split (h : AxialRotationSpec) (θ : ℝ) :
    rotMap θ = Real.cos θ • cosPart + Real.sin θ • sinPart + axisPart := by
  ext1 y
  simp only [add_apply, smul_apply, cosPart, sinPart,
    axisPart, sub_apply, rotMap_apply, h.1]
  apply space_coord_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      axialFormula_zero_coord, Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      axialFormula_one_coord, Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      axialFormula_two_coord]
    ring

theorem rot_hasDerivAt (h : AxialRotationSpec) {θ : ℝ → ℝ} {θ' t : ℝ} {u : ℝ → Space}
    {u' : Space} (hθ : HasDerivAt θ θ' t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun τ => axialRotation (θ τ) (u τ))
      (θ' • axialTurn (axialRotation (θ t) (u t)) + axialRotation (θ t) u') t := by
  have hL : HasDerivAt (fun τ => Real.cos (θ τ) • cosPart + Real.sin (θ τ) • sinPart + axisPart)
      ((-Real.sin (θ t) * θ') • cosPart + (Real.cos (θ t) * θ') • sinPart) t := by
    have := ((hθ.cos.smul_const cosPart).add (hθ.sin.smul_const sinPart)).add_const axisPart
    exact this
  have hA := hL.clm_apply hu
  have hfun : (fun τ => axialRotation (θ τ) (u τ)) =
      fun τ => (Real.cos (θ τ) • cosPart + Real.sin (θ τ) • sinPart + axisPart) (u τ) := by
    funext τ
    rw [← rotMap_split h, rotMap_apply]
  rw [hfun]
  refine hA.congr_deriv ?_
  rw [← rotMap_split h, rotMap_apply]
  congr 1
  have e := congrArg (fun L : Space →L[ℝ] Space => L (u t)) (rotMap_split h (θ t))
  simp only [rotMap_apply] at e
  rw [e]
  simp only [add_apply, smul_apply, cosPart, sinPart,
    axisPart, sub_apply, rotMap_apply, h.1]
  apply space_coord_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, turn_zero_coord,
      axialFormula_zero_coord, axialFormula_one_coord, Real.cos_zero, Real.sin_zero, Real.cos_pi,
      Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, turn_one_coord,
      axialFormula_zero_coord, axialFormula_one_coord, Real.cos_zero, Real.sin_zero, Real.cos_pi,
      Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, turn_two_coord,
      axialFormula_two_coord]
    ring

end Momentum

end FracInternal


namespace FracInternal

namespace Momentum

theorem vec_sum (w : Space) : w = ∑ j : Fin 3, w j • unitVector j := by
  ext i
  simp [unitVector, Pi.single_apply]

theorem apply_inner_sum (L : Space →L[ℝ] ℝ) (v : Space) :
    L v = inner ℝ (∑ i : Fin 3, L (unitVector i) • unitVector i) v := by
  conv_lhs => rw [vec_sum v]
  simp only [map_sum, map_smul, sum_inner, inner_smul_left, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [unitVector, EuclideanSpace.inner_single_left, mul_comm]

theorem gradientAt_comp_isometry (R : Space ≃ₗᵢ[ℝ] Space) {φ : Space → ℝ}
    (hφ : Differentiable ℝ φ) (y : Space) :
    gradientAt (fun z => φ (R.symm z)) y = R (gradientAt φ (R.symm y)) := by
  have hd : ∀ v, fderiv ℝ (fun z => φ (R.symm z)) y v = fderiv ℝ φ (R.symm y) (R.symm v) := by
    intro v
    have h2 : HasFDerivAt (fun z => φ (R.symm z)) ((fderiv ℝ φ (R.symm y)).comp
        ((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space)) y :=
      (hφ (R.symm y)).hasFDerivAt.comp y (R.symm.toContinuousLinearEquiv).hasFDerivAt
    rw [h2.fderiv]
    rfl
  simp only [gradientAt, hd]
  have hg : ∀ i, fderiv ℝ φ (R.symm y) (R.symm (unitVector i)) =
      (R (∑ j : Fin 3, fderiv ℝ φ (R.symm y) (unitVector j) • unitVector j)) i := by
    intro i
    rw [apply_inner_sum, ← R.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
    simp [unitVector, EuclideanSpace.inner_single_right]
  simp only [hg]
  exact (vec_sum _).symm

theorem gradientAt_scaled (k m : ℝ) {Q : Space → ℝ} (hQ : Differentiable ℝ Q) (x : Space) :
    gradientAt (fun y => k * Q (m • y)) x = (k * m) • gradientAt Q (m • x) := by
  have hs : HasFDerivAt (fun y : Space => k * Q (m • y))
      (k • (fderiv ℝ Q (m • x)).comp (m • ContinuousLinearMap.id ℝ Space)) x :=
    ((hQ (m • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul m)).const_mul k
  have hd : ∀ v, fderiv ℝ (fun y : Space => k * Q (m • y)) x v = k * (m * fderiv ℝ Q (m • x) v) := by
    intro v
    rw [hs.fderiv]
    simp
  simp only [gradientAt, hd, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_assoc]

theorem fderiv_scaled_apply (c m : ℝ) {V : Space → Space} (hV : Differentiable ℝ V) (x v : Space) :
    fderiv ℝ (fun y => c • V (m • y)) x v = c • m • fderiv ℝ V (m • x) v := by
  have hs : HasFDerivAt (fun y : Space => c • V (m • y))
      (c • (fderiv ℝ V (m • x)).comp (m • ContinuousLinearMap.id ℝ Space)) x :=
    ((hV (m • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul m)).const_smul c
  rw [hs.fderiv]
  simp

theorem fderiv_pushForward_apply (R : Space ≃ₗᵢ[ℝ] Space) {U : Space → Space}
    (hU : Differentiable ℝ U) (y v : Space) :
    fderiv ℝ (pushForward R U) y v = R (fderiv ℝ U (R.symm y) (R.symm v)) := by
  have hs : HasFDerivAt (pushForward R U)
      ((R.toContinuousLinearEquiv : Space →L[ℝ] Space).comp ((fderiv ℝ U (R.symm y)).comp
        (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space))) y :=
    R.toContinuousLinearEquiv.hasFDerivAt.comp y
      ((hU (R.symm y)).hasFDerivAt.comp y R.symm.toContinuousLinearEquiv.hasFDerivAt)
  rw [hs.fderiv]
  rfl

theorem scalar_facts (α l : ℝ) (hα : α ≠ 0) (hl : 0 < l) :
    l ^ (1 - 1 / (2 * α)) * (l ^ (1 / (2 * α))) ^ (2 * α) = l ^ (1 - 1 / (2 * α)) * l ∧
    l ^ (1 - 1 / (2 * α)) * l ^ (1 / (2 * α)) * l ^ (1 - 1 / (2 * α)) =
      l ^ (1 - 1 / (2 * α)) * l ∧
    l ^ (2 - 1 / α) * l ^ (1 / (2 * α)) = l ^ (1 - 1 / (2 * α)) * l := by
  have e1 : 1 / (2 * α) * (2 * α) = 1 := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.rpow_mul hl.le, e1, Real.rpow_one]
  · rw [← Real.rpow_add hl, sub_add_cancel, Real.rpow_one, mul_comm]
  · rw [← Real.rpow_add hl, ← Real.rpow_add_one hl.ne']
    congr 1
    field_simp
    ring

theorem final_alg (R : Space ≃ₗᵢ[ℝ] Space) (D : Space →L[ℝ] Space) (u tw w au gp : Space)
    (a c l g E1 E2 E3 : ℝ) (h1 : E1 = c * l) (h2 : E2 = c * l) (h3 : E3 = c * l)
    (hres : (1 - g) • u + g • D w + a • (D tw - axialTurn u) + (1 : ℝ) • au + D u + gp = 0)
    (hcomm : axialTurn (R u) = R (axialTurn u)) :
    c • ((-(a * l)) • axialTurn (R u) + R (D ((a * l) • tw + (g * l) • w)))
        + ((1 - g) * c * l) • R u =
      -(E1 • R au) - E2 • R (D u) - E3 • R gp := by
  subst h1 h2 h3
  rw [hcomm]
  have hau : au = -((1 - g) • u + g • D w + a • (D tw - axialTurn u) + D u + gp) := by
    rw [← sub_eq_zero, ← hres]
    module
  rw [hau]
  simp only [map_add, map_smul, map_sub, map_neg]
  module

end Momentum

end FracInternal


namespace FracInternal

namespace Momentum

theorem selfSimilar_hasDerivAt (h : AxialRotationSpec) (α a : ℝ) (U : Space → Space)
    (hU : Differentiable ℝ U) (s₀ t : ℝ) (ht : t < 1) (x : Space) :
    HasDerivAt (fun τ => selfSimilarField α a U s₀ τ x)
      (((1 - t)⁻¹) ^ (1 - 1 / (2 * α)) •
          ((-(a * (1 - t)⁻¹)) • axialTurn (axialRotation (-(a * (s₀ - Real.log (1 - t))))
              (U ((axialRotation (-(a * (s₀ - Real.log (1 - t))))).symm
                (((1 - t)⁻¹) ^ (1 / (2 * α)) • x))))
            + axialRotation (-(a * (s₀ - Real.log (1 - t))))
              (fderiv ℝ U ((axialRotation (-(a * (s₀ - Real.log (1 - t))))).symm
                  (((1 - t)⁻¹) ^ (1 / (2 * α)) • x))
                ((a * (1 - t)⁻¹) • axialTurn ((axialRotation (-(a * (s₀ - Real.log (1 - t))))).symm
                    (((1 - t)⁻¹) ^ (1 / (2 * α)) • x))
                  + (1 / (2 * α) * (1 - t)⁻¹) • (axialRotation (-(a * (s₀ - Real.log (1 - t))))).symm
                    (((1 - t)⁻¹) ^ (1 / (2 * α)) • x))))
        + ((1 - 1 / (2 * α)) * ((1 - t)⁻¹) ^ (1 - 1 / (2 * α)) * (1 - t)⁻¹) •
          axialRotation (-(a * (s₀ - Real.log (1 - t))))
            (U ((axialRotation (-(a * (s₀ - Real.log (1 - t))))).symm
              (((1 - t)⁻¹) ^ (1 / (2 * α)) • x)))) t := by
  have hne : (1 - t) ≠ 0 := by linarith
  have hpos : 0 < (1 - t)⁻¹ := inv_pos.mpr (by linarith)
  have hsymm : ∀ θ y, (axialRotation (-θ)).symm y = axialRotation θ y := by
    intro θ y
    rw [h.2.2.2.1, neg_neg]
  set l := (1 - t)⁻¹ with hl
  set g := 1 / (2 * α) with hg
  have h1 : HasDerivAt (fun τ : ℝ => 1 - τ) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
  have hlam : HasDerivAt (fun τ : ℝ => (1 - τ)⁻¹) (l ^ 2) t := by
    refine (h1.inv hne).congr_deriv ?_
    rw [hl, inv_pow]
    ring
  have hc : HasDerivAt (fun τ : ℝ => ((1 - τ)⁻¹) ^ (1 - g)) ((1 - g) * l ^ (1 - g) * l) t := by
    refine (hlam.rpow_const (Or.inl hpos.ne')).congr_deriv ?_
    have e : l ^ (1 - g) = l ^ (1 - g - 1) * l := by
      rw [← Real.rpow_add_one hpos.ne', sub_add_cancel]
    rw [e]
    ring
  have hm : HasDerivAt (fun τ : ℝ => ((1 - τ)⁻¹) ^ g) (g * l * l ^ g) t := by
    refine (hlam.rpow_const (Or.inl hpos.ne')).congr_deriv ?_
    have e : l ^ g = l ^ (g - 1) * l := by
      rw [← Real.rpow_add_one hpos.ne', sub_add_cancel]
    rw [e]
    ring
  have hθ : HasDerivAt (fun τ : ℝ => a * (s₀ - Real.log (1 - τ))) (a * l) t := by
    refine ((h1.log hne).const_sub s₀).const_mul a |>.congr_deriv ?_
    rw [hl]
    field_simp
  have hy : HasDerivAt (fun τ : ℝ => ((1 - τ)⁻¹) ^ g • x) ((g * l * l ^ g) • x) t :=
    hm.smul_const x
  have hw := rot_hasDerivAt h hθ hy
  set w := axialRotation (a * (s₀ - Real.log (1 - t))) (l ^ g • x) with hwdef
  have hU' : HasDerivAt (fun τ => U (axialRotation (a * (s₀ - Real.log (1 - τ)))
      (((1 - τ)⁻¹) ^ g • x)))
      (fderiv ℝ U w ((a * l) • axialTurn w +
        axialRotation (a * (s₀ - Real.log (1 - t))) ((g * l * l ^ g) • x))) t :=
    (hU w).hasFDerivAt.comp_hasDerivAt t hw
  have hRU := rot_hasDerivAt h hθ.neg hU'
  have hF := hc.smul hRU
  have hfun : (fun τ => selfSimilarField α a U s₀ τ x) = fun τ =>
      ((1 - τ)⁻¹) ^ (1 - g) • axialRotation (-(a * (s₀ - Real.log (1 - τ))))
        (U (axialRotation (a * (s₀ - Real.log (1 - τ))) (((1 - τ)⁻¹) ^ g • x))) := by
    funext τ
    simp only [selfSimilarField, scaleField, rotatingSlice, pushForward, hsymm, hg]
  rw [hfun]
  refine hF.congr_deriv ?_
  simp only [hsymm, Pi.neg_apply, ← hl]
  rw [← hwdef]
  have e2 : axialRotation (a * (s₀ - Real.log (1 - t))) ((g * l * l ^ g) • x) = (g * l) • w := by
    rw [hwdef, ← map_smul, smul_smul]
  rw [e2, turn_rot_comm h]

end Momentum

end FracInternal


open FracInternal FracInternal.Momentum in
theorem selfSimilarMomentum (h : AxialRotationSpec) : SelfSimilarMomentum := by
  intro α hα _ a U P hp s₀ t ht x
  have hα0 : α ≠ 0 := by linarith
  have hUd : Differentiable ℝ U := hp.smooth.differentiable (by simp)
  have hU2 : ContDiff ℝ 2 U := hp.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
  have hPd : Differentiable ℝ P := hp.smooth_pressure.differentiable (by simp)
  refine (selfSimilar_hasDerivAt h α a U hUd s₀ t ht x).congr_deriv ?_
  have hpos : 0 < (1 - t)⁻¹ := inv_pos.mpr (by linarith)
  set l := (1 - t)⁻¹ with hl
  set R := axialRotation (-(a * (s₀ - Real.log (1 - t)))) with hR
  set c := l ^ (1 - 1 / (2 * α)) with hc
  set m := l ^ (1 / (2 * α)) with hm
  set w := R.symm (m • x) with hw
  have hmpos : 0 < m := Real.rpow_pos_of_pos hpos _
  have hVd : Differentiable ℝ (rotatingSlice a U (s₀ - Real.log (1 - t))) :=
    (R.toContinuousLinearEquiv.differentiable).comp
      (hUd.comp R.symm.toContinuousLinearEquiv.differentiable)
  have hV2 : ContDiff ℝ 2 (rotatingSlice a U (s₀ - Real.log (1 - t))) :=
    R.contDiff.comp (hU2.comp R.symm.contDiff)
  have hF : selfSimilarField α a U s₀ t =
      fun y => c • rotatingSlice a U (s₀ - Real.log (1 - t)) (m • y) := rfl
  have hA : fractionalPowerAt α (selfSimilarField α a U s₀ t) x =
      (c * m ^ (2 * α)) • R (fractionalPowerAt α U w) := by
    rw [hF]
    have e1 : fractionalPowerAt α (fun y => c • rotatingSlice a U (s₀ - Real.log (1 - t)) (m • y)) x =
        c • fractionalPowerAt α (fun y => rotatingSlice a U (s₀ - Real.log (1 - t)) (m • y)) x :=
      fractionalPowerAt_const_smul α _ (hV2.comp (contDiff_const_smul m)) c x
    have e2 : fractionalPowerAt α (fun y => rotatingSlice a U (s₀ - Real.log (1 - t)) (m • y)) x =
        m ^ (2 * α) • fractionalPowerAt α (rotatingSlice a U (s₀ - Real.log (1 - t))) (m • x) :=
      fractionalPowerAt_comp_smul α _ hV2 m hmpos x
    have e3 : fractionalPowerAt α (rotatingSlice a U (s₀ - Real.log (1 - t))) (m • x) =
        R (fractionalPowerAt α U (R.symm (m • x))) :=
      fractionalPowerAt_comp_isometry α U hU2 R (m • x)
    rw [e1, e2, e3, smul_smul]
  have hAdv : advectionAt (selfSimilarField α a U s₀ t) x =
      (c * m * c) • R (fderiv ℝ U w (U w)) := by
    rw [hF]
    unfold advectionAt
    rw [fderiv_scaled_apply c m hVd x]
    have e : rotatingSlice a U (s₀ - Real.log (1 - t)) = pushForward R U := rfl
    rw [e, fderiv_pushForward_apply R hUd]
    simp only [pushForward]
    rw [← hw]
    simp only [map_smul, LinearIsometryEquiv.symm_apply_apply, smul_smul]
    congr 1
    ring
  have hsymm : ∀ y, R.symm y = axialRotation (a * (s₀ - Real.log (1 - t))) y := by
    intro y
    rw [hR, h.2.2.2.1, neg_neg]
  have hGrad : gradientAt (selfSimilarPressure α a P s₀ t) x =
      (l ^ (2 - 1 / α) * m) • R (gradientAt P w) := by
    have e : selfSimilarPressure α a P s₀ t = fun y => l ^ (2 - 1 / α) * (fun z => P (R.symm z)) (m • y) := by
      funext y
      simp only [selfSimilarPressure, hsymm, hl, hm]
    rw [e, gradientAt_scaled (Q := fun z => P (R.symm z)) _ _ (hPd.comp R.symm.toContinuousLinearEquiv.differentiable) x,
      gradientAt_comp_isometry R hPd]
  rw [hA, hAdv, hGrad]
  obtain ⟨f1, f2, f3⟩ := scalar_facts α l hα0 hpos
  have hres := hp.residual w
  unfold rotatingProfileResidual advectionAt at hres
  have hcomm : axialTurn (R (U w)) = R (axialTurn (U w)) := turn_rot_comm h _ _
  exact final_alg R (fderiv ℝ U w) (U w) (axialTurn w) w (fractionalPowerAt α U w) (gradientAt P w)
    a c l (1 / (2 * α)) _ _ _ f1 f2 f3 hres hcomm

end Breakdown
