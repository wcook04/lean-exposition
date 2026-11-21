import Breakdown.Frac.StTorusApprox
import Breakdown.Frac.StOperator
import Breakdown.Torus.SelfSimilar

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracSelfSimilar.Internal

theorem rot_contDiff (hA : AxialRotationSpec) :
    ContDiff ℝ ∞ (fun p : ℝ × Space => axialRotation p.1 p.2) := by
  have hfun : (fun p : ℝ × Space => axialRotation p.1 p.2) =
      fun p => axialRotationFormula p.1 p.2 := funext fun p => hA.1 p.1 p.2
  rw [hfun]
  refine (contDiff_piLp 2).2 fun j => ?_
  have h0 : ContDiff ℝ ∞ (fun p : ℝ × Space => p.2 0) :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × Space => p.2 1) :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × Space => p.2 2) :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
  have hc : ContDiff ℝ ∞ (fun p : ℝ × Space => Real.cos p.1) := Real.contDiff_cos.comp contDiff_fst
  have hs : ContDiff ℝ ∞ (fun p : ℝ × Space => Real.sin p.1) := Real.contDiff_sin.comp contDiff_fst
  fin_cases j
  · simp only [axialRotationFormula]
    simpa using (hc.mul h0).sub (hs.mul h1)
  · simp only [axialRotationFormula]
    simpa using (hs.mul h0).add (hc.mul h1)
  · simp only [axialRotationFormula]
    simpa using h2

theorem rot_hasDerivAt (hA : AxialRotationSpec) {φ : ℝ → ℝ} {w : ℝ → Space} {φ' t : ℝ}
    {w' : Space} (hφ : HasDerivAt φ φ' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun τ => axialRotation (φ τ) (w τ))
      (φ' • axialTurn (axialRotation (φ t) (w t)) + axialRotation (φ t) w') t := by
  have hFd : DifferentiableAt ℝ (fun p : ℝ × Space => axialRotation p.1 p.2) (φ t, w t) :=
    ((rot_contDiff hA).differentiable (by simp)) _
  have hγ : HasDerivAt (fun τ => (φ τ, w τ)) (φ', w') t := hφ.prodMk hw
  have h : HasDerivAt (fun τ => axialRotation (φ τ) (w τ))
      (fderiv ℝ (fun p : ℝ × Space => axialRotation p.1 p.2) (φ t, w t) (φ', w')) t := by
    have h0 := hFd.hasFDerivAt.comp_hasDerivAt t hγ
    exact h0
  have h1 : fderiv ℝ (fun p : ℝ × Space => axialRotation p.1 p.2) (φ t, w t) ((1 : ℝ), (0 : Space))
      = axialTurn (axialRotation (φ t) (w t)) := by
    have hc : HasDerivAt (fun σ : ℝ => (σ, w t)) ((1 : ℝ), (0 : Space)) (φ t) :=
      (hasDerivAt_id' (φ t)).prodMk (hasDerivAt_const (φ t) (w t))
    have h' : HasDerivAt (fun σ => axialRotation σ (w t))
        (fderiv ℝ (fun p : ℝ × Space => axialRotation p.1 p.2) (φ t, w t) ((1 : ℝ), (0 : Space)))
        (φ t) := by
      have h0 := hFd.hasFDerivAt.comp_hasDerivAt (φ t) hc
      exact h0
    exact h'.unique (hA.2.2.2.2.2 (φ t) (w t))
  have h2 : fderiv ℝ (fun p : ℝ × Space => axialRotation p.1 p.2) (φ t, w t) ((0 : ℝ), w')
      = axialRotation (φ t) w' := by
    have h' : HasFDerivAt (fun y => axialRotation (φ t) y)
        ((fderiv ℝ (fun p : ℝ × Space => axialRotation p.1 p.2) (φ t, w t)).comp
          (ContinuousLinearMap.inr ℝ ℝ Space)) (w t) :=
      hFd.hasFDerivAt.comp (w t) (hasFDerivAt_prodMk_right (φ t) (w t))
    have h'' : HasFDerivAt (fun y => axialRotation (φ t) y)
        ((axialRotation (φ t)).toContinuousLinearEquiv : Space →L[ℝ] Space) (w t) :=
      (axialRotation (φ t)).toContinuousLinearEquiv.hasFDerivAt
    have heq := h'.unique h''
    have := congrArg (fun L : Space →L[ℝ] Space => L w') heq
    simpa using this
  have hsplit : ((φ', w') : ℝ × Space) = φ' • ((1 : ℝ), (0 : Space)) + ((0 : ℝ), w') := by
    ext <;> simp
  refine h.congr_deriv ?_
  rw [hsplit, map_add, map_smul, h1, h2]

theorem turn_comm (hA : AxialRotationSpec) (θ : ℝ) (y : Space) :
    axialTurn (axialRotation θ y) = axialRotation θ (axialTurn y) := by
  have h1 := hA.2.2.2.2.2 0 (axialRotation θ y)
  have hfun : (fun σ => axialRotation σ (axialRotation θ y)) =
      fun σ => axialRotation θ (axialRotation σ y) := by
    funext σ
    rw [← hA.2.2.1, ← hA.2.2.1, add_comm]
  rw [hfun] at h1
  have h2 : HasDerivAt (fun σ => axialRotation θ (axialRotation σ y))
      (axialRotation θ (axialTurn (axialRotation 0 y))) 0 :=
    ((axialRotation θ).toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp_hasDerivAt 0
      (hA.2.2.2.2.2 0 y)
  have h := h1.unique h2
  rw [hA.2.1] at h
  simpa using h

theorem hasFDerivAt_field (R : Space ≃ₗᵢ[ℝ] Space) (U : Space → Space) (hU : Differentiable ℝ U)
    (A r : ℝ) (x : Space) :
    HasFDerivAt (fun z : Space => A • R (U (R.symm (r • (z - center)))))
      (A • ((R.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
        ((fderiv ℝ U (R.symm (r • (x - center)))).comp
          ((R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
            (r • ContinuousLinearMap.id ℝ Space))))) x := by
  have h1 : HasFDerivAt (fun z : Space => r • (z - center)) (r • ContinuousLinearMap.id ℝ Space) x :=
    ((hasFDerivAt_id x).sub_const center).const_smul r
  have h2 := (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp x h1
  have h3 := (hU (R.symm (r • (x - center)))).hasFDerivAt.comp x h2
  have h4 := (R.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp x h3
  exact h4.const_smul A

theorem fderiv_field_apply (R : Space ≃ₗᵢ[ℝ] Space) (U : Space → Space) (hU : Differentiable ℝ U)
    (A r : ℝ) (x w : Space) :
    fderiv ℝ (fun z : Space => A • R (U (R.symm (r • (z - center))))) x w =
      (A * r) • R (fderiv ℝ U (R.symm (r • (x - center))) (R.symm w)) := by
  rw [(hasFDerivAt_field R U hU A r x).fderiv]
  simp [smul_smul, map_smul]

theorem sum_coord_conj (R : Space ≃ₗᵢ[ℝ] Space) (L : Space →L[ℝ] Space) :
    ∑ i : Fin 3, (R (L (R.symm (unitVector i)))) i = ∑ i : Fin 3, (L (unitVector i)) i := by
  have key : ∀ b : OrthonormalBasis (Fin 3) ℝ Space,
      ∑ i, inner ℝ (b i) (L (b i)) = LinearMap.trace ℝ Space (L : Space →ₗ[ℝ] Space) := fun b =>
    (LinearMap.trace_eq_sum_inner (L : Space →ₗ[ℝ] Space) b).symm
  have e : ∀ (v : Space) (i : Fin 3), v i = inner ℝ (unitVector i) v := by
    intro v i
    simp [unitVector, EuclideanSpace.inner_single_left]
  have h1 : ∑ i : Fin 3, (L (unitVector i)) i = ∑ i, inner ℝ ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
      (L ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, e (L (unitVector i)) i]
    rfl
  have h2 : ∑ i : Fin 3, (R (L (R.symm (unitVector i)))) i =
      ∑ i, inner ℝ (((EuclideanSpace.basisFun (Fin 3) ℝ).map R.symm) i)
        (L (((EuclideanSpace.basisFun (Fin 3) ℝ).map R.symm) i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply, e (R (L (R.symm (unitVector i)))) i,
      ← LinearIsometryEquiv.inner_map_map R.symm]
    simp [unitVector]
  rw [h1, h2, key, key]

theorem divergence_field (R : Space ≃ₗᵢ[ℝ] Space) (U : Space → Space) (hU : Differentiable ℝ U)
    (A r : ℝ) (x : Space) :
    divergenceAt (fun z : Space => A • R (U (R.symm (r • (z - center))))) x =
      (A * r) * divergenceAt U (R.symm (r • (x - center))) := by
  unfold divergenceAt
  simp_rw [fderiv_field_apply R U hU A r x]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, sum_coord_conj]

theorem advection_field (R : Space ≃ₗᵢ[ℝ] Space) (U : Space → Space) (hU : Differentiable ℝ U)
    (A r : ℝ) (x : Space) :
    advectionAt (fun z : Space => A • R (U (R.symm (r • (z - center))))) x =
      (A * A * r) • R (fderiv ℝ U (R.symm (r • (x - center))) (U (R.symm (r • (x - center))))) := by
  unfold advectionAt
  rw [fderiv_field_apply R U hU A r x]
  simp only [map_smul, LinearIsometryEquiv.symm_apply_apply, smul_smul]
  congr 1
  ring

theorem power_field (hC : CovarianceStatement) (α : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (U : Space → Space)
    (hU : ContDiff ℝ 2 U) (A r : ℝ) (hr : 0 < r) (x : Space) :
    fractionalPowerAt α (fun z : Space => A • R (U (R.symm (r • (z - center))))) x =
      (A * r ^ (2 * α)) • R (fractionalPowerAt α U (R.symm (r • (x - center)))) := by
  have h3 : ContDiff ℝ 2 (fun z : Space => R (U (R.symm z))) :=
    (R.toContinuousLinearEquiv : Space →L[ℝ] Space).contDiff.comp
      (hU.comp (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space).contDiff)
  have h2 : ContDiff ℝ 2 (fun z : Space => R (U (R.symm (r • z)))) :=
    h3.comp (contDiff_const_smul r)
  have h1 : ContDiff ℝ 2 (fun z : Space => R (U (R.symm (r • (z + -center))))) :=
    h2.comp (contDiff_id.add contDiff_const)
  simp only [sub_eq_add_neg]
  rw [(hC α _ h1).2.1 A x, (hC α _ h2).2.2.2 (-center) x, (hC α _ h3).1 r hr (x + -center),
    (hC α U hU).2.2.1 R (r • (x + -center)), smul_smul]

theorem inner_gradient (f : Space → ℝ) (x w : Space) :
    inner ℝ (gradientAt f x) w = fderiv ℝ f x w := by
  unfold gradientAt
  have hw : w = ∑ i : Fin 3, inner ℝ (unitVector i) w • unitVector i := by
    have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr' w
    simp only [EuclideanSpace.basisFun_apply] at this
    exact this.symm
  conv_rhs => rw [hw]
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, real_inner_smul_left, smul_eq_mul, mul_comm]

theorem gradient_field (R : Space ≃ₗᵢ[ℝ] Space) (P : Space → ℝ) (hP : Differentiable ℝ P)
    (B r : ℝ) (x : Space) :
    gradientAt (fun z : Space => B * P (R.symm (r • (z - center)))) x =
      (B * r) • R (gradientAt P (R.symm (r • (x - center)))) := by
  have h1 : HasFDerivAt (fun z : Space => r • (z - center)) (r • ContinuousLinearMap.id ℝ Space) x :=
    ((hasFDerivAt_id x).sub_const center).const_smul r
  have h2 := (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp x h1
  have h3 : HasFDerivAt (fun z : Space => B * P (R.symm (r • (z - center))))
      (B • ((fderiv ℝ P (R.symm (r • (x - center)))).comp
        ((R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
          (r • ContinuousLinearMap.id ℝ Space)))) x :=
    ((hP (R.symm (r • (x - center)))).hasFDerivAt.comp x h2).const_mul B
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_gradient, h3.fderiv, real_inner_smul_left, ← LinearIsometryEquiv.inner_map_map R.symm,
    LinearIsometryEquiv.symm_apply_apply, inner_gradient]
  simp [map_smul]
  ring

theorem hasDerivAt_rpow_sub (T t p : ℝ) (ht : t < T) :
    HasDerivAt (fun τ : ℝ => (T - τ) ^ p) (-p * (T - t) ^ p * (T - t)⁻¹) t := by
  have hp : 0 < T - t := sub_pos.2 ht
  have h1 : HasDerivAt (fun τ : ℝ => T - τ) (0 - 1) t :=
    (hasDerivAt_const t T).sub (hasDerivAt_id' t)
  have h2 := h1.rpow_const (p := p) (Or.inl hp.ne')
  convert h2 using 1
  rw [rpow_sub_one hp.ne']
  ring

theorem hasDerivAt_selfSimilar (hA : AxialRotationSpec) (α a : ℝ) (U : Space → Space)
    (hU : Differentiable ℝ U) (T t : ℝ) (hT : 0 < T) (ht : t < T) (x : Space) :
    HasDerivAt (fun τ => fracSelfSimilar α a U T τ x)
      ((T - t) ^ (-(1 - 1 / (2 * α))) •
          ((-(a * (T - t)⁻¹)) • axialRotation (-(a * similarityTime T t))
              (axialTurn (U (axialRotation (a * similarityTime T t)
                ((T - t) ^ (-(1 / (2 * α))) • (x - center)))))
            + axialRotation (-(a * similarityTime T t))
              (fderiv ℝ U (axialRotation (a * similarityTime T t)
                  ((T - t) ^ (-(1 / (2 * α))) • (x - center)))
                ((a * (T - t)⁻¹) • axialTurn (axialRotation (a * similarityTime T t)
                    ((T - t) ^ (-(1 / (2 * α))) • (x - center)))
                  + ((1 / (2 * α)) * (T - t)⁻¹) • axialRotation (a * similarityTime T t)
                    ((T - t) ^ (-(1 / (2 * α))) • (x - center)))))
        + (-(-(1 - 1 / (2 * α))) * (T - t) ^ (-(1 - 1 / (2 * α))) * (T - t)⁻¹) •
          axialRotation (-(a * similarityTime T t))
            (U (axialRotation (a * similarityTime T t) ((T - t) ^ (-(1 / (2 * α))) • (x - center)))))
      t := by
  have hfun : (fun τ => fracSelfSimilar α a U T τ x) = fun τ =>
      (T - τ) ^ (-(1 - 1 / (2 * α))) • axialRotation (-(a * similarityTime T τ))
        (U (axialRotation (a * similarityTime T τ) ((T - τ) ^ (-(1 / (2 * α))) • (x - center)))) := by
    funext τ
    simp only [fracSelfSimilar, rotatingSlice, pushForward, hA.2.2.2.1, neg_neg]
  rw [hfun]
  have hs := SelfSimilar.Internal.hasDerivAt_similarityTime T t hT ht
  have has : HasDerivAt (fun τ => a * similarityTime T τ) (a * (T - t)⁻¹) t := hs.const_mul a
  have hr := hasDerivAt_rpow_sub T t (-(1 / (2 * α))) ht
  have hq : HasDerivAt (fun τ => (T - τ) ^ (-(1 / (2 * α))) • (x - center))
      (((1 / (2 * α)) * (T - t)⁻¹) • ((T - t) ^ (-(1 / (2 * α))) • (x - center))) t := by
    refine (hr.smul_const (x - center)).congr_deriv ?_
    rw [smul_smul]
    congr 1
    ring
  have hz := rot_hasDerivAt hA has hq
  have hUz := (hU _).hasFDerivAt.comp_hasDerivAt t hz
  have hw := rot_hasDerivAt hA has.neg hUz
  have hamp := hasDerivAt_rpow_sub T t (-(1 - 1 / (2 * α))) ht
  refine (hamp.smul hw).congr_deriv ?_
  simp only [Function.comp_apply, Pi.neg_apply, turn_comm hA (-(a * similarityTime T t)),
    LinearIsometryEquiv.map_smul]

theorem rot_contDiffAt (hA : AxialRotationSpec) {θ : ℝ × Space → ℝ} {v : ℝ × Space → Space}
    {z : ℝ × Space} (hθ : ContDiffAt ℝ ∞ θ z) (hv : ContDiffAt ℝ ∞ v z) :
    ContDiffAt ℝ ∞ (fun z => axialRotation (θ z) (v z)) z := by
  have h := (rot_contDiff hA).contDiffAt.comp z (hθ.prodMk hv)
  exact h

theorem comp_contDiffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : Space → F}
    (hg : ContDiff ℝ ∞ g) {v : ℝ × Space → Space} {z : ℝ × Space} (hv : ContDiffAt ℝ ∞ v z) :
    ContDiffAt ℝ ∞ (fun z => g (v z)) z := by
  have h := hg.contDiffAt.comp z hv
  exact h

theorem contDiffAt_pow_sub (T p : ℝ) (z : ℝ × Space) (hz : z.1 < T) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => (T - z.1) ^ p) z :=
  (contDiffAt_const.sub contDiffAt_fst).rpow_const_of_ne (sub_pos.2 hz).ne'

theorem contDiffAt_point (α a T : ℝ) (hA : AxialRotationSpec) (hT : 0 < T) (z : ℝ × Space)
    (hz : z.1 < T) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => axialRotation (a * similarityTime T z.1)
      ((T - z.1) ^ (-(1 / (2 * α))) • (z.2 - center))) z := by
  have hsim := SelfSimilar.Internal.contDiffAt_similarityTime T hT z hz
  have hθ : ContDiffAt ℝ ∞ (fun z : ℝ × Space => a * similarityTime T z.1) z :=
    contDiffAt_const.mul hsim
  have hq : ContDiffAt ℝ ∞
      (fun z : ℝ × Space => (T - z.1) ^ (-(1 / (2 * α))) • (z.2 - center)) z :=
    (contDiffAt_pow_sub T (-(1 / (2 * α))) z hz).smul (contDiffAt_snd.sub contDiffAt_const)
  exact rot_contDiffAt hA hθ hq

theorem contDiffOn_field (hA : AxialRotationSpec) (α a : ℝ) (U : Space → Space)
    (hU : ContDiff ℝ ∞ U) (T : ℝ) (hT : 0 < T) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => fracSelfSimilar α a U T z.1 z.2) (Iio T ×ˢ univ) := by
  have hfun : (fun z : ℝ × Space => fracSelfSimilar α a U T z.1 z.2) = fun z =>
      (T - z.1) ^ (-(1 - 1 / (2 * α))) • axialRotation (-(a * similarityTime T z.1))
        (U (axialRotation (a * similarityTime T z.1)
          ((T - z.1) ^ (-(1 / (2 * α))) • (z.2 - center)))) := by
    funext z
    simp only [fracSelfSimilar, rotatingSlice, pushForward, hA.2.2.2.1, neg_neg]
  rw [hfun]
  intro z hz
  have hz1 : z.1 < T := hz.1
  have hsim := SelfSimilar.Internal.contDiffAt_similarityTime T hT z hz1
  have hθ : ContDiffAt ℝ ∞ (fun z : ℝ × Space => -(a * similarityTime T z.1)) z :=
    (contDiffAt_const.mul hsim).neg
  have hUz : ContDiffAt ℝ ∞ (fun z : ℝ × Space => U (axialRotation (a * similarityTime T z.1)
      ((T - z.1) ^ (-(1 / (2 * α))) • (z.2 - center)))) z :=
    comp_contDiffAt hU (contDiffAt_point α a T hA hT z hz1)
  have hout := rot_contDiffAt hA hθ hUz
  exact ((contDiffAt_pow_sub T (-(1 - 1 / (2 * α))) z hz1).smul hout).contDiffWithinAt

theorem contDiffOn_pressure (hA : AxialRotationSpec) (α a : ℝ) (P : Space → ℝ)
    (hP : ContDiff ℝ ∞ P) (T : ℝ) (hT : 0 < T) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => fracSelfSimilarPressure α a P T z.1 z.2)
      (Iio T ×ˢ univ) := by
  intro z hz
  have hz1 : z.1 < T := hz.1
  have hPz : ContDiffAt ℝ ∞ (fun z : ℝ × Space => P (axialRotation (a * similarityTime T z.1)
      ((T - z.1) ^ (-(1 / (2 * α))) • (z.2 - center)))) z :=
    comp_contDiffAt hP (contDiffAt_point α a T hA hT z hz1)
  exact ((contDiffAt_pow_sub T (-(2 - 1 / α)) z hz1).mul hPz).contDiffWithinAt

end FracSelfSimilar.Internal

open FracSelfSimilar.Internal in
theorem fracSelfSimilarSolves_of (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) (hA : AxialRotationSpec)
    (hC : CovarianceStatement) : FracSelfSimilarSolves α := by
  intro a U P hP T hT
  have hUd : Differentiable ℝ U := SelfSimilar.Internal.differentiable_of_smooth hP.smooth
  have hPd : Differentiable ℝ P := SelfSimilar.Internal.differentiable_of_smooth hP.smooth_pressure
  have hU2 : ContDiff ℝ 2 U := hP.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨contDiffOn_field hA α a U hP.smooth T hT, contDiffOn_pressure hA α a P hP.smooth_pressure T hT,
    fun t ht x => ?_⟩
  have hμ : 0 < T - t := sub_pos.2 ht
  have hα : α ≠ 0 := by linarith
  have hr : 0 < (T - t) ^ (-(1 / (2 * α))) := rpow_pos_of_pos hμ _
  have hRs : (axialRotation (-(a * similarityTime T t))).symm = axialRotation (a * similarityTime T t) := by
    rw [hA.2.2.2.1, neg_neg]
  have hfield : fracSelfSimilar α a U T t = fun z : Space =>
      (T - t) ^ (-(1 - 1 / (2 * α))) • (axialRotation (-(a * similarityTime T t)))
        (U ((axialRotation (-(a * similarityTime T t))).symm
          ((T - t) ^ (-(1 / (2 * α))) • (z - center)))) := rfl
  have hpres : fracSelfSimilarPressure α a P T t = fun z : Space =>
      (T - t) ^ (-(2 - 1 / α)) * P ((axialRotation (-(a * similarityTime T t))).symm
        ((T - t) ^ (-(1 / (2 * α))) • (z - center))) := by
    funext z
    rw [hRs]
    rfl
  have e1 : (T - t) ^ (-(1 - 1 / (2 * α))) * (T - t) ^ (-(1 - 1 / (2 * α))) *
      (T - t) ^ (-(1 / (2 * α))) = (T - t) ^ (-(1 - 1 / (2 * α))) * (T - t)⁻¹ := by
    rw [mul_assoc, ← rpow_add hμ, show -(1 - 1 / (2 * α)) + -(1 / (2 * α)) = -1 by ring,
      rpow_neg_one]
  have e2 : (T - t) ^ (-(1 - 1 / (2 * α))) * ((T - t) ^ (-(1 / (2 * α)))) ^ (2 * α) =
      (T - t) ^ (-(1 - 1 / (2 * α))) * (T - t)⁻¹ := by
    rw [← rpow_mul hμ.le, show -(1 / (2 * α)) * (2 * α) = -1 by field_simp, rpow_neg_one]
  have e3 : (T - t) ^ (-(2 - 1 / α)) * (T - t) ^ (-(1 / (2 * α))) =
      (T - t) ^ (-(1 - 1 / (2 * α))) * (T - t)⁻¹ := by
    rw [← rpow_add hμ, ← rpow_neg_one, ← rpow_add hμ]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · rw [hfield, divergence_field _ U hUd, hP.div, mul_zero]
  · have hres := hP.residual (axialRotation (a * similarityTime T t)
      ((T - t) ^ (-(1 / (2 * α))) • (x - center)))
    have hR := congrArg (axialRotation (-(a * similarityTime T t))) hres
    unfold rotatingProfileResidual advectionAt at hR
    rw [(hasDerivAt_selfSimilar hA α a U hUd T t hT ht x).deriv, hfield, hpres,
      advection_field _ U hUd, power_field hC α _ U hU2 _ _ hr, gradient_field _ P hPd, hRs, e1, e2, e3]
    simp only [map_add, map_smul, map_sub, map_zero, one_smul] at hR ⊢
    linear_combination (norm := module) ((T - t) ^ (-(1 - 1 / (2 * α))) * (T - t)⁻¹) • hR

end Breakdown.Periodic
