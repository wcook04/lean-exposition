import TorusEuler.Piola
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! The divergence and cutoff identities in the proof of Proposition 5.11. -/

namespace TorusEuler

noncomputable section

private def traceCLM : (Vec3 →L[ℝ] Vec3) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).comp
    (ContinuousLinearMap.apply ℝ Vec3 (EuclideanSpace.single i 1))

private theorem traceCLM_apply (D : Vec3 →L[ℝ] Vec3) :
    traceCLM D = LinearMap.trace ℝ Vec3 D.toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [traceCLM, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

/-- In a divergence-free field the divergence of advection is exactly the
trace of the square of the spatial velocity gradient. -/
theorem divergence_advection_eq_trace_square {v : Vec3 → Vec3}
    (hv : ContDiff ℝ 2 v) (hdiv : ∀ x, divergence v x = 0) (x : Vec3) :
    divergence (fun y => fderiv ℝ v y (v y)) x =
      LinearMap.trace ℝ Vec3 ((fderiv ℝ v x).comp (fderiv ℝ v x)).toLinearMap := by
  let D := fderiv ℝ v x
  let D₂ := fderiv ℝ (fderiv ℝ v) x
  have hv' : HasFDerivAt v D x := (hv.differentiable (by norm_num) x).hasFDerivAt
  have hD₂ : HasFDerivAt (fderiv ℝ v) D₂ x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  have hsym : IsSymmSndFDerivAt ℝ v x := hv.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hzero : (traceCLM.comp D₂) (v x) = 0 := by
    have hd := (traceCLM.hasFDerivAt.comp x hD₂).fderiv
    have heq : (traceCLM ∘ fderiv ℝ v) = (fun _ : Vec3 => (0 : ℝ)) := by
      funext y
      rw [Function.comp_apply, traceCLM_apply, ← divergence_eq_trace_fderiv, hdiv]
    rw [heq] at hd
    have hz : fderiv ℝ (fun _ : Vec3 => (0 : ℝ)) x = 0 :=
      (hasFDerivAt_const (c := (0 : ℝ)) x).fderiv
    rw [hz] at hd
    rw [← hd, zero_apply]
  have hadv := (hD₂.clm_apply hv').fderiv
  rw [divergence, hadv, ← traceCLM_apply]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, PiLp.add_apply, Finset.sum_add_distrib, traceCLM,
    _root_.sum_apply, ContinuousLinearMap.apply_apply]
  have hess : (∑ i : Fin 3, (D₂ (EuclideanSpace.single i 1) (v x)) i) = 0 := by
    calc
      _ = (∑ i : Fin 3, (D₂ (v x) (EuclideanSpace.single i 1)) i) := by
        exact Finset.sum_congr rfl (fun i _ => congrArg (fun w : Vec3 => w i)
          (hsym (EuclideanSpace.single i 1) (v x)))
      _ = (traceCLM.comp D₂) (v x) := by
        simp [traceCLM]
      _ = 0 := hzero
  simp [hess, D]

variable {F Q : Type*} [AddCommGroup F] [Module ℝ F] [AddCommGroup Q] [Module ℝ Q]

/-- The residual identity (5.58) in Proposition 5.11, for the projected momentum
equations and commuting cutoff and divergence. The tensor order is
`(u - V) ⊗ u + V ⊗ (u - V)`. -/
theorem projected_residual_of_cutoff
    (P cutoff : F →ₗ[ℝ] F) (tensorCutoff : Q →ₗ[ℝ] Q)
    (divTensor : Q →ₗ[ℝ] F) (tensor : F →ₗ[ℝ] F →ₗ[ℝ] Q)
    {u V u_t V_t R_u R_V pressureGradient : F}
    (hut : u_t = cutoff V_t)
    (hCommute : ∀ X, cutoff (divTensor X) = divTensor (tensorCutoff X))
    (hPressure : P (cutoff pressureGradient) = 0)
    (hV : V_t + divTensor (tensor V V) + pressureGradient = R_V)
    (hR : R_u = P (u_t + divTensor (tensor u u))) :
    R_u = P (cutoff R_V + divTensor (tensor (u - V) u + tensor V (u - V) +
      (tensor V V - tensorCutoff (tensor V V)))) := by
  have hcut : P (cutoff R_V) = P (u_t + divTensor (tensorCutoff (tensor V V))) := by
    rw [← hV]
    simp only [map_add, ← hut, hCommute, hPressure, add_zero]
  have htensor : tensor (u - V) u + tensor V (u - V) + (tensor V V - tensorCutoff (tensor V V)) =
      tensor u u - tensorCutoff (tensor V V) := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  rw [hR, htensor]
  calc
    _ = P (u_t + divTensor (tensorCutoff (tensor V V))) +
        P (divTensor (tensor u u - tensorCutoff (tensor V V))) := by
      simp only [map_add, map_sub]
      abel
    _ = _ := by rw [← hcut, map_add]

end

end TorusEuler
