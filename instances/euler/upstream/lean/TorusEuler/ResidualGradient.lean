import TorusEuler.EndpointEnergy
import TorusEuler.Statement
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-! The residual gradient along the parent trajectory in (4.3). -/

open ContinuousLinearMap Filter Set
open scoped Topology

namespace TorusEuler

/-- The Eulerian material acceleration on a time slab. -/
noncomputable def materialAcceleration (I : Set ℝ) (u : Velocity) (t : ℝ) (x : Vec3) : Vec3 :=
  derivWithin (fun r => u r x) I t + fderiv ℝ (u t) x (u t x)

/-- The momentum residual for a parent velocity and pressure. -/
noncomputable def momentumResidual (I : Set ℝ) (u : Velocity) (p : Pressure) : Velocity :=
  fun t x => materialAcceleration I u t x + gradient (p t) x

/-- The spatial derivative of self-advection is the gradient squared plus the directional
derivative of the gradient. The latter uses symmetry of the spatial second derivative. -/
theorem hasFDerivAt_selfAdvection {u : Vec3 → Vec3} {x : Vec3}
    {D : Vec3 →L[ℝ] Vec3 →L[ℝ] Vec3} (hu : DifferentiableAt ℝ u x)
    (hD : HasFDerivAt (fderiv ℝ u) D x) (hSym : ∀ v w, D v w = D w v) :
    HasFDerivAt (fun y => fderiv ℝ u y (u y))
      ((fderiv ℝ u x).comp (fderiv ℝ u x) + D (u x)) x := by
  refine (hD.clm_apply hu.hasFDerivAt).congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, flip_apply, hSym v (u x)]

/-- The derivative of the material acceleration is the trajectory derivative of the
velocity gradient plus its square. `I` may include its time endpoints. -/
theorem hasFDerivAt_materialAcceleration_alongTrajectory {I : Set ℝ} {u : Velocity}
    {X : ℝ → Vec3} {t : ℝ} (ht : t ∈ I) (hI : UniqueDiffOn ℝ I)
    (hInterior : I ⊆ closure (interior I))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (I ×ˢ univ))
    (hX : HasDerivWithinAt X (u t (X t)) I t) :
    HasFDerivAt (materialAcceleration I u t)
      (derivWithin (fun r => fderiv ℝ (u r) (X r)) I t +
        (fderiv ℝ (u t) (X t)).comp (fderiv ℝ (u t) (X t))) (X t) := by
  let S := I ×ˢ (univ : Set Vec3)
  let dU := fderivWithin ℝ (Function.uncurry u) S
  let d₂U := fderivWithin ℝ dU S (t, X t)
  let timeDirection : ℝ × Vec3 := (1, 0)
  let spaceDirections := inr ℝ ℝ Vec3
  let timePart := ContinuousLinearMap.apply ℝ Vec3 timeDirection
  let spacePart := (compL ℝ Vec3 (ℝ × Vec3) Vec3).flip spaceDirections
  have hS : UniqueDiffOn ℝ S := hI.prod uniqueDiffOn_univ
  have hpt : (t, X t) ∈ S := ⟨ht, mem_univ _⟩
  have hAccum : (t, X t) ∈ closure (interior S) := by
    rw [show S = I ×ˢ (univ : Set Vec3) from rfl, interior_prod_eq, closure_prod_eq,
      interior_univ, closure_univ]
    exact ⟨hInterior ht, mem_univ _⟩
  have hSym : ∀ v w, d₂U v w = d₂U w v :=
    (hu _ hpt).isSymmSndFDerivWithinAt (by rw [minSmoothness_of_isRCLikeNormedField]) hS hAccum hpt
  have hdu (r : ℝ) (hr : r ∈ I) (y : Vec3) :
      HasFDerivWithinAt (Function.uncurry u) (dU (r, y)) S (r, y) :=
    (hu.differentiableOn (by norm_num) _ (mem_prod.mpr ⟨hr, mem_univ y⟩)).hasFDerivWithinAt
  have h₂u : HasFDerivWithinAt dU d₂U S (t, X t) :=
    DifferentiableWithinAt.hasFDerivWithinAt
      ((hu.fderivWithin hS (m := 1) (by norm_num)).differentiableOn (by norm_num) _ hpt)
  have hspace (r : ℝ) (hr : r ∈ I) (y : Vec3) :
      HasFDerivAt (u r) (spacePart (dU (r, y))) y :=
    (hdu r hr y).comp_hasFDerivAt y (hasFDerivAt_prodMk_right (𝕜 := ℝ) r y)
      (Eventually.of_forall fun z => mem_prod.mpr ⟨hr, mem_univ z⟩)
  have htime (y : Vec3) : derivWithin (fun r => u r y) I t = timePart (dU (t, y)) := by
    have h := (hdu t ht y).comp_hasDerivWithinAt t
      ((hasDerivWithinAt_id t I).prodMk (hasDerivWithinAt_const t I y))
      (fun _ hr => mem_prod.mpr ⟨hr, mem_univ y⟩)
    exact h.derivWithin (hI t ht)
  have h₂space := h₂u.comp_hasFDerivAt (X t) (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (X t))
    (Eventually.of_forall fun y => mem_prod.mpr ⟨ht, mem_univ y⟩)
  have hdxTime : HasFDerivAt (fun y => derivWithin (fun r => u r y) I t)
      (timePart.comp (d₂U.comp spaceDirections)) (X t) :=
    (timePart.hasFDerivAt.comp (X t) h₂space).congr_of_eventuallyEq
      (Eventually.of_forall htime)
  have hdxSpace : HasFDerivAt (fderiv ℝ (u t))
      (spacePart.comp (d₂U.comp spaceDirections)) (X t) :=
    (spacePart.hasFDerivAt.comp (X t) h₂space).congr_of_eventuallyEq
      (Eventually.of_forall fun y => (hspace t ht y).fderiv)
  have htrajectory := h₂u.comp_hasDerivWithinAt t ((hasDerivWithinAt_id t I).prodMk hX)
    (fun r hr => mem_prod.mpr ⟨hr, mem_univ (X r)⟩)
  have hM : HasDerivWithinAt (fun r => fderiv ℝ (u r) (X r))
      (spacePart (d₂U (1, u t (X t)))) I t :=
    (spacePart.hasFDerivAt.comp_hasDerivWithinAt t htrajectory).congr_of_mem
      (fun r hr => (hspace r hr (X r)).fderiv) ht
  let M := fderiv ℝ (u t) (X t)
  have hx : HasFDerivAt (u t) M (X t) := (hspace t ht (X t)).differentiableAt.hasFDerivAt
  have hAdv := hasFDerivAt_selfAdvection hx.differentiableAt hdxSpace
    (fun v w => hSym (0, v) (0, w))
  refine (hdxTime.add hAdv).congr_fderiv ?_
  rw [hM.derivWithin (hI t ht)]
  apply ContinuousLinearMap.ext
  intro v
  change d₂U (0, v) (1, 0) + ((M.comp M) v + d₂U (0, u t (X t)) (0, v)) =
    d₂U (1, u t (X t)) (0, v) + (M.comp M) v
  rw [hSym (0, v) (1, 0), add_left_comm, ← add_apply, ← map_add, add_comm]
  simp

/-- Equation (4.3) along a supplied parent trajectory on the closed time slab. -/
theorem endpointHessian_eq_pressureHessian_sub_residualGradient {T t : ℝ} {u : Velocity}
    {p : Pressure} {X : ℝ → Vec3} (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hX : HasDerivWithinAt X (u t (X t)) (Icc 0 T) t)
    (hp : DifferentiableAt ℝ (gradient (p t)) (X t)) :
    endpointHessian (fderiv ℝ (u t) (X t))
        (derivWithin (fun r => fderiv ℝ (u r) (X r)) (Icc 0 T) t) =
      fderiv ℝ (gradient (p t)) (X t) - fderiv ℝ (momentumResidual (Icc 0 T) u p t) (X t) := by
  have hInterior : Icc 0 T ⊆ closure (interior (Icc 0 T)) := by
    rw [interior_Icc, closure_Ioo hT.ne]
  have ha := hasFDerivAt_materialAcceleration_alongTrajectory ht (uniqueDiffOn_Icc hT)
    hInterior hu hX
  have hr := (ha.add hp.hasFDerivAt).fderiv
  change fderiv ℝ (momentumResidual (Icc 0 T) u p t) (X t) = _ at hr
  rw [hr, endpointHessian]
  abel

end TorusEuler
