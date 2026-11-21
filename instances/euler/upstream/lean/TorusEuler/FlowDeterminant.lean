/-
Copyright 2026 Anthropic, PBC
SPDX-License-Identifier: Apache-2.0

The coordinate determinant calculation is adapted from
`CCPoint/Lib/R04/DetLiouville.lean` in the September CCPoint archive.
-/
import TorusEuler.LinearFlow
import TorusEuler.Statement
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Ring

open Set

namespace TorusEuler

private noncomputable def flowMatrix (A : Vec3 →L[ℝ] Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  LinearMap.toMatrix b b A.toLinearMap

private theorem flowMatrix_apply (A : Vec3 →L[ℝ] Vec3) (i j : Fin 3) :
    flowMatrix A i j = (A (EuclideanSpace.single j 1)) i := by
  simp [flowMatrix, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply]

private theorem flowMatrix_comp (A F : Vec3 →L[ℝ] Vec3) :
    flowMatrix (A.comp F) = flowMatrix A * flowMatrix F :=
  LinearMap.toMatrix_comp _ _ _ A.toLinearMap F.toLinearMap

private theorem matrix_det_hasDerivWithinAt {f : ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    {A : Matrix (Fin 3) (Fin 3) ℝ} {s : Set ℝ} {t : ℝ}
    (h : ∀ i j, HasDerivWithinAt (fun r => f r i j) ((A * f t) i j) s t) :
    HasDerivWithinAt (fun r => (f r).det) (A.trace * (f t).det) s t := by
  have h₁ := ((h 0 0).mul (h 1 1)).mul (h 2 2)
  have h₂ := ((h 0 0).mul (h 1 2)).mul (h 2 1)
  have h₃ := ((h 0 1).mul (h 1 0)).mul (h 2 2)
  have h₄ := ((h 0 1).mul (h 1 2)).mul (h 2 0)
  have h₅ := ((h 0 2).mul (h 1 0)).mul (h 2 1)
  have h₆ := ((h 0 2).mul (h 1 1)).mul (h 2 0)
  have hdet := ((((h₁.sub h₂).sub h₃).add h₄).add h₅).sub h₆
  simp only [Matrix.det_fin_three]
  refine hdet.congr_deriv ?_
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, Pi.mul_apply]
  ring

/-- Liouville's determinant identity for a variational equation on `Vec3`. -/
theorem hasDerivWithinAt_det_flow {F : ℝ → Vec3 →L[ℝ] Vec3}
    {M : Vec3 →L[ℝ] Vec3} {s : Set ℝ} {t : ℝ}
    (hF : HasDerivWithinAt F (M.comp (F t)) s t) :
    HasDerivWithinAt (fun r => LinearMap.det (F r).toLinearMap)
      (LinearMap.trace ℝ Vec3 M.toLinearMap * LinearMap.det (F t).toLinearMap) s t := by
  have hcoord (i j : Fin 3) : HasDerivWithinAt (fun r => flowMatrix (F r) i j)
      ((flowMatrix M * flowMatrix (F t)) i j) s t := by
    rw [← flowMatrix_comp]
    simp only [flowMatrix_apply]
    have hev : HasDerivWithinAt (fun r => F r (EuclideanSpace.single j 1))
        ((M.comp (F t)) (EuclideanSpace.single j 1)) s t := by
      simpa using hF.clm_apply (hasDerivWithinAt_const t s (EuclideanSpace.single j 1))
    exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivWithinAt t hev
  simpa only [flowMatrix, LinearMap.det_toMatrix, ← LinearMap.trace_eq_matrix_trace] using
    matrix_det_hasDerivWithinAt hcoord

/-- A normalized flow with trace-free coefficient has determinant one on its interval. -/
theorem det_flow_eq_one {F M : ℝ → Vec3 →L[ℝ] Vec3} {J : Set ℝ} {t₀ : ℝ}
    (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (hF : ∀ t ∈ J, HasDerivWithinAt F ((M t).comp (F t)) J t)
    (htr : ∀ t ∈ J, LinearMap.trace ℝ Vec3 (M t).toLinearMap = 0)
    (h₀ : F t₀ = ContinuousLinearMap.id ℝ Vec3) :
    ∀ t ∈ J, LinearMap.det (F t).toLinearMap = 1 := by
  refine linearODE_unique_of_mem (A := fun _ => 0) hJ ht₀ continuousOn_const
    (fun t ht => ?_) (fun t _ => by simpa using hasDerivWithinAt_const t J (1 : ℝ)) ?_
  · simpa only [htr t ht, zero_mul, zero_apply] using hasDerivWithinAt_det_flow (hF t ht)
  · rw [h₀]
    exact LinearMap.det_id

end TorusEuler
