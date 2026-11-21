import TorusEuler.FlowDeterminant
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Trace

open Filter Set
open scoped Topology

namespace TorusEuler

/-- Divergence in the Euclidean lift is the trace of the spatial derivative. -/
theorem divergence_eq_trace_fderiv (v : Vec3 → Vec3) (a : Vec3) :
    divergence v a = LinearMap.trace ℝ Vec3 (fderiv ℝ v a).toLinearMap := by
  rw [divergence, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

/-- When the determinant is locally one, its directional derivative gives a zero trace. -/
theorem trace_deriv_comp_inverse_eq_zero {F : Vec3 → Vec3 →L[ℝ] Vec3}
    {DF : Vec3 →L[ℝ] Vec3 →L[ℝ] Vec3} {G : Vec3 →L[ℝ] Vec3} {a : Vec3}
    (hF : HasFDerivAt F DF a) (hGF : G.comp (F a) = ContinuousLinearMap.id ℝ Vec3)
    (hdet : ∀ᶠ b in 𝓝 a, LinearMap.det (F b).toLinearMap = 1) (w : Vec3) :
    LinearMap.trace ℝ Vec3 ((DF w).comp G).toLinearMap = 0 := by
  have hline : HasDerivAt (fun s : ℝ => a + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add a
  have htend : Tendsto (fun s : ℝ => a + s • w) (𝓝 0) (𝓝 a) := by
    simpa [ContinuousAt] using hline.continuousAt
  have hF₀ : HasFDerivAt F DF (a + (0 : ℝ) • w) := by simpa using hF
  have hpath := hF₀.comp_hasDerivAt 0 hline
  have hcomp : ((DF w).comp G).comp (F a) = DF w := by
    rw [ContinuousLinearMap.comp_assoc, hGF, ContinuousLinearMap.comp_id]
  have hflow : HasDerivWithinAt (fun s : ℝ => F (a + s • w))
      (((DF w).comp G).comp (F (a + (0 : ℝ) • w))) univ 0 := by
    simpa [Function.comp_def, hcomp] using hpath.hasDerivWithinAt (s := univ)
  have hdet' : HasDerivAt (fun s : ℝ => LinearMap.det (F (a + s • w)).toLinearMap)
      (LinearMap.trace ℝ Vec3 ((DF w).comp G).toLinearMap) 0 := by
    have hdet₁ : (fun b => LinearMap.det (F b).toLinearMap) =ᶠ[𝓝 a] (fun _ => 1) := hdet
    simpa [hdet₁.eq_of_nhds] using
      (hasDerivWithinAt_det_flow hflow).hasDerivAt Filter.univ_mem
  exact hdet'.unique ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq
    (htend.eventually hdet))

/-- Pointwise Piola identity for a volume-preserving deformation and a differentiable
local left inverse. The derivative of the deformation gradient is symmetric. -/
theorem divergence_piola {X Y v : Vec3 → Vec3} {F : Vec3 → Vec3 →L[ℝ] Vec3}
    {DF : Vec3 →L[ℝ] Vec3 →L[ℝ] Vec3} {G Dv : Vec3 →L[ℝ] Vec3} {a : Vec3}
    (hX : HasFDerivAt X (F a) a) (hF : HasFDerivAt F DF a)
    (hsym : ∀ w z : Vec3, DF w z = DF z w)
    (hY : HasFDerivAt Y G (X a)) (hYX : Y ∘ X =ᶠ[𝓝 a] id)
    (hdet : ∀ᶠ b in 𝓝 a, LinearMap.det (F b).toLinearMap = 1)
    (hv : HasFDerivAt v Dv a) :
    divergence (fun x => F (Y x) (v (Y x))) (X a) = divergence v a := by
  have hYa : Y (X a) = a := hYX.eq_of_nhds
  have hGF : G.comp (F a) = ContinuousLinearMap.id ℝ Vec3 :=
    ((hY.comp a hX).congr_of_eventuallyEq hYX.symm).unique (hasFDerivAt_id a)
  have hFv : HasFDerivAt (fun b => F b (v b)) ((F a).comp Dv + DF.flip (v a)) (Y (X a)) := by
    rw [hYa]
    exact hF.clm_apply hv
  have hpush : HasFDerivAt (fun x => F (Y x) (v (Y x)))
      (((F a).comp Dv + DF.flip (v a)).comp G) (X a) := hFv.comp (X a) hY
  have hflip : DF.flip (v a) = DF (v a) := by
    apply ContinuousLinearMap.ext
    intro z
    exact hsym z (v a)
  rw [divergence_eq_trace_fderiv, divergence_eq_trace_fderiv, hpush.fderiv, hv.fderiv,
    hflip, ContinuousLinearMap.add_comp]
  change LinearMap.trace ℝ Vec3
    ((((F a).comp Dv).comp G).toLinearMap + ((DF (v a)).comp G).toLinearMap) = _
  rw [map_add, trace_deriv_comp_inverse_eq_zero hF hGF hdet, add_zero]
  change LinearMap.trace ℝ Vec3 (((F a).toLinearMap.comp Dv.toLinearMap).comp G.toLinearMap) = _
  rw [LinearMap.trace_comp_cycle']
  change LinearMap.trace ℝ Vec3 ((G.comp (F a)).toLinearMap.comp Dv.toLinearMap) = _
  rw [hGF]
  exact congrArg (LinearMap.trace ℝ Vec3) (LinearMap.id_comp _)

/-- The pointwise Piola identity for a (C^2) deformation whose Jacobian determinant
is one near the label. -/
theorem divergence_piola_of_contDiffAt {X Y v : Vec3 → Vec3} {G Dv : Vec3 →L[ℝ] Vec3}
    {a : Vec3} (hX : ContDiffAt ℝ 2 X a) (hY : HasFDerivAt Y G (X a))
    (hYX : Y ∘ X =ᶠ[𝓝 a] id)
    (hdet : ∀ᶠ b in 𝓝 a, LinearMap.det (fderiv ℝ X b).toLinearMap = 1)
    (hv : HasFDerivAt v Dv a) :
    divergence (fun x => fderiv ℝ X (Y x) (v (Y x))) (X a) = divergence v a :=
  divergence_piola (hX.differentiableAt (by simp)).hasFDerivAt
    (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
    (hX.isSymmSndFDerivAt (by simp)) hY hYX hdet hv

end TorusEuler
