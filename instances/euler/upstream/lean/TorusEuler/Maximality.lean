import TorusEuler.Statement
import Mathlib.Tactic.FinCases

open Filter Set
open scoped ContDiff Topology

namespace TorusEuler

theorem continuous_curlOfDerivative :
    Continuous (curlOfDerivative : (Vec3 →L[ℝ] Vec3) → Vec3) := by
  have hcoord (j i : Fin 3) :
      Continuous (fun D : Vec3 →L[ℝ] Vec3 => (D (EuclideanSpace.single j 1)) i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp
      (continuous_id.clm_apply continuous_const)
  unfold curlOfDerivative
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact (hcoord 1 2).sub (hcoord 2 1)
  · exact (hcoord 2 0).sub (hcoord 0 2)
  · exact (hcoord 0 1).sub (hcoord 1 0)

/-- The maximal-lifespan implication of Corollary 8.3. -/
theorem IsEulerSolution.isMaximal_of_tendsto_curl_atTop
    {T : ℝ} {u : Velocity} {p : Pressure} (hu : IsEulerSolution T u p)
    (hblowup : Tendsto (fun t => ‖curl (u t) 0‖) (𝓝[Ico 0 T] T) atTop) :
    IsMaximalEulerSolution T u p := by
  refine ⟨hu, ?_⟩
  rintro S hTS ⟨v, q, hv, hagree⟩
  have htime : Ico 0 S ∈ 𝓝 T :=
    mem_of_superset (Ioo_mem_nhds hu.time_pos hTS) Ioo_subset_Ico_self
  have hslab : Ico 0 S ×ˢ (univ : Set Vec3) ∈ 𝓝 (T, (0 : Vec3)) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod htime univ_mem
  have hsmooth : ContDiffAt ℝ ∞ (Function.uncurry v) (T, (0 : Vec3)) :=
    hv.smooth_velocity.contDiffAt hslab
  have hderiv : ContinuousAt (fun t => fderiv ℝ (v t) (0 : Vec3)) T :=
    (hsmooth.fderiv (g := fun _ => (0 : Vec3)) (m := 0) contDiffAt_const (by simp)).continuousAt
  have hcurl : ContinuousAt (fun t => ‖curl (v t) 0‖) T :=
    (continuous_curlOfDerivative.continuousAt.comp hderiv).norm
  have hfinite : Tendsto (fun t => ‖curl (u t) 0‖) (𝓝[Ico 0 T] T)
      (𝓝 ‖curl (v T) 0‖) := by
    apply (hcurl.continuousWithinAt : ContinuousWithinAt _ (Ico 0 T) T).tendsto.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hagree t ht]
  let _ := terminalTime_neBot hu.time_pos
  exact (not_tendsto_atTop_of_tendsto_nhds hfinite) hblowup

end TorusEuler
