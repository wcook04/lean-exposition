import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

open Filter MeasureTheory Set
open scoped InnerProductSpace Topology

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The operator in (4.1), which can be nonsymmetric for an approximate parent. -/
def endpointHessian (M Mt : E →L[ℝ] E) : E →L[ℝ] E :=
  -(Mt + M.comp M)

noncomputable def endpointLabelEnergy (F M : E →L[ℝ] E) (z v : E) : ℝ :=
  ⟪F.adjoint (F v), v⟫_ℝ +
    ⟪F.adjoint ((M.adjoint - M) (F v)), z⟫_ℝ

def endpointDisplacementDerivative (F M : E →L[ℝ] E) (z v : E) : E :=
  M (F z) + F v

noncomputable def endpointBoundaryDerivative (M Mt : E →L[ℝ] E) (ξ dξ : E) : ℝ :=
  ⟪ξ, Mt ξ + M dξ⟫_ℝ + ⟪dξ, M ξ⟫_ℝ

omit [CompleteSpace E] in
/-- The product rule in (4.4) for the displacement from label coordinates. -/
theorem hasDerivWithinAt_endpointDisplacement
    {F M : ℝ → E →L[ℝ] E} {z v : ℝ → E} {s : Set ℝ} {t : ℝ}
    (hF : HasDerivWithinAt F ((M t).comp (F t)) s t)
    (hz : HasDerivWithinAt z (v t) s t) :
    HasDerivWithinAt (fun r => F r (z r))
      (endpointDisplacementDerivative (F t) (M t) (z t) (v t)) s t := by
  simpa only [endpointDisplacementDerivative, ContinuousLinearMap.comp_apply] using hF.clm_apply hz

/-- The pointwise algebra in §4.2, prior to integrating the boundary derivative. -/
theorem endpointLabelEnergy_eq (F M Mt : E →L[ℝ] E) (z v : E) :
    let ξ := F z
    let dξ := endpointDisplacementDerivative F M z v
    endpointLabelEnergy F M z v =
      ‖dξ‖ ^ 2 - ⟪endpointHessian M Mt ξ, ξ⟫_ℝ - endpointBoundaryDerivative M Mt ξ dξ := by
  simp only [endpointLabelEnergy, endpointHessian, endpointDisplacementDerivative,
    endpointBoundaryDerivative, ContinuousLinearMap.comp_apply, sub_apply, neg_apply, add_apply,
    ContinuousLinearMap.adjoint_inner_left, norm_add_sq_real, inner_add_left, inner_add_right,
    inner_sub_left, inner_neg_left, map_add]
  rw [real_inner_self_eq_norm_sq (F v), real_inner_self_eq_norm_sq (M (F z)),
    real_inner_comm (F z) (Mt (F z)), real_inner_comm (F z) (M (M (F z))),
    real_inner_comm (M (F z)) (F v), real_inner_comm (M (F v)) (F z)]
  ring

/-- Integrated identity (4.7) at one label for paths with continuous derivatives. -/
theorem integral_endpointLabelEnergy_eq {T : ℝ} {F M Mt : ℝ → E →L[ℝ] E} {z v : ℝ → E}
    (hT : 0 ≤ T)
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (hM : ∀ t ∈ Icc 0 T, HasDerivWithinAt M (Mt t) (Icc 0 T) t)
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z (v t) (Icc 0 T) t)
    (hMt : ContinuousOn Mt (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hz0 : z 0 = 0) (hzT : z T = 0) :
    let ξ := fun t => F t (z t)
    let dξ := fun t => endpointDisplacementDerivative (F t) (M t) (z t) (v t)
    (∫ t in (0 : ℝ)..T, endpointLabelEnergy (F t) (M t) (z t) (v t)) =
      ∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2 - ⟪endpointHessian (M t) (Mt t) (ξ t), ξ t⟫_ℝ := by
  let ξ := fun t => F t (z t)
  let dξ := fun t => endpointDisplacementDerivative (F t) (M t) (z t) (v t)
  let boundary := fun t => endpointBoundaryDerivative (M t) (Mt t) (ξ t) (dξ t)
  have cF : ContinuousOn F (Icc 0 T) := fun t ht => (hF t ht).continuousWithinAt
  have cM : ContinuousOn M (Icc 0 T) := fun t ht => (hM t ht).continuousWithinAt
  have cz : ContinuousOn z (Icc 0 T) := fun t ht => (hz t ht).continuousWithinAt
  have cξ : ContinuousOn ξ (Icc 0 T) := cF.clm_apply cz
  have cdξ : ContinuousOn dξ (Icc 0 T) := (cM.clm_apply cξ).add (cF.clm_apply hv)
  have cb : ContinuousOn boundary (Icc 0 T) :=
    (cξ.inner ((hMt.clm_apply cξ).add (cM.clm_apply cdξ))).add (cdξ.inner (cM.clm_apply cξ))
  have cH : ContinuousOn (fun t => endpointHessian (M t) (Mt t)) (Icc 0 T) :=
    (hMt.add (cM.clm_comp cM)).neg
  have cenergy : ContinuousOn (fun t => ‖dξ t‖ ^ 2 -
      ⟪endpointHessian (M t) (Mt t) (ξ t), ξ t⟫_ℝ) (Icc 0 T) :=
    (cdξ.norm.pow 2).sub ((cH.clm_apply cξ).inner cξ)
  have ib : IntervalIntegrable boundary volume 0 T := (by simpa only [uIcc_of_le hT] using cb :
    ContinuousOn boundary (uIcc 0 T)).intervalIntegrable
  have ie : IntervalIntegrable (fun t => ‖dξ t‖ ^ 2 -
      ⟪endpointHessian (M t) (Mt t) (ξ t), ξ t⟫_ℝ) volume 0 T :=
    (by simpa only [uIcc_of_le hT] using cenergy :
    ContinuousOn (fun t => ‖dξ t‖ ^ 2 -
      ⟪endpointHessian (M t) (Mt t) (ξ t), ξ t⟫_ℝ) (uIcc 0 T)).intervalIntegrable
  have hb : (∫ t in (0 : ℝ)..T, boundary t) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
      (cξ.inner (cM.clm_apply cξ)) (fun t ht => ?_) ib
    · simpa [ξ, hz0, hzT] using h
    · have hs : Icc 0 T ∈ 𝓝 t :=
        mem_of_superset (isOpen_Ioo.mem_nhds ht) Ioo_subset_Icc_self
      have hd := hasDerivWithinAt_endpointDisplacement
        (hF t (Ioo_subset_Icc_self ht)) (hz t (Ioo_subset_Icc_self ht))
      exact (hd.inner ℝ ((hM t (Ioo_subset_Icc_self ht)).clm_apply hd)).hasDerivAt hs
  change _ = ∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2 - ⟪endpointHessian (M t) (Mt t) (ξ t), ξ t⟫_ℝ
  calc
    (∫ t in (0 : ℝ)..T, endpointLabelEnergy (F t) (M t) (z t) (v t)) =
        ∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2 -
          ⟪endpointHessian (M t) (Mt t) (ξ t), ξ t⟫_ℝ - boundary t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact endpointLabelEnergy_eq (F t) (M t) (Mt t) (z t) (v t)
    _ = _ := by rw [intervalIntegral.integral_sub ie ib, hb, sub_zero]

end TorusEuler
