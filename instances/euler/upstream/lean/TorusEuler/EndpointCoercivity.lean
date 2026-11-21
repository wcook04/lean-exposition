import TorusEuler.EndpointEnergy
import TorusEuler.EndpointNorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic-form upper bound and terminal Poincaré give Lemma 4.1
    in displacement coordinates, with the sharper factor before using `T ≤ 1`. -/
theorem endpointDisplacementEnergy_coercive
    {T : ℝ} {H : ℝ → E →L[ℝ] E} {ξ dξ : ℝ → E}
    (hT : 0 ≤ T) (hξT : ξ T = 0)
    (hdξ : ContinuousOn dξ (Icc 0 T))
    (hξ : ∀ t ∈ Icc 0 T, HasDerivWithinAt ξ (dξ t) (Icc 0 T) t)
    (hH : ContinuousOn H (Icc 0 T))
    (hupper : ∀ t ∈ Icc 0 T, ∀ x : E, ⟪H t x, x⟫_ℝ ≤ ‖x‖ ^ 2) :
    (1 - T ^ 2 / 2) * (∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2 - ⟪H t (ξ t), ξ t⟫_ℝ := by
  have cξ : ContinuousOn ξ (Icc 0 T) := fun t ht => (hξ t ht).continuousWithinAt
  rw [← uIcc_of_le hT] at cξ hdξ hH
  have iH : IntervalIntegrable (fun t => ⟪H t (ξ t), ξ t⟫_ℝ) volume 0 T :=
    ((hH.clm_apply cξ).inner cξ).intervalIntegrable
  have idξ : IntervalIntegrable (fun t => ‖dξ t‖ ^ 2) volume 0 T :=
    (hdξ.norm.pow 2).intervalIntegrable
  have iξ : IntervalIntegrable (fun t => ‖ξ t‖ ^ 2) volume 0 T :=
    (cξ.norm.pow 2).intervalIntegrable
  have ibound := intervalIntegral.integral_mono_on hT iH iξ (fun t ht => hupper t ht (ξ t))
  have hp := terminal_poincare_integral hT hξT (by rwa [uIcc_of_le hT] at hdξ) hξ
  rw [intervalIntegral.integral_sub idξ iH, sub_mul, one_mul]
  exact sub_le_sub_left (ibound.trans hp) _

/-- The one-label `C¹` version of the estimate (4.8) in Lemma 4.1. -/
theorem endpointLabelEnergy_coercive {T : ℝ} {F M Mt : ℝ → E →L[ℝ] E} {z v : ℝ → E}
    (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (hM : ∀ t ∈ Icc 0 T, HasDerivWithinAt M (Mt t) (Icc 0 T) t)
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z (v t) (Icc 0 T) t)
    (hMt : ContinuousOn Mt (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hz0 : z 0 = 0) (hzT : z T = 0)
    (hupper : ∀ t ∈ Icc 0 T, ∀ x : E, ⟪endpointHessian (M t) (Mt t) x, x⟫_ℝ ≤ ‖x‖ ^ 2) :
    (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..T, ‖endpointDisplacementDerivative (F t) (M t) (z t) (v t)‖ ^ 2)
      ≤ ∫ t in (0 : ℝ)..T, endpointLabelEnergy (F t) (M t) (z t) (v t) := by
  let ξ := fun t => F t (z t)
  let dξ := fun t => endpointDisplacementDerivative (F t) (M t) (z t) (v t)
  have cF : ContinuousOn F (Icc 0 T) := fun t ht => (hF t ht).continuousWithinAt
  have cM : ContinuousOn M (Icc 0 T) := fun t ht => (hM t ht).continuousWithinAt
  have cz : ContinuousOn z (Icc 0 T) := fun t ht => (hz t ht).continuousWithinAt
  have cdξ : ContinuousOn dξ (Icc 0 T) := (cM.clm_apply (cF.clm_apply cz)).add (cF.clm_apply hv)
  have cH : ContinuousOn (fun t => endpointHessian (M t) (Mt t)) (Icc 0 T) :=
    (hMt.add (cM.clm_comp cM)).neg
  have hξ : ∀ t ∈ Icc 0 T, HasDerivWithinAt ξ (dξ t) (Icc 0 T) t :=
    fun t ht => hasDerivWithinAt_endpointDisplacement (hF t ht) (hz t ht)
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hT (fun t => sq_nonneg ‖dξ t‖)
  have hcoef : (1 / 2 : ℝ) ≤ 1 - T ^ 2 / 2 := by
    nlinarith [mul_nonneg hT (sub_nonneg.mpr hT1)]
  calc
    (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2)
        ≤ (1 - T ^ 2 / 2) * (∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hcoef hnonneg
    _ ≤ ∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2 - ⟪endpointHessian (M t) (Mt t) (ξ t), ξ t⟫_ℝ :=
      endpointDisplacementEnergy_coercive hT (by simp [ξ, hzT]) cdξ hξ cH hupper
    _ = ∫ t in (0 : ℝ)..T, endpointLabelEnergy (F t) (M t) (z t) (v t) :=
      (integral_endpointLabelEnergy_eq hT hF hM hz hMt hv hz0 hzT).symm

/-- The one-label coercivity constant used at the start of Theorem 4.2,
    for continuously differentiable displacement paths. -/
theorem endpointLabelEnergy_coercive_velocity {T D L : ℝ}
    {F G M Mt : ℝ → E →L[ℝ] E} {z v : ℝ → E}
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (hM : ∀ t ∈ Icc 0 T, HasDerivWithinAt M (Mt t) (Icc 0 T) t)
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z (v t) (Icc 0 T) t)
    (hMt : ContinuousOn Mt (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hz0 : z 0 = 0) (hzT : z T = 0)
    (hGF : ∀ t ∈ Icc 0 T, (G t).comp (F t) = ContinuousLinearMap.id ℝ E)
    (hGbound : ∀ t ∈ Icc 0 T, ‖G t‖ ≤ D) (hMbound : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ L)
    (hupper : ∀ t ∈ Icc 0 T, ∀ x : E, ⟪endpointHessian (M t) (Mt t) x, x⟫_ℝ ≤ ‖x‖ ^ 2) :
    (1 / (2 * D ^ 2 * (1 + L) ^ 2)) * (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T, endpointLabelEnergy (F t) (M t) (z t) (v t) := by
  let dξ := fun t => endpointDisplacementDerivative (F t) (M t) (z t) (v t)
  have cM : ContinuousOn M (Icc 0 T) := fun t ht => (hM t ht).continuousWithinAt
  have hnorm := integral_endpointLabelVelocity_norm_sq_le hT hT1 (zero_le_one.trans hD) hL
    hF hz cM hv hzT hGF hGbound hMbound
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hdenom : 0 < 2 * D ^ 2 * (1 + L) ^ 2 := by positivity
  have hscaled : (1 / (2 * D ^ 2 * (1 + L) ^ 2)) * (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) ≤
      (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hdenom]
    calc
      (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) ≤
          D ^ 2 * (1 + L) ^ 2 * (∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2) := hnorm
      _ = _ := by ring
  exact hscaled.trans (endpointLabelEnergy_coercive hT hT1 hF hM hz hMt hv hz0 hzT hupper)

end TorusEuler
