import TorusEuler.EndpointEnergy
import TorusEuler.TerminalPoincare
import Mathlib.Tactic.Linarith

open MeasureTheory Set

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

section NormedSpace

variable [NormedSpace ℝ E]

/-- The squared velocity estimate in (4.6) for a displacement that vanishes at the
terminal time. The constants bound the inverse deformation and the velocity gradient. -/
theorem integral_endpointVelocity_norm_sq_le
    {T D L : ℝ} {G M : ℝ → E →L[ℝ] E} {ξ dξ v : ℝ → E}
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hξT : ξ T = 0) (hdξ : ContinuousOn dξ (Icc 0 T))
    (hv : ContinuousOn v (Icc 0 T))
    (hξ : ∀ t ∈ Icc 0 T, HasDerivWithinAt ξ (dξ t) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, ‖G t‖ ≤ D)
    (hM : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ L)
    (hvelocity : ∀ t ∈ Icc 0 T, v t = G t (dξ t - M t (ξ t))) :
    (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) ≤
      D ^ 2 * (1 + L) ^ 2 * (∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2) := by
  have hpointwise (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖v t‖ ^ 2 ≤ (D ^ 2 * (1 + L)) * (‖dξ t‖ ^ 2 + L * ‖ξ t‖ ^ 2) := by
    have hnormM : ‖M t (ξ t)‖ ≤ L * ‖ξ t‖ :=
      ((M t).le_opNorm (ξ t)).trans (mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _))
    have hnorm : ‖v t‖ ≤ D * (‖dξ t‖ + L * ‖ξ t‖) := by
      rw [hvelocity t ht]
      calc
        ‖G t (dξ t - M t (ξ t))‖ ≤ ‖G t‖ * ‖dξ t - M t (ξ t)‖ := (G t).le_opNorm _
        _ ≤ D * ‖dξ t - M t (ξ t)‖ :=
          mul_le_mul_of_nonneg_right (hG t ht) (norm_nonneg _)
        _ ≤ D * (‖dξ t‖ + L * ‖ξ t‖) := mul_le_mul_of_nonneg_left
          ((norm_sub_le _ _).trans (add_le_add_right hnormM _)) hD
    have hsq : (‖dξ t‖ + L * ‖ξ t‖) ^ 2 ≤ (1 + L) * (‖dξ t‖ ^ 2 + L * ‖ξ t‖ ^ 2) := by
      nlinarith only [mul_nonneg hL (sq_nonneg (‖dξ t‖ - ‖ξ t‖))]
    calc
      ‖v t‖ ^ 2 ≤ (D * (‖dξ t‖ + L * ‖ξ t‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = D ^ 2 * (‖dξ t‖ + L * ‖ξ t‖) ^ 2 := mul_pow _ _ _
      _ ≤ (D ^ 2 * (1 + L)) * (‖dξ t‖ ^ 2 + L * ‖ξ t‖ ^ 2) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hsq (sq_nonneg D)
  have cξ : ContinuousOn ξ (Icc 0 T) := fun t ht => (hξ t ht).continuousWithinAt
  have iξ : IntervalIntegrable (fun t => ‖ξ t‖ ^ 2) volume 0 T :=
    (cξ.norm.pow 2).intervalIntegrable_of_Icc hT
  have idξ : IntervalIntegrable (fun t => ‖dξ t‖ ^ 2) volume 0 T :=
    (hdξ.norm.pow 2).intervalIntegrable_of_Icc hT
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hT (fun t => sq_nonneg ‖dξ t‖)
  have hcoef : T ^ 2 / 2 ≤ 1 := by
    nlinarith [mul_nonneg hT (sub_nonneg.mpr hT1)]
  have hξsq : (∫ t in (0 : ℝ)..T, ‖ξ t‖ ^ 2) ≤ ∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2 :=
    (terminal_poincare_integral hT hξT hdξ hξ).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hnonneg)
  calc
    (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) ≤
        ∫ t in (0 : ℝ)..T, (D ^ 2 * (1 + L)) * (‖dξ t‖ ^ 2 + L * ‖ξ t‖ ^ 2) :=
      intervalIntegral.integral_mono_on hT ((hv.norm.pow 2).intervalIntegrable_of_Icc hT)
        ((idξ.add (iξ.const_mul L)).const_mul _) hpointwise
    _ = (D ^ 2 * (1 + L)) *
        ((∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2) + L * (∫ t in (0 : ℝ)..T, ‖ξ t‖ ^ 2)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add idξ (iξ.const_mul L),
        intervalIntegral.integral_const_mul]
    _ ≤ (D ^ 2 * (1 + L)) * ((∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2) +
        L * (∫ t in (0 : ℝ)..T, ‖dξ t‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hξsq hL) _)
        (mul_nonneg (sq_nonneg D) (add_nonneg zero_le_one hL))
    _ = _ := by ring

end NormedSpace

/-- The one-label `C¹` version of (4.6), using the displacement derivative from (4.4). -/
theorem integral_endpointLabelVelocity_norm_sq_le [InnerProductSpace ℝ E]
    {T D L : ℝ} {F G M : ℝ → E →L[ℝ] E} {z v : ℝ → E}
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z (v t) (Icc 0 T) t)
    (cM : ContinuousOn M (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T)) (hzT : z T = 0)
    (hGF : ∀ t ∈ Icc 0 T, (G t).comp (F t) = ContinuousLinearMap.id ℝ E)
    (hG : ∀ t ∈ Icc 0 T, ‖G t‖ ≤ D)
    (hM : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ L) :
    (∫ t in (0 : ℝ)..T, ‖v t‖ ^ 2) ≤ D ^ 2 * (1 + L) ^ 2 *
      (∫ t in (0 : ℝ)..T, ‖endpointDisplacementDerivative (F t) (M t) (z t) (v t)‖ ^ 2) := by
  let ξ := fun t => F t (z t)
  let dξ := fun t => endpointDisplacementDerivative (F t) (M t) (z t) (v t)
  have cF : ContinuousOn F (Icc 0 T) := fun t ht => (hF t ht).continuousWithinAt
  have cz : ContinuousOn z (Icc 0 T) := fun t ht => (hz t ht).continuousWithinAt
  have cdξ : ContinuousOn dξ (Icc 0 T) := (cM.clm_apply (cF.clm_apply cz)).add (cF.clm_apply hv)
  have hξ : ∀ t ∈ Icc 0 T, HasDerivWithinAt ξ (dξ t) (Icc 0 T) t :=
    fun t ht => hasDerivWithinAt_endpointDisplacement (hF t ht) (hz t ht)
  refine integral_endpointVelocity_norm_sq_le hT hT1 hD hL
    (by simp [ξ, hzT]) cdξ hv hξ hG hM ?_
  intro t ht
  have hinv := DFunLike.congr_fun (hGF t ht) (v t)
  simpa only [ξ, dξ, endpointDisplacementDerivative, add_sub_cancel_left,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hinv.symm

end TorusEuler
