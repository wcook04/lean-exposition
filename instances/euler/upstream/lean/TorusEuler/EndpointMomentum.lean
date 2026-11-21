import TorusEuler.EndpointKinetic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open ContinuousLinearMap Set MeasureTheory
open scoped InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private theorem endpoint_integral_hasDerivWithinAt {T t : ℝ} {f : ℝ → E}
    (ht : t ∈ Icc 0 T) (hf : ContinuousOn f (Icc 0 T)) :
    HasDerivWithinAt (fun r => ∫ s in (0 : ℝ)..r, f s) (f t) (Icc 0 T) t := by
  let _ : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.2 (ht.1.trans ht.2)
  exact intervalIntegral.integral_hasDerivWithinAt_right
    (hf.mono (uIcc_subset_Icc h0 ht)).intervalIntegrable
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)

/-- Differentiate (4.9) for the force source `-∫g`. Here `P` is the label gradient
in the integrated equation and `Q` is the gradient of the strong pressure. -/
theorem strongLabelMomentum_of_integrated {T t : ℝ}
    {F M : ℝ → E →L[ℝ] E} {v g P : ℝ → E} {dv c Q : E}
    (hT : 0 < T) (ht : t ∈ Icc 0 T)
    (hF : HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (hv : HasDerivWithinAt v dv (Icc 0 T) t)
    (hP : HasDerivWithinAt P (-Q) (Icc 0 T) t)
    (hΩ : ContinuousOn (fun r => vorticityForm (F r) (M r) (v r)) (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T))
    (hEq : ∀ r ∈ Icc 0 T, kineticForm (F r) (v r) -
      (∫ s in (0 : ℝ)..r, vorticityForm (F s) (M s) (v s)) -
      (∫ s in (0 : ℝ)..r, g s) = c + P r) :
    kineticForm (F t) dv + Q = g t -
      (2 : ℝ) • (F t).adjoint (M t (F t (v t))) := by
  have hL := (((hasDerivWithinAt_kineticForm hF).clm_apply hv).sub
    (endpoint_integral_hasDerivWithinAt ht hΩ)).sub (endpoint_integral_hasDerivWithinAt ht hg)
  have hR := (hP.const_add c).congr hEq (hEq t ht)
  have hdiff := uniqueDiffOn_Icc hT t ht
  have h := (hL.derivWithin hdiff).symm.trans (hR.derivWithin hdiff)
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply] at h
  have h' := congrArg (fun x : E => x + (g t - (2 : ℝ) •
    (F t).adjoint (M t (F t (v t)))) + Q) h
  have hr : -Q + (g t - (2 : ℝ) • (F t).adjoint (M t (F t (v t)))) + Q =
      g t - (2 : ℝ) • (F t).adjoint (M t (F t (v t))) := by abel
  rw [hr] at h'
  convert h' using 1; abel

/-- A covector gradient pulls back by the adjoint of the label derivative. -/
theorem hasGradientAt_endpointPressurePullback {X : E → E} {q : E → ℝ}
    {a gradq : E} {F : E →L[ℝ] E} (hX : HasFDerivAt X F a)
    (hq : HasGradientAt q gradq (X a)) :
    HasGradientAt (q ∘ X) (F.adjoint gradq) a := by
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt _ (innerSL ℝ (F.adjoint gradq)) a
  rw [← innerSL_apply_comp]
  exact hq.hasFDerivAt.comp a hX

/-- A right inverse of the deformation allows recovery of the Eulerian momentum from
its pulled-back equation. `dB` differentiates `B = Fv` at fixed label. -/
theorem eulerianMomentum_of_strongLabelMomentum {F M : ℝ → E →L[ℝ] E}
    {v : ℝ → E} {I : Set ℝ} {t : ℝ} {G : E →L[ℝ] E} {dv f gradq : E}
    (hFG : (F t).comp G = ContinuousLinearMap.id ℝ E)
    (hF : HasDerivWithinAt F ((M t).comp (F t)) I t)
    (hv : HasDerivWithinAt v dv I t)
    (hEq : kineticForm (F t) dv + (F t).adjoint gradq =
        (F t).adjoint f - (2 : ℝ) • (F t).adjoint (M t (F t (v t)))) :
    ∃ dB, HasDerivWithinAt (fun r => F r (v r)) dB I t ∧
      dB + M t (F t (v t)) + gradq = f := by
  refine ⟨M t (F t (v t)) + F t dv, hF.clm_apply hv, ?_⟩
  have hAdj : G.adjoint.comp (F t).adjoint = ContinuousLinearMap.id ℝ E := by
    rw [← ContinuousLinearMap.adjoint_comp, hFG, ContinuousLinearMap.adjoint_id]
  have hInv : Function.LeftInverse G.adjoint (F t).adjoint := by
    intro y
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      DFunLike.congr_fun hAdj y
  apply hInv.injective
  simp only [map_add, kineticForm, ContinuousLinearMap.comp_apply] at *
  rw [two_smul] at hEq
  have h' := congrArg (fun x : E => x + ((F t).adjoint (M t (F t (v t))) +
    (F t).adjoint (M t (F t (v t))))) hEq
  convert h' using 1 <;> abel

end TorusEuler
