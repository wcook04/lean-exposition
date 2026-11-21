import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem slice_hasFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × E → F} (hf : ContDiff ℝ 1 f) (σ : ℝ) (y : E) :
    HasFDerivAt (fun x => f (σ, x)) ((fderiv ℝ f (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y :=
  ((hf.differentiable one_ne_zero) (σ, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)

theorem slice_fderiv_continuous {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × E → F} (hf : ContDiff ℝ 1 f) :
    Continuous (fun z : ℝ × E => fderiv ℝ (fun x => f (z.1, x)) z.2) := by
  have h : (fun z : ℝ × E => fderiv ℝ (fun x => f (z.1, x)) z.2) =
      fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext z
    exact (slice_hasFDerivAt hf z.1 z.2).fderiv
  rw [h]
  exact (hf.continuous_fderiv one_ne_zero).clm_comp continuous_const

end Internal

open Internal in
theorem smoothShiftPiecesHolds : SmoothShiftPiecesHolds := by
  intro k d r hB hC hG hV
  refine ⟨?_, ?_, ?_⟩
  · intro q hq σ y
    have hP : ∀ x, DifferentiableAt ℝ (d.profile q σ) x := fun x =>
      (slice_hasFDerivAt (hB.profile_smooth q hq) σ x).differentiableAt
    have hA : ∀ a x, DifferentiableAt ℝ (r.piece a q σ) x := fun a x =>
      (slice_hasFDerivAt (hC a q hq) σ x).differentiableAt
    have hM : d.model q σ = fun x => d.profile q σ x - ∑ a, r.piece a q σ x := by
      funext x
      rw [← hV q hq σ x, sub_sub_cancel]
    have hMd : DifferentiableAt ℝ (d.model q σ) y := by
      rw [hM]
      exact (hP y).sub (DifferentiableAt.fun_sum fun a _ => hA a y)
    have hD : (fun x => d.profile q σ x - d.model q σ x) = fun x => ∑ a, r.piece a q σ x :=
      funext (hV q hq σ)
    rw [← fderiv_fun_sub (hP y) hMd, hD, fderiv_fun_sum fun a _ => hA a y]
    exact Finset.sum_congr rfl fun a _ => (hG a q σ y).symm
  · intro a q hq
    exact (hC a q hq).continuous.stronglyMeasurable
  · intro a q hq
    have h : (fun z : ℝ × Space => r.pieceGrad a q z.1 z.2) =
        fun z => fderiv ℝ (fun x => (fun w : ℝ × Space => r.piece a q w.1 w.2) (z.1, x)) z.2 := by
      funext z
      exact hG a q z.1 z.2
    rw [h]
    exact (slice_fderiv_continuous (hC a q hq)).stronglyMeasurable

end CertReduction

end Breakdown
