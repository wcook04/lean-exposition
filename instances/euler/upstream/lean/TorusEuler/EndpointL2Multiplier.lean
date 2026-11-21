import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory

namespace TorusEuler

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def endpointOperatorEval : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.apply ℝ F).flip

/-- An essentially bounded strongly measurable operator field multiplies `L²` representatives
pointwise. -/
theorem memLp_endpointL2Mul (A : α → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hbound : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) {v : α → E} (hv : MemLp v 2 μ) :
    MemLp (fun t => A t (v t)) 2 μ :=
  (endpointOperatorEval (E := E) (F := F)).memLp_of_bilin 2
    (memLp_top_of_bound hA C hbound) hv

/-- Pointwise action of an essentially bounded strongly measurable operator field on `L²`. -/
noncomputable def endpointL2Multiplier (A : α → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hbound : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) : Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  (endpointOperatorEval (E := E) (F := F)).holderL μ ⊤ 2 2
    ((memLp_top_of_bound hA C hbound).toLp A)

theorem endpointL2Multiplier_apply_ae (A : α → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hbound : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) (v : Lp E 2 μ) :
    ⇑(endpointL2Multiplier A hA hbound v) =ᵐ[μ] fun t => A t (v t) := by
  let hA_top := memLp_top_of_bound hA C hbound
  have h := (endpointOperatorEval (E := E) (F := F)).coeFn_holder (r := 2) (hA_top.toLp A) v
  filter_upwards [h, hA_top.coeFn_toLp] with t ht hAt
  exact ht.trans (congrArg (fun B : E →L[ℝ] F => B (v t)) hAt)

theorem endpointL2Multiplier_apply_toLp (A : α → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hbound : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) {v : α → E} (hv : MemLp v 2 μ) :
    endpointL2Multiplier A hA hbound (hv.toLp v) =
      (memLp_endpointL2Mul A hA hbound hv).toLp (fun t => A t (v t)) := by
  apply Lp.ext
  filter_upwards [endpointL2Multiplier_apply_ae A hA hbound (hv.toLp v), hv.coeFn_toLp,
    (memLp_endpointL2Mul A hA hbound hv).coeFn_toLp] with t ht hvt hmul
  exact ht.trans ((congrArg (A t) hvt).trans hmul.symm)

theorem norm_endpointL2Multiplier_le (A : α → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hbound : ∀ᵐ t ∂μ, ‖A t‖ ≤ C) (hC : 0 ≤ C) :
    ‖endpointL2Multiplier A hA hbound‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [endpointL2Multiplier_apply_ae A hA hbound v, hbound] with t ht hAt
  rw [ht]
  exact ((A t).le_opNorm (v t)).trans (mul_le_mul_of_nonneg_right hAt (norm_nonneg _))

end TorusEuler
