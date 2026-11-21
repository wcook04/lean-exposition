import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

theorem columnSquareSum_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem apply_norm_sq_le_columnSquareSum (A : Space →L[ℝ] Space) (x : Space) :
    ‖A x‖ ^ 2 ≤ matSq A * ‖x‖ ^ 2 := by
  have hx : x = ∑ i : Fin 3, x i • unitVector i := by
    have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
    simpa [unitVector, EuclideanSpace.basisFun_apply] using h.symm
  have hAx : A x = ∑ i : Fin 3, x i • A (unitVector i) := by
    conv_lhs => rw [hx]
    simp [map_sum, map_smul]
  have h1 : ‖A x‖ ≤ ∑ i : Fin 3, |x i| * ‖A (unitVector i)‖ := by
    rw [hAx]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : (∑ i : Fin 3, |x i| * ‖A (unitVector i)‖) ^ 2 ≤
      (∑ i : Fin 3, |x i| ^ 2) * (∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ‖x‖ ^ 2 = ∑ i : Fin 3, |x i| ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs]
  have h0 : 0 ≤ ‖A x‖ := norm_nonneg _
  calc ‖A x‖ ^ 2 ≤ (∑ i : Fin 3, |x i| * ‖A (unitVector i)‖) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ ≤ (∑ i : Fin 3, |x i| ^ 2) * (∑ i : Fin 3, ‖A (unitVector i)‖ ^ 2) := h2
    _ = matSq A * ‖x‖ ^ 2 := by rw [h3, matSq, mul_comm]

theorem operatorSquareBound : OperatorSquareBoundHolds := by
  intro A
  have hf := columnSquareSum_nonneg A
  have hb : ‖A‖ ≤ Real.sqrt (matSq A) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun x => ?_)
    have h := apply_norm_sq_le_columnSquareSum A x
    have hr : Real.sqrt (‖A x‖ ^ 2) ≤ Real.sqrt (matSq A * ‖x‖ ^ 2) := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hf, Real.sqrt_sq (norm_nonneg _)] at hr
  calc ‖A‖ ^ 2 ≤ Real.sqrt (matSq A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = matSq A := Real.sq_sqrt hf

theorem strainOfSymmetricPart : StrainOfSymmetricPartHolds := by
  intro A S hS u
  set B : Space →L[ℝ] Space := (1 / 2 : ℝ) • (A + ContinuousLinearMap.adjoint A) with hBdef
  have hadj : inner ℝ ((ContinuousLinearMap.adjoint A) u) u = inner ℝ (A u) u := by
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  have hB : inner ℝ (B u) u = inner ℝ (A u) u := by
    rw [show B u = (1 / 2 : ℝ) • (A u + (ContinuousLinearMap.adjoint A) u) from rfl, inner_smul_left,
      inner_add_left, hadj]
    simp only [RCLike.conj_to_real]
    ring
  have habs : |inner ℝ (B u) u| ≤ S * ‖u‖ ^ 2 := by
    calc |inner ℝ (B u) u| ≤ ‖B u‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖B‖ * ‖u‖) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (S * ‖u‖) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS (norm_nonneg _)) (norm_nonneg _)
      _ = S * ‖u‖ ^ 2 := by ring
  have := neg_le_of_abs_le habs
  rw [hB] at this
  linarith

theorem matrixFacts : MatrixFactsHolds :=
  ⟨operatorSquareBound, strainOfSymmetricPart⟩

end CertReduction

end Breakdown
