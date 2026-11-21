import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem strainCoord_eq_inner_unit (x : Space) (j : Fin 3) : x j = inner ℝ (unitVector j) x := by
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem strainAdjointColumnSquareSum (A : Space →L[ℝ] Space) :
    ∑ i : Fin 3, ‖ContinuousLinearMap.adjoint A (unitVector i)‖ ^ 2 = matSq A := by
  have key : ∀ i j : Fin 3,
      (ContinuousLinearMap.adjoint A (unitVector i)) j = (A (unitVector j)) i := by
    intro i j
    rw [strainCoord_eq_inner_unit, ContinuousLinearMap.adjoint_inner_right, real_inner_comm,
      ← strainCoord_eq_inner_unit]
  unfold matSq
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, key]
  exact Finset.sum_comm

theorem strainColumnSum_lower (A G : Space →L[ℝ] Space) (S : ℝ)
    (h : ∀ u : Space, -S * ‖u‖ ^ 2 ≤ inner ℝ (A u) u) :
    -S * matSq G ≤ ∑ i : Fin 3, inner ℝ (A (ContinuousLinearMap.adjoint G (unitVector i)))
        (ContinuousLinearMap.adjoint G (unitVector i)) := by
  rw [← strainAdjointColumnSquareSum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => h _)

theorem strainColumnSquareSum_continuous : Continuous (fun A : Space →L[ℝ] Space => matSq A) := by
  unfold matSq
  refine continuous_finsetSum _ (fun i _ => ?_)
  have hc : Continuous (fun A : Space →L[ℝ] Space => A (unitVector i)) := by
    exact continuous_id.clm_apply continuous_const
  exact (continuous_norm.comp hc).pow 2

theorem strainColumnSquareSum_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end Internal

theorem strainTerm_of (hconv : ConvectionIdentityHolds) : StrainTermHolds := by
  intro Γ w₀ S C W w G H hw hS hW hWb hWd hdiv hstrain hprof
  rw [hconv Γ W w G H C hW hWb hWd hdiv hprof]
  have hE1 : 0 ≤ ∫ y, ‖secondDerivTrace (H y)‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hE2 : 0 ≤ ∫ y, matSq (G y) :=
    integral_nonneg (fun _ => Internal.strainColumnSquareSum_nonneg _)
  have henergy : stationaryEnergy (fun _ => w₀) G H =
      (∫ y, ‖secondDerivTrace (H y)‖ ^ 2) + w₀ * (∫ y, matSq (G y)) := by
    unfold stationaryEnergy
    rw [integral_const_mul]
  have hcancel : S / w₀ * (w₀ * (∫ y, matSq (G y))) = S * (∫ y, matSq (G y)) := by
    calc S / w₀ * (w₀ * (∫ y, matSq (G y))) = S * (∫ y, matSq (G y)) * (w₀ / w₀) := by ring
      _ = S * (∫ y, matSq (G y)) := by rw [div_self hw.ne', mul_one]
  have hfirst : 0 ≤ S / w₀ * (∫ y, ‖secondDerivTrace (H y)‖ ^ 2) :=
    mul_nonneg (div_nonneg hS hw.le) hE1
  have hkey : -(S / w₀) * stationaryEnergy (fun _ => w₀) G H ≤ -S * (∫ y, matSq (G y)) := by
    rw [henergy, neg_mul, mul_add, hcancel]
    linarith
  by_cases hint : Integrable (fun y => ∑ i : Fin 3,
      inner ℝ (fderiv ℝ W y (ContinuousLinearMap.adjoint (G y) (unitVector i)))
        (ContinuousLinearMap.adjoint (G y) (unitVector i)))
  · have hGmeas : AEStronglyMeasurable G volume :=
      hprof.weak_gradient.2.1.aestronglyMeasurable
    have hfrob : Integrable (fun y => matSq (G y)) := by
      refine ⟨Internal.strainColumnSquareSum_continuous.comp_aestronglyMeasurable hGmeas, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall (fun y => Internal.strainColumnSquareSum_nonneg (G y)))]
      exact hprof.gradient_finite
    have hmono := integral_mono (hfrob.const_mul (-S)) hint
      (fun y => Internal.strainColumnSum_lower (fderiv ℝ W y) (G y) S (hstrain y))
    rw [integral_const_mul] at hmono
    linarith
  · rw [integral_undef hint]
    have hnn : 0 ≤ S / w₀ * stationaryEnergy (fun _ => w₀) G H := by
      rw [henergy]
      exact mul_nonneg (div_nonneg hS hw.le) (add_nonneg hE1 (mul_nonneg hw.le hE2))
    linarith

end CertReduction

end Breakdown
