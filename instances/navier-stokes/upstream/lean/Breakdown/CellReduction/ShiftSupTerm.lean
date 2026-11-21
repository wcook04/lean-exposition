import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace ShiftSupInternal

theorem product_le_energy {a b w₀ : ℝ} (hw : 0 < w₀) :
    a * b ≤ (b ^ 2 + w₀ * a ^ 2) / (2 * Real.sqrt w₀) := by
  have hs : 0 < Real.sqrt w₀ := Real.sqrt_pos.2 hw
  have h2 : Real.sqrt w₀ ^ 2 = w₀ := Real.sq_sqrt hw.le
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt w₀ * a - b)]

theorem columnSum_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem columnSum_continuous : Continuous (fun A : Space →L[ℝ] Space => matSq A) := by
  unfold matSq
  fun_prop

theorem trace_eq (A : Space →L[ℝ] Space →L[ℝ] Space) :
    secondDerivTrace A = ∑ j : Fin 3, (A.flip (unitVector j)) (unitVector j) := by
  simp [secondDerivTrace, ContinuousLinearMap.flip_apply]

theorem pointwise_le {w₀ s : ℝ} (hw : 0 < w₀) (hs : 0 ≤ s) (h0 : OperatorSquareBoundHolds)
    (A : Space →L[ℝ] Space) (x t : Space) (hx : ‖x‖ ≤ s) :
    ‖A x‖ * ‖t‖ ≤ s / (2 * Real.sqrt w₀) * (‖t‖ ^ 2 + w₀ * matSq A) := by
  have hA : ‖A‖ ≤ Real.sqrt (matSq A) := Real.le_sqrt_of_sq_le (h0 A)
  have hF : Real.sqrt (matSq A) ^ 2 = matSq A := Real.sq_sqrt (columnSum_nonneg A)
  have h1 : ‖A x‖ ≤ Real.sqrt (matSq A) * s :=
    (A.le_opNorm x).trans (mul_le_mul hA hx (norm_nonneg _) (Real.sqrt_nonneg _))
  have h2 : Real.sqrt (matSq A) * ‖t‖ ≤ (‖t‖ ^ 2 + w₀ * matSq A) / (2 * Real.sqrt w₀) := by
    have := product_le_energy (a := Real.sqrt (matSq A)) (b := ‖t‖) hw
    rwa [hF] at this
  calc ‖A x‖ * ‖t‖ ≤ Real.sqrt (matSq A) * s * ‖t‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = s * (Real.sqrt (matSq A) * ‖t‖) := by ring
    _ ≤ s * ((‖t‖ ^ 2 + w₀ * matSq A) / (2 * Real.sqrt w₀)) := mul_le_mul_of_nonneg_left h2 hs
    _ = s / (2 * Real.sqrt w₀) * (‖t‖ ^ 2 + w₀ * matSq A) := by ring

end ShiftSupInternal

open ShiftSupInternal in
theorem shiftSupTerm_of (h0 : MatrixFactsHolds) : ShiftSupTermHolds := by
  intro Γ w₀ s w δ G H hw hs hP hδ
  have hGm : AEStronglyMeasurable G volume := hP.weak_gradient.2.1.aestronglyMeasurable
  have hHm : AEStronglyMeasurable (fun y => secondDerivTrace (H y)) volume := by
    simp_rw [trace_eq]
    refine Finset.aestronglyMeasurable_fun_sum
      (f := fun j y => ((H y).flip (unitVector j)) (unitVector j)) Finset.univ (fun j _ => ?_)
    have hj : AEStronglyMeasurable (fun y => (H y).flip (unitVector j)) volume :=
      (hP.weak_secondDeriv j).2.1.aestronglyMeasurable
    have h2 :=
      (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable hj
    exact h2
  have hT : Integrable (fun y => ‖secondDerivTrace (H y)‖ ^ 2) volume := by
    refine ⟨(hHm.norm.pow 2), ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => sq_nonneg _)]
    exact hP.sumSecondPartials_finite
  have hF : Integrable (fun y => matSq (G y)) volume := by
    refine ⟨columnSum_continuous.comp_aestronglyMeasurable hGm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => columnSum_nonneg _)]
    exact hP.gradient_finite
  have hsum : Integrable (fun y => s / (2 * Real.sqrt w₀) *
      (‖secondDerivTrace (H y)‖ ^ 2 + w₀ * matSq (G y))) volume :=
    (hT.add (hF.const_mul w₀)).const_mul _
  have hnn : 0 ≤ᵐ[volume] (fun y => s / (2 * Real.sqrt w₀) *
      (‖secondDerivTrace (H y)‖ ^ 2 + w₀ * matSq (G y))) :=
    ae_of_all _ fun y => mul_nonneg (by positivity)
      (add_nonneg (sq_nonneg _) (mul_nonneg hw.le (columnSum_nonneg _)))
  calc (∫⁻ y, ENNReal.ofReal (‖G y (δ y)‖ * ‖secondDerivTrace (H y)‖))
      ≤ ∫⁻ y, ENNReal.ofReal (s / (2 * Real.sqrt w₀) *
          (‖secondDerivTrace (H y)‖ ^ 2 + w₀ * matSq (G y))) :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal
          (pointwise_le hw hs h0.1 (G y) (δ y) (secondDerivTrace (H y)) (hδ y))
    _ = ENNReal.ofReal (∫ y, s / (2 * Real.sqrt w₀) *
          (‖secondDerivTrace (H y)‖ ^ 2 + w₀ * matSq (G y))) :=
        (ofReal_integral_eq_lintegral_ofReal hsum hnn).symm
    _ = ENNReal.ofReal (s / (2 * Real.sqrt w₀) * stationaryEnergy (fun _ => w₀) G H) := by
        rw [integral_const_mul, integral_add hT (hF.const_mul w₀)]
        rfl

end CertReduction

end Breakdown
