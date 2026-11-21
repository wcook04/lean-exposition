import Breakdown.CellReduction.ReductionStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem columnSquares_nonneg (A : Space →L[ℝ] Space) : 0 ≤ matSq A := by
  unfold matSq
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem stationaryEnergy_const_nonneg {w₀ : ℝ} (hw₀ : 0 ≤ w₀) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    0 ≤ stationaryEnergy (fun _ => w₀) G H := by
  unfold stationaryEnergy
  exact add_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun y => mul_nonneg hw₀ (columnSquares_nonneg (G y)))

theorem shiftGradCoeff_cubic_nonneg {w₀ : ℝ} (hw₀ : 0 < w₀) : 0 ≤ shiftGradCoeff w₀ true := by
  simp only [shiftGradCoeff, if_true]
  have := Real.sqrt_pos.2 hw₀
  positivity

end Internal

theorem frozenFormBridge_of (hFI : FrozenIntegrandHolds) (hStrain : StrainTermHolds)
    (hShiftGrad : ShiftGradTermHolds) (hPeriodGlue : PeriodGlueHolds) : FrozenFormBridgeHolds := by
  intro k d r h hc q hq σ w G H hw
  obtain ⟨HW, D, hs⟩ := h.model_state q hq
  have hw0 : 0 < d.weight := h.weight_pos
  rw [h.weightFn_const]
  have hWs : ContDiff ℝ 1 (d.model q σ) := hs.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hdec := hs.decay σ
  have hD : 0 ≤ D := by
    have h0 := (hdec 0).1
    rw [norm_zero, add_zero, div_one] at h0
    exact (norm_nonneg _).trans h0
  have hWb : ∀ y, ‖d.model q σ y‖ ≤ D := fun y =>
    (hdec y).1.trans (div_le_self hD (by linarith [norm_nonneg y]))
  have hWdb : ∀ y, ‖fderiv ℝ (d.model q σ) y‖ ≤ D := fun y =>
    (hdec y).2.1.trans (div_le_self hD (one_le_pow₀ (by linarith [norm_nonneg y])))
  obtain ⟨hI1, hI2⟩ := hFI d.symmetries D (d.model q σ) w G H hWs (fun y => (hdec y).1)
    (fun y => (hdec y).2.1) hw
  have hM := hStrain d.symmetries d.weight r.strainLower D (d.model q σ) w G H hw0
    hc.strainLower_nonneg hWs hWb hWdb (hs.divergence_free σ) (hc.strain q hq σ) hw
  have hmeas : StronglyMeasurable (fderiv ℝ (d.model q σ)) :=
    (hWs.continuous_fderiv one_ne_zero).stronglyMeasurable
  have hpgb : PieceGradBound true (fderiv ℝ (d.model q σ)) r.gradCubic := by
    simp only [PieceGradBound, if_true]
    exact hc.grad_cubic q hq σ
  have hF := hShiftGrad d.symmetries d.weight r.gradCubic true w (fderiv ℝ (d.model q σ)) G H hw0
    hc.gradCubic_nonneg hw hmeas hpgb
  set E := stationaryEnergy (fun _ => d.weight) G H with hEdef
  have hE : 0 ≤ E := Internal.stationaryEnergy_const_nonneg hw0.le G H
  have hB : 0 ≤ shiftGradCoeff d.weight true * r.gradCubic * E :=
    mul_nonneg (mul_nonneg (Internal.shiftGradCoeff_cubic_nonneg hw0) hc.gradCubic_nonneg) hE
  have hP := hPeriodGlue.2.2.1 (fun y => fderiv ℝ (d.model q σ) y (w y)) (fun y => -secondDerivTrace (H y))
    (shiftGradCoeff d.weight true * r.gradCubic * E) hB (by simpa only [norm_neg] using hF)
  have hP' := (abs_le.mp hP).1
  have hsplit : (∫ y, inner ℝ (G y (d.model q σ y) + fderiv ℝ (d.model q σ) y (w y))
      (-secondDerivTrace (H y))) = (∫ y, inner ℝ (G y (d.model q σ y)) (-secondDerivTrace (H y)))
        + ∫ y, inner ℝ (fderiv ℝ (d.model q σ) y (w y)) (-secondDerivTrace (H y)) := by
    simp_rw [inner_add_left]
    exact integral_add hI1 hI2
  have hA : 0 ≤ ∫ y, ‖secondDerivTrace (H y)‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hFr : 0 ≤ ∫ y, matSq (G y) := integral_nonneg fun y => Internal.columnSquares_nonneg (G y)
  have hcoef : r.strainLower / d.weight + shiftGradCoeff d.weight true * r.gradCubic ≤
      d.modelFormBound := by
    have hs3 := hc.sum_le
    have heq : shiftGradCoeff d.weight true * r.gradCubic =
        2 / Real.sqrt 3 * r.gradCubic / (2 * Real.sqrt d.weight) := by
      simp only [shiftGradCoeff, if_true]
      ring
    rw [heq]
    exact hs3
  have hkey := mul_le_mul_of_nonneg_right hcoef hE
  unfold frozenForm
  rw [hsplit]
  nlinarith [hkey, hM, hP', hA, hFr]

end CertReduction

end Breakdown
