import Breakdown.CellReduction.ReductionStatements
import Breakdown.CertCell.SixthPower

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem columnSquareSum_continuous : Continuous (fun G : Space →L[ℝ] Space => matSq G) := by
  unfold matSq
  exact continuous_finsetSum _ fun i _ =>
    ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.norm.pow 2)

theorem columnSquareSum_nonneg (G : Space →L[ℝ] Space) : 0 ≤ matSq G := by
  unfold matSq
  positivity

theorem sq_rpow_three_halves (a : ℝ) : (a ^ 2) ^ ((3 : ℝ) / 2) = |a| ^ 3 := by
  have h : a ^ 2 = |a| ^ (2 : ℝ) := by rw [Real.rpow_two, sq_abs]
  rw [h, ← Real.rpow_mul (abs_nonneg a), show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

theorem sq_rpow_three (a : ℝ) : (a ^ 2) ^ (3 : ℝ) = a ^ 6 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]

end Internal

open Internal in
theorem cubicWeightProductHolds : CubicWeightProductHolds := by
  intro w G A hwG hw6 hG hA
  have hwm : AEStronglyMeasurable w volume := hwG.1.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G volume := hwG.2.1.aestronglyMeasurable
  have hFm : AEStronglyMeasurable (fun y => matSq (G y)) volume :=
    columnSquareSum_continuous.comp_aestronglyMeasurable hGm
  have h6m : AEStronglyMeasurable (fun y => ‖w y‖ ^ 6) volume := hwm.norm.pow 6
  have hsix := sixthPowerGradientBound_four_thirds w G hwG hw6 hG
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => by positivity) h6m,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => columnSquareSum_nonneg (G y))
      hFm] at hsix
  have hI6 : (∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6)) ^ ((1 : ℝ) / 3) ≤
      ENNReal.ofReal (4 / 3) * (∫⁻ y, ENNReal.ofReal (matSq (G y))) := by
    rw [← ENNReal.ofReal_toReal hw6.ne, ← ENNReal.ofReal_toReal hG.ne,
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hsix
  have hAm : AEMeasurable (fun y => ENNReal.ofReal (A y ^ 2)) volume :=
    (hA.aemeasurable.pow_const 2).ennreal_ofReal
  have hwm2 : AEMeasurable (fun y => ENNReal.ofReal (‖w y‖ ^ 2)) volume :=
    (hwm.aemeasurable.norm.pow_const 2).ennreal_ofReal
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hAm hwm2
  have e2 : ∀ y, ENNReal.ofReal (A y ^ 2) ^ ((3 : ℝ) / 2) = ENNReal.ofReal (|A y| ^ 3) := by
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), sq_rpow_three_halves]
  have e3 : ∀ y, ENNReal.ofReal (‖w y‖ ^ 2) ^ (3 : ℝ) = ENNReal.ofReal (‖w y‖ ^ 6) := by
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), sq_rpow_three]
  simp only [Pi.mul_apply, e2, e3] at hH
  rw [show (1 : ℝ) / (3 / 2) = 2 / 3 by norm_num] at hH
  calc (∫⁻ y, ENNReal.ofReal (A y ^ 2 * ‖w y‖ ^ 2))
      = ∫⁻ y, ENNReal.ofReal (A y ^ 2) * ENNReal.ofReal (‖w y‖ ^ 2) := by
        congr 1
        funext y
        exact ENNReal.ofReal_mul (sq_nonneg _)
    _ ≤ (∫⁻ y, ENNReal.ofReal (|A y| ^ 3)) ^ ((2 : ℝ) / 3) *
        (∫⁻ y, ENNReal.ofReal (‖w y‖ ^ 6)) ^ ((1 : ℝ) / 3) := hH
    _ ≤ (∫⁻ y, ENNReal.ofReal (|A y| ^ 3)) ^ ((2 : ℝ) / 3) *
        (ENNReal.ofReal (4 / 3) * (∫⁻ y, ENNReal.ofReal (matSq (G y)))) := by
        gcongr
    _ = ENNReal.ofReal (4 / 3) * (∫⁻ y, ENNReal.ofReal (|A y| ^ 3)) ^ ((2 : ℝ) / 3) *
        (∫⁻ y, ENNReal.ofReal (matSq (G y))) := by
        ring

end CertReduction

end Breakdown
