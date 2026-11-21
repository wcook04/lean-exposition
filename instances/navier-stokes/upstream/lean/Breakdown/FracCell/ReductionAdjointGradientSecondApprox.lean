import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FracCell.ReductionAdjointMollifySecondApprox
import Breakdown.FracCell.ReductionAdjointCutoffSecondApprox

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

def GradientSecondApproxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∃ u : ℕ → Space → Space, (∀ n, IsTestVectorField (u n)) ∧
      (∀ n, Integrable (fun y => entrySq (fderiv ℝ (u n) y - G y))) ∧
      Tendsto (fun n => ∫ y, entrySq (fderiv ℝ (u n) y - G y)) atTop (𝓝 0) ∧
      (∀ n, Integrable (fun y => CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u n)) y - H y))) ∧
      Tendsto (fun n => ∫ y, CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u n)) y - H y)) atTop (𝓝 0)

namespace GradientSecondApproxInternal

theorem sq_norm_add_le (a b : Space) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h0 : 0 ≤ ‖a + b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem entrySq_add_le (A B : Space →L[ℝ] Space) : entrySq (A + B) ≤ 2 * entrySq A + 2 * entrySq B := by
  unfold entrySq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ContinuousLinearMap.add_apply]
  exact sq_norm_add_le _ _

theorem fullSecondSq_add_le (A B : Space →L[ℝ] Space →L[ℝ] Space) :
    CellCert.fullSecondSq (A + B) ≤ 2 * CellCert.fullSecondSq A + 2 * CellCert.fullSecondSq B := by
  unfold CellCert.fullSecondSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  exact sq_norm_add_le _ _

theorem entrySq_nonneg (A : Space →L[ℝ] Space) : 0 ≤ entrySq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem fullSecondSq_nonneg (A : Space →L[ℝ] Space →L[ℝ] Space) : 0 ≤ CellCert.fullSecondSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem entrySq_continuous : Continuous entrySq := by
  unfold entrySq
  exact continuous_finset_sum _ fun i _ => ((continuous_id.clm_apply continuous_const).norm.pow 2)

theorem fullSecondSq_continuous : Continuous CellCert.fullSecondSq := by
  unfold CellCert.fullSecondSq
  exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
    (((continuous_id.clm_apply continuous_const).clm_apply continuous_const).norm.pow 2)

theorem split_bound {f g h : Space → ℝ} (hm : AEStronglyMeasurable f volume) (hg : Integrable g)
    (hh : Integrable h) (hle : ∀ y, f y ≤ 2 * g y + 2 * h y) (h0 : ∀ y, 0 ≤ f y) {ε : ℝ}
    (hgε : ∫ y, g y ≤ ε) (hhε : ∫ y, h y ≤ ε) : Integrable f ∧ ∫ y, f y ≤ 4 * ε := by
  have hs : Integrable (fun y => 2 * g y + 2 * h y) := (hg.const_mul 2).add (hh.const_mul 2)
  have hf : Integrable f := hs.mono' hm (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]
    exact hle y)
  refine ⟨hf, ?_⟩
  calc ∫ y, f y ≤ ∫ y, (2 * g y + 2 * h y) := integral_mono hf hs hle
    _ = 2 * (∫ y, g y) + 2 * ∫ y, h y := by
        rw [integral_add (hg.const_mul 2) (hh.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ 4 * ε := by linarith

end GradientSecondApproxInternal

open GradientSecondApproxInternal in
theorem gradientSecondApprox_of (h1 : MollifySecondApproxStatement) (h2 : CutoffSecondApproxStatement) :
    GradientSecondApproxStatement := by
  intro m v G H hv
  have hε : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  choose w hwc hw6 hwE hwS hwGi hwGle hwHi hwHle using fun k => h1 m v G H hv _ (hε k)
  choose u hut huGi huGle huHi huHle using fun k => h2 (w k) (hwc k) (hw6 k) (hwE k) (hwS k) _ (hε k)
  have hD1 : ∀ k, Continuous (fun y => fderiv ℝ (u k) y) := fun k =>
    (hut k).1.continuous_fderiv (by simp)
  have hD2 : ∀ k, Continuous (fun y => fderiv ℝ (fderiv ℝ (u k)) y) := fun k =>
    (contDiff_infty_iff_fderiv.1 (contDiff_infty_iff_fderiv.1 (hut k).1).2).2.continuous
  have bG : ∀ k, Integrable (fun y => entrySq (fderiv ℝ (u k) y - G y)) ∧
      ∫ y, entrySq (fderiv ℝ (u k) y - G y) ≤ 4 * (1 / ((k : ℝ) + 1)) := by
    intro k
    refine split_bound (entrySq_continuous.comp_aestronglyMeasurable
      ((hD1 k).aestronglyMeasurable.sub hv.measurable_gradient)) (huGi k) (hwGi k) (fun y => ?_)
      (fun y => entrySq_nonneg _) (huGle k) (hwGle k)
    have e : fderiv ℝ (u k) y - G y = (fderiv ℝ (u k) y - fderiv ℝ (w k) y) + (fderiv ℝ (w k) y - G y) := by
      abel
    show entrySq (fderiv ℝ (u k) y - G y) ≤ _
    rw [e]
    exact entrySq_add_le _ _
  have bH : ∀ k, Integrable (fun y => CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u k)) y - H y)) ∧
      ∫ y, CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u k)) y - H y) ≤ 4 * (1 / ((k : ℝ) + 1)) := by
    intro k
    refine split_bound (fullSecondSq_continuous.comp_aestronglyMeasurable
      ((hD2 k).aestronglyMeasurable.sub hv.measurable_second)) (huHi k) (hwHi k) (fun y => ?_)
      (fun y => fullSecondSq_nonneg _) (huHle k) (hwHle k)
    have e : fderiv ℝ (fderiv ℝ (u k)) y - H y =
        (fderiv ℝ (fderiv ℝ (u k)) y - fderiv ℝ (fderiv ℝ (w k)) y) + (fderiv ℝ (fderiv ℝ (w k)) y - H y) := by
      abel
    show CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u k)) y - H y) ≤ _
    rw [e]
    exact fullSecondSq_add_le _ _
  have ht : Tendsto (fun k : ℕ => 4 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (4 : ℝ)
    rwa [mul_zero] at h
  refine ⟨u, hut, fun k => (bG k).1, ?_, fun k => (bH k).1, ?_⟩
  · exact squeeze_zero (fun k => integral_nonneg fun y => entrySq_nonneg _) (fun k => (bG k).2) ht
  · exact squeeze_zero (fun k => integral_nonneg fun y => fullSecondSq_nonneg _) (fun k => (bH k).2) ht

theorem gradientSecondApprox : GradientSecondApproxStatement :=
  gradientSecondApprox_of mollifySecondApprox cutoffSecondApprox

end Reduction

end CellCert

end Breakdown
