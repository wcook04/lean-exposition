import Breakdown.FracCell.StSpectral

open MeasureTheory Polynomial
open scoped Interval

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

private def clampUnit (x : ℝ) : ℝ := max (-1) (min 1 x)

private theorem clampUnit_mem (x : ℝ) : clampUnit x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem clampUnit_dist (x y : ℝ) : dist (clampUnit x) (clampUnit y) ≤ dist x y := by
  rw [Real.dist_eq, Real.dist_eq, abs_sub_le_iff]
  unfold clampUnit
  constructor <;>
  · rcases abs_cases (x - y) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
    · simp only [max_def, min_def]
      split_ifs <;> linarith

private theorem clampUnit_eq {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : clampUnit x = x := by
  unfold clampUnit
  rw [min_eq_right hx.2, max_eq_right hx.1]

private theorem slope_comp_clamp (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) :
    ∃ K, LipschitzWith K (fun x => u (clampUnit x)) := by
  obtain ⟨K, hK⟩ := (hu.contDiffOn (s := Set.Icc (-1 : ℝ) 1)).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  exact (hK.dist_le_mul _ (clampUnit_mem x) _ (clampUnit_mem y)).trans
    (mul_le_mul_of_nonneg_left (clampUnit_dist x y) K.2)

private theorem deriv_comp_clamp (u : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun y => u (clampUnit y)) x = deriv u x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  rw [clampUnit_eq (Set.Ioo_subset_Icc_self hy)]

theorem intervalMonotone_of (h1 : IntervalIdentityStatement) (h2 : IntervalMinimalStatement) :
    IntervalMonotoneStatement := by
  intro ν μ p hν hνμ
  have hμ : 0 < μ := hν.trans_le hνμ
  obtain ⟨hC, hm1, hp1, hid⟩ := h1 ν p hν
  set u := intervalResolvent ν p with hu_def
  set w : ℝ → ℝ := fun y => u (clampUnit y) with hw_def
  have hwL : ∃ K, LipschitzWith K w := slope_comp_clamp u hC
  have hwm1 : w (-1) = 0 := by
    simp only [hw_def]; rw [clampUnit_eq (by norm_num)]; exact hm1
  have hwp1 : w 1 = 0 := by
    simp only [hw_def]; rw [clampUnit_eq (by norm_num)]; exact hp1
  have hmin := h2 μ p hμ w hwL hwm1 hwp1
  have hsq : (∫ x in (-1 : ℝ)..1, (p.eval x - w x) ^ 2) = ∫ x in (-1 : ℝ)..1, (p.eval x - u x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [hw_def]
    rw [clampUnit_eq hx]
  have hder : (∫ x in (-1 : ℝ)..1, deriv w x ^ 2) = ∫ x in (-1 : ℝ)..1, deriv u x ^ 2 := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [Measure.ae_ne volume (1 : ℝ)] with x hx1 hx
      rw [deriv_comp_clamp u ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩]
    · exact Filter.Eventually.of_forall fun x hx => absurd (hx.1.trans_le hx.2) (by norm_num)
  have hnn : 0 ≤ ∫ x in (-1 : ℝ)..1, deriv u x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => sq_nonneg _
  have hinv : μ⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hνμ
  calc (∫ x in (-1 : ℝ)..1, intervalSmoothed μ p x * p.eval x)
      ≤ (∫ x in (-1 : ℝ)..1, (p.eval x - w x) ^ 2) + μ⁻¹ * (∫ x in (-1 : ℝ)..1, deriv w x ^ 2) := hmin
    _ = (∫ x in (-1 : ℝ)..1, (p.eval x - u x) ^ 2) + μ⁻¹ * (∫ x in (-1 : ℝ)..1, deriv u x ^ 2) := by
      rw [hsq, hder]
    _ ≤ (∫ x in (-1 : ℝ)..1, (p.eval x - u x) ^ 2) + ν⁻¹ * (∫ x in (-1 : ℝ)..1, deriv u x ^ 2) := by
      gcongr
    _ = ∫ x in (-1 : ℝ)..1, intervalSmoothed ν p x * p.eval x := hid

end Spectral

end CellCert

end Breakdown
