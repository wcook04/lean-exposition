import Breakdown.FracCert.StKernel
import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff
open Real

noncomputable section

namespace Breakdown.FracCert

private def ringProfile (ξ : Space) : ℝ := radialCutoff 1 ξ - radialCutoff (1 / 2) ξ

private theorem ringProfile_eq (ξ : Space) :
    ringProfile ξ = smoothTransition (2 - ‖ξ‖) - smoothTransition (2 - 2 * ‖ξ‖) := by
  unfold ringProfile radialCutoff
  congr 2 <;> ring

private theorem ringProfile_contDiff : ContDiff ℝ ∞ ringProfile := by
  show ContDiff ℝ ∞ (fun ξ => radialCutoff 1 ξ - radialCutoff (1 / 2) ξ)
  exact (contDiff_radialCutoff one_pos).sub (contDiff_radialCutoff (by norm_num))

private theorem ringProfile_bounds (ξ : Space) : 0 ≤ ringProfile ξ ∧ ringProfile ξ ≤ 1 := by
  rw [ringProfile_eq]
  have h1 := smoothTransition.monotone (show 2 - 2 * ‖ξ‖ ≤ 2 - ‖ξ‖ by linarith [norm_nonneg ξ])
  have h2 := smoothTransition.le_one (2 - ‖ξ‖)
  have h3 := smoothTransition.nonneg (2 - 2 * ‖ξ‖)
  constructor <;> linarith

private theorem ringProfile_support (ξ : Space) (h : ringProfile ξ ≠ 0) :
    1 / 2 < ‖ξ‖ ∧ ‖ξ‖ < 2 := by
  rw [ringProfile_eq] at h
  by_contra hc
  rcases not_and_or.1 hc with h' | h'
  · push Not at h'
    have e1 : smoothTransition (2 - ‖ξ‖) = 1 := smoothTransition.one_of_one_le (by linarith)
    have e2 : smoothTransition (2 - 2 * ‖ξ‖) = 1 := smoothTransition.one_of_one_le (by linarith)
    exact h (by rw [e1, e2, sub_self])
  · push Not at h'
    have e1 : smoothTransition (2 - ‖ξ‖) = 0 := smoothTransition.zero_of_nonpos (by linarith)
    have e2 : smoothTransition (2 - 2 * ‖ξ‖) = 0 := smoothTransition.zero_of_nonpos (by linarith)
    exact h (by rw [e1, e2, sub_self])

private theorem ringProfile_smul {c : ℝ} (hc : 0 < c) (ξ : Space) :
    ringProfile (c • ξ) =
      smoothTransition (2 - c * ‖ξ‖) - smoothTransition (2 - 2 * (c * ‖ξ‖)) := by
  rw [ringProfile_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hc]

private theorem two_rpow_neg_int (l : ℤ) : (2 : ℝ) ^ (-(l : ℝ)) = ((2 : ℝ) ^ l)⁻¹ := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_intCast]

private theorem ringProfile_hasSum (ξ : Space) (hξ : ξ ≠ 0) :
    HasSum (fun l : ℤ => ringProfile (((2 : ℝ) ^ (-(l : ℝ))) • ξ)) 1 := by
  have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow hr (show (1 : ℝ) < 2 by norm_num)
  have h2pos : ∀ l : ℤ, (0 : ℝ) < 2 ^ l := fun l => zpow_pos (by norm_num) l
  have hterm : ∀ l : ℤ, ringProfile (((2 : ℝ) ^ (-(l : ℝ))) • ξ) =
      smoothTransition (2 - ‖ξ‖ / 2 ^ l) - smoothTransition (2 - 2 * (‖ξ‖ / 2 ^ l)) := by
    intro l
    rw [ringProfile_smul (Real.rpow_pos_of_pos (by norm_num) _), two_rpow_neg_int,
      inv_mul_eq_div]
  have hzero : ∀ l ∉ ({m, m + 1} : Finset ℤ),
      ringProfile (((2 : ℝ) ^ (-(l : ℝ))) • ξ) = 0 := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    rw [hterm]
    rcases lt_or_gt_of_ne hl.1 with h | h
    · have hle : (2 : ℝ) ^ l * 2 ≤ 2 ^ m := by
        rw [← zpow_add_one₀ (by norm_num)]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hu : 2 ≤ ‖ξ‖ / 2 ^ l := by
        rw [le_div_iff₀ (h2pos l)]
        linarith
      have e1 : smoothTransition (2 - ‖ξ‖ / 2 ^ l) = 0 :=
        smoothTransition.zero_of_nonpos (by linarith)
      have e2 : smoothTransition (2 - 2 * (‖ξ‖ / 2 ^ l)) = 0 :=
        smoothTransition.zero_of_nonpos (by linarith)
      rw [e1, e2, sub_self]
    · have hle : (2 : ℝ) ^ (m + 1) * 2 ≤ 2 ^ l := by
        rw [← zpow_add_one₀ (by norm_num)]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hu : ‖ξ‖ / 2 ^ l ≤ 1 / 2 := by
        rw [div_le_iff₀ (h2pos l)]
        linarith
      have e1 : smoothTransition (2 - ‖ξ‖ / 2 ^ l) = 1 :=
        smoothTransition.one_of_one_le (by linarith)
      have e2 : smoothTransition (2 - 2 * (‖ξ‖ / 2 ^ l)) = 1 :=
        smoothTransition.one_of_one_le (by linarith)
      rw [e1, e2, sub_self]
  have hsum := hasSum_sum_of_ne_finset_zero
    (f := fun l : ℤ => ringProfile (((2 : ℝ) ^ (-(l : ℝ))) • ξ))
    (L := SummationFilter.unconditional ℤ) hzero
  have hm' : m ≠ m + 1 := by omega
  rw [Finset.sum_pair hm'] at hsum
  convert hsum using 1
  simp only [hterm]
  have hhalf : 2 * (‖ξ‖ / 2 ^ (m + 1)) = ‖ξ‖ / 2 ^ m := by
    rw [zpow_add_one₀ (by norm_num)]
    field_simp
  have hbig : 1 ≤ ‖ξ‖ / 2 ^ m := by
    rw [le_div_iff₀ (h2pos m)]
    linarith
  have hsmall : ‖ξ‖ / 2 ^ (m + 1) ≤ 1 := by
    rw [div_le_one (h2pos _)]
    exact hm2.le
  have e1 : smoothTransition (2 - 2 * (‖ξ‖ / 2 ^ m)) = 0 :=
    smoothTransition.zero_of_nonpos (by linarith)
  have e2 : smoothTransition (2 - ‖ξ‖ / 2 ^ (m + 1)) = 1 :=
    smoothTransition.one_of_one_le (by linarith)
  rw [hhalf, e1, e2]
  ring

theorem ringCutoff : RingCutoffStatement :=
  ⟨ringProfile, ringProfile_contDiff, ringProfile_bounds, ringProfile_support, ringProfile_hasSum⟩

end Breakdown.FracCert
