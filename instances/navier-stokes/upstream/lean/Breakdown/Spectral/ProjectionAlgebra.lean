import Mathlib

noncomputable section

namespace Breakdown.Spectral

private theorem tendsto_bound_prod {K r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ < r₂) :
    Filter.Tendsto (fun n : ℕ => K * r₁ ^ n * (K * r₂⁻¹ ^ n)) Filter.atTop (nhds 0) := by
  have hr₂ : 0 < r₂ := lt_of_le_of_lt h0 h12
  have hq0 : 0 ≤ r₁ * r₂⁻¹ := mul_nonneg h0 (inv_nonneg.mpr hr₂.le)
  have hq1 : r₁ * r₂⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one hr₂).mpr h12
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (K * K)
  rw [mul_zero] at h
  refine h.congr (fun n => ?_)
  rw [mul_pow]
  ring

private theorem eq_zero_of_bounds {E : Type*} [NormedAddCommGroup E] (v : E) {K r₁ r₂ c : ℝ}
    (h0 : 0 ≤ r₁) (h12 : r₁ < r₂) (h : ∀ n : ℕ, ‖v‖ ≤ K * r₁ ^ n * (K * r₂⁻¹ ^ n) * c) :
    v = 0 := by
  have ht := (tendsto_bound_prod (K := K) h0 h12).mul_const c
  rw [zero_mul] at ht
  exact norm_le_zero_iff.mp (ge_of_tendsto' ht h)

theorem idempotent_of_bounds {A : Type*} [NormedRing A] (T Q : A) (B : ℕ → A) {K r₁ r₂ : ℝ}
    (h0 : 0 ≤ r₁) (h12 : r₁ < r₂) (hQT : Commute Q T) (hQB : ∀ n, Commute Q (B n))
    (hTB : ∀ n, T ^ n * B n = 1 - Q) (hs : ∀ n : ℕ, ‖T ^ n * Q‖ ≤ K * r₁ ^ n)
    (hu : ∀ n : ℕ, ‖B n‖ ≤ K * r₂⁻¹ ^ n) : Q * Q = Q := by
  have key : ∀ n : ℕ, ‖Q - Q * Q‖ ≤ K * r₁ ^ n * (K * r₂⁻¹ ^ n) := by
    intro n
    have he : Q - Q * Q = T ^ n * Q * B n := by
      rw [← (hQT.pow_right n).eq, mul_assoc, hTB n, mul_sub, mul_one]
    rw [he]
    calc ‖T ^ n * Q * B n‖ ≤ ‖T ^ n * Q‖ * ‖B n‖ := norm_mul_le _ _
      _ ≤ K * r₁ ^ n * (K * r₂⁻¹ ^ n) :=
        mul_le_mul (hs n) (hu n) (norm_nonneg _) ((norm_nonneg _).trans (hs n))
  have h := ge_of_tendsto' (tendsto_bound_prod (K := K) h0 h12) key
  have hz : Q - Q * Q = 0 := norm_le_zero_iff.mp h
  exact (sub_eq_zero.mp hz).symm

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

private theorem iterate_comm (T : Y →L[ℂ] Y) (U : Y →+ Y) (hUT : ∀ y, U (T y) = T (U y)) :
    ∀ (n : ℕ) (y : Y), U ((T ^ n) y) = (T ^ n) (U y) := by
  intro n
  induction n with
  | zero =>
    intro y
    rw [pow_zero, one_apply_eq_self, one_apply_eq_self]
  | succ n ih =>
    intro y
    rw [pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih, hUT]

theorem map_comm_of_bounds (T Q : Y →L[ℂ] Y) (B : ℕ → Y →L[ℂ] Y) {K r₁ r₂ : ℝ}
    (h0 : 0 ≤ r₁) (h12 : r₁ < r₂) (hQT : Commute Q T) (hBT : ∀ n, Commute (B n) T)
    (hTB : ∀ n, T ^ n * B n = 1 - Q) (hs : ∀ n : ℕ, ‖T ^ n * Q‖ ≤ K * r₁ ^ n)
    (hu : ∀ n : ℕ, ‖B n‖ ≤ K * r₂⁻¹ ^ n) (U : Y →+ Y) (hU : ∀ y, ‖U y‖ = ‖y‖)
    (hUT : ∀ y, U (T y) = T (U y)) (y : Y) : U (Q y) = Q (U y) := by
  have hit := iterate_comm T U hUT
  have hBT' : ∀ n, B n * T ^ n = 1 - Q := fun n => ((hBT n).pow_right n).eq.trans (hTB n)
  have hQTn : ∀ n : ℕ, Q * T ^ n = T ^ n * Q := fun n => (hQT.pow_right n).eq
  have ha : U (Q y) - Q (U (Q y)) = 0 := by
    refine eq_zero_of_bounds _ h0 h12 (K := K) (c := ‖y‖) (fun n => ?_)
    have he : U (Q y) - Q (U (Q y)) = B n (U ((T ^ n * Q) y)) := by
      rw [mul_apply_eq_comp, hit, ← mul_apply_eq_comp (B n), hBT' n,
        sub_apply, one_apply_eq_self]
    rw [he]
    calc ‖B n (U ((T ^ n * Q) y))‖ ≤ ‖B n‖ * ‖U ((T ^ n * Q) y)‖ := (B n).le_opNorm _
      _ = ‖B n‖ * ‖(T ^ n * Q) y‖ := by rw [hU]
      _ ≤ ‖B n‖ * (‖T ^ n * Q‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left ((T ^ n * Q).le_opNorm _) (norm_nonneg _)
      _ ≤ (K * r₂⁻¹ ^ n) * ((K * r₁ ^ n) * ‖y‖) :=
        mul_le_mul (hu n) (mul_le_mul_of_nonneg_right (hs n) (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ((norm_nonneg _).trans (hu n))
      _ = K * r₁ ^ n * (K * r₂⁻¹ ^ n) * ‖y‖ := by ring
  have hb : Q (U (y - Q y)) = 0 := by
    refine eq_zero_of_bounds _ h0 h12 (K := K) (c := ‖y‖) (fun n => ?_)
    have he : Q (U (y - Q y)) = (T ^ n * Q) (U (B n y)) := by
      rw [← hQTn, mul_apply_eq_comp, ← hit, ← mul_apply_eq_comp (T ^ n),
        hTB n, sub_apply, one_apply_eq_self]
    rw [he]
    calc ‖(T ^ n * Q) (U (B n y))‖ ≤ ‖T ^ n * Q‖ * ‖U (B n y)‖ := (T ^ n * Q).le_opNorm _
      _ = ‖T ^ n * Q‖ * ‖B n y‖ := by rw [hU]
      _ ≤ ‖T ^ n * Q‖ * (‖B n‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left ((B n).le_opNorm _) (norm_nonneg _)
      _ ≤ (K * r₁ ^ n) * ((K * r₂⁻¹ ^ n) * ‖y‖) :=
        mul_le_mul (hs n) (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ((norm_nonneg _).trans (hs n))
      _ = K * r₁ ^ n * (K * r₂⁻¹ ^ n) * ‖y‖ := by ring
  have hy : U y = U (Q y) + U (y - Q y) := by
    rw [← map_add, add_sub_cancel]
  rw [hy, map_add, hb, add_zero]
  exact sub_eq_zero.mp ha

end Breakdown.Spectral
