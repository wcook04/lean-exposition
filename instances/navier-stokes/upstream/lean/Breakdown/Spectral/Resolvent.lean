import Mathlib

noncomputable section

open Metric

namespace Breakdown.Spectral

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

theorem resolvent_mul_sub (T : Y →L[ℂ] Y) {z : ℂ} (hz : z ∈ resolventSet ℂ T) :
    resolvent T z * (z • 1 - T) = 1 := by
  have h := spectrum.mem_resolventSet_iff.mp hz
  rw [Algebra.algebraMap_eq_smul_one] at h
  rw [resolvent, Algebra.algebraMap_eq_smul_one]
  exact Ring.inverse_mul_cancel _ h

theorem sub_mul_resolvent (T : Y →L[ℂ] Y) {z : ℂ} (hz : z ∈ resolventSet ℂ T) :
    (z • 1 - T) * resolvent T z = 1 := by
  have h := spectrum.mem_resolventSet_iff.mp hz
  rw [Algebra.algebraMap_eq_smul_one] at h
  rw [resolvent, Algebra.algebraMap_eq_smul_one]
  exact Ring.mul_inverse_cancel _ h

theorem commute_resolvent {T A : Y →L[ℂ] Y} (h : Commute A T) (z : ℂ) :
    Commute A (resolvent T z) := by
  have h1 : Commute A (algebraMap ℂ (Y →L[ℂ] Y) z - T) :=
    (show Commute A (algebraMap ℂ (Y →L[ℂ] Y) z) from (Algebra.commutes z A).symm).sub_right h
  rw [resolvent]
  by_cases hu : IsUnit (algebraMap ℂ (Y →L[ℂ] Y) z - T)
  · obtain ⟨u, hu⟩ := hu
    rw [← hu] at h1 ⊢
    rw [Ring.inverse_unit]
    exact (Commute.units_inv_right h1)
  · rw [Ring.inverse_non_unit _ hu]
    exact Commute.zero_right A

theorem mul_resolvent (T : Y →L[ℂ] Y) {z : ℂ} (hz : z ∈ resolventSet ℂ T) :
    T * resolvent T z = z • resolvent T z - 1 := by
  have h := sub_mul_resolvent T hz
  rw [sub_mul, smul_mul_assoc, one_mul] at h
  rw [← h]
  abel

theorem pow_mul_resolvent (T : Y →L[ℂ] Y) {z : ℂ} (hz : z ∈ resolventSet ℂ T) (n : ℕ) :
    T ^ n * resolvent T z =
      z ^ n • resolvent T z - ∑ j ∈ Finset.range n, z ^ (n - 1 - j) • T ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, mul_sub, mul_smul_comm, mul_resolvent T hz, Finset.mul_sum,
      Finset.sum_range_succ']
    have hs : ∀ j ∈ Finset.range n, T * z ^ (n - 1 - j) • T ^ j =
        z ^ (n + 1 - 1 - (j + 1)) • T ^ (j + 1) := by
      intro j _
      rw [mul_smul_comm, ← pow_succ']
      congr 2
      omega
    rw [Finset.sum_congr rfl hs, smul_sub, smul_smul, ← pow_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero]
    abel

theorem continuousOn_resolvent (T : Y →L[ℂ] Y) :
    ContinuousOn (resolvent T) (resolventSet ℂ T) := fun _ hz =>
  (spectrum.hasDerivAt_resolvent_const_left hz).continuousAt.continuousWithinAt

theorem differentiableAt_resolvent (T : Y →L[ℂ] Y) {z : ℂ} (hz : z ∈ resolventSet ℂ T) :
    DifferentiableAt ℂ (resolvent T) z :=
  (spectrum.hasDerivAt_resolvent_const_left hz).differentiableAt

theorem mem_resolventSet_of_norm_le_lt {T : Y →L[ℂ] Y} {b : ℝ} (hT : ‖T‖ ≤ b) {z : ℂ}
    (hz : b < ‖z‖) : z ∈ resolventSet ℂ T := by
  apply spectrum.mem_resolventSet_of_norm_lt_mul
  have h1 : ‖(1 : Y →L[ℂ] Y)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc ‖T‖ * ‖(1 : Y →L[ℂ] Y)‖ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ b := by rw [mul_one]; exact hT
    _ < ‖z‖ := hz

private theorem norm_le_of_sub_apply {T : Y →L[ℂ] Y} {b : ℝ} (hT : ‖T‖ ≤ b) (z : ℂ) (v : Y) :
    (‖z‖ - b) * ‖v‖ ≤ ‖(z • 1 - T) v‖ := by
  have h1 : ‖T v‖ ≤ b * ‖v‖ :=
    (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have h2 : ‖z • v‖ - ‖T v‖ ≤ ‖z • v - T v‖ := norm_sub_norm_le _ _
  have h3 : (z • 1 - T) v = z • v - T v := by simp
  rw [h3]
  rw [norm_smul] at h2
  nlinarith

theorem norm_resolvent_le {T : Y →L[ℂ] Y} {b : ℝ} (hT : ‖T‖ ≤ b) {z : ℂ} (hz : b < ‖z‖) :
    ‖resolvent T z‖ ≤ (‖z‖ - b)⁻¹ := by
  have hpos : 0 < ‖z‖ - b := sub_pos.mpr hz
  have hr := mem_resolventSet_of_norm_le_lt hT hz
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hpos.le) fun w => ?_
  have h1 := norm_le_of_sub_apply hT z (resolvent T z w)
  have h2 : (z • 1 - T) (resolvent T z w) = w := by
    show ((z • 1 - T) * resolvent T z) w = w
    rw [sub_mul_resolvent T hr]
    rfl
  rw [h2] at h1
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  exact h1

theorem circleIntegral_mul_left (A : Y →L[ℂ] Y) {f : ℂ → Y →L[ℂ] Y} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), A * f z) = A * ∮ z in C(c, R), f z := by
  have h := (ContinuousLinearMap.mul ℂ (Y →L[ℂ] Y) A).intervalIntegral_comp_comm hf.out
  simp only [ContinuousLinearMap.mul_apply', mul_smul_comm] at h
  simpa only [circleIntegral] using h

theorem circleIntegral_mul_right (A : Y →L[ℂ] Y) {f : ℂ → Y →L[ℂ] Y} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), f z * A) = (∮ z in C(c, R), f z) * A := by
  have h := ((ContinuousLinearMap.mul ℂ (Y →L[ℂ] Y)).flip A).intervalIntegral_comp_comm hf.out
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', smul_mul_assoc] at h
  simpa only [circleIntegral] using h

theorem commute_circleIntegral {A : Y →L[ℂ] Y} {f : ℂ → Y →L[ℂ] Y} (hA : ∀ z, Commute A (f z))
    (c : ℂ) (R : ℝ) : Commute A (∮ z in C(c, R), f z) := by
  by_cases hf : CircleIntegrable f c R
  · change A * _ = _ * A
    rw [← circleIntegral_mul_left A hf, ← circleIntegral_mul_right A hf]
    congr 1
    funext z
    exact (hA z).eq
  · rw [circleIntegral.integral_undef hf]
    exact Commute.zero_right A

theorem circleIntegral_pow_smul_const (E : Y →L[ℂ] Y) {R : ℝ} (n : ℕ) :
    (∮ z in C(0, R), z ^ n • E) = 0 := by
  rw [circleIntegral.integral_smul_const]
  have h := circleIntegral.integral_sub_zpow_of_ne (n := (n : ℤ)) (by omega) 0 0 R
  simp only [sub_zero, zpow_natCast] at h
  rw [h, zero_smul]

theorem circleIntegral_inv_pow_smul_const (E : Y →L[ℂ] Y) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    (∮ z in C(0, R), (z ^ (n + 1))⁻¹ • E) = if n = 0 then (2 * Real.pi * Complex.I) • E else 0 := by
  rw [circleIntegral.integral_smul_const]
  split_ifs with hn
  · subst hn
    have h := circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := R)
      (mem_ball_self hR)
    simp only [sub_zero] at h
    simp only [zero_add, pow_one, h]
  · have h := circleIntegral.integral_sub_zpow_of_ne (n := -((n : ℤ) + 1)) (by omega) 0 0 R
    simp only [sub_zero, zpow_neg] at h
    have h2 : ∀ z : ℂ, (z ^ ((n : ℤ) + 1))⁻¹ = (z ^ (n + 1))⁻¹ := fun z => by
      rw [← zpow_natCast]; push_cast; rfl
    simp only [h2] at h
    rw [h, zero_smul]

end Breakdown.Spectral
