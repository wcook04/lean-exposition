import Breakdown.CertCell.ShapeDefs

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open Polynomial

private theorem eval_iterate_derivative_eq_zero_of_dvd {P : Polynomial ℂ} {r : ℂ} {n o : ℕ}
    (h : (X - C r) ^ n ∣ P) (ho : o < n) : (derivative^[o] P).eval r = 0 := by
  obtain ⟨q, hq⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd o h
  rw [hq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow (by omega), zero_mul]

private theorem iterate_derivative_comp_linear (P q : Polynomial ℂ) (c : ℂ) (hq : derivative q = C c)
    (o : ℕ) : derivative^[o] (P.comp q) = C (c ^ o) * (derivative^[o] P).comp q := by
  induction o with
  | zero => simp
  | succ o ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp, hq,
      Function.iterate_succ_apply', pow_succ, C_mul]
    ring

private theorem eval_iterate_derivative_C_mul_X_pow_zero (c : ℂ) (p o : ℕ) :
    (derivative^[o] (C c * X ^ p)).eval 0 = if o = p then c * (p.factorial : ℂ) else 0 := by
  rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul, eval_mul, eval_C, eval_mul, eval_C,
    eval_pow, eval_X]
  rcases lt_trichotomy o p with h | h | h
  · rw [if_neg h.ne, zero_pow (by omega)]
    ring
  · subst h
    simp [Nat.descFactorial_self]
  · rw [if_neg h.ne', (Nat.descFactorial_eq_zero_iff_lt).2 h]
    simp

private theorem one_sub_pow_mul_choose_sum_sub_one (d m : ℕ) :
    X ^ m ∣ (1 - X : Polynomial ℂ) ^ (d + 1) *
      (∑ s ∈ Finset.range m, C ((Nat.choose (d + 1 - 1 + s) s : ℕ) : ℂ) * X ^ s) - 1 := by
  set F : PowerSeries ℂ := PowerSeries.mk fun s => ((Nat.choose (d + s) d : ℕ) : ℂ) with hF
  have hS : (∑ s ∈ Finset.range m, C ((Nat.choose (d + 1 - 1 + s) s : ℕ) : ℂ) * X ^ s) =
      PowerSeries.trunc m F := by
    ext k
    rw [PowerSeries.coeff_trunc, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, hF, PowerSeries.coeff_mk, Nat.add_sub_cancel]
    split_ifs
    · rw [Nat.choose_symm_add]
    · rfl
  have hG : ((((1 - X : Polynomial ℂ) ^ (d + 1) : Polynomial ℂ)) : PowerSeries ℂ) =
      (1 - PowerSeries.X) ^ (d + 1) := by
    simp
  rw [hS, X_pow_dvd_iff]
  intro k hk
  have key := congrArg (fun q : Polynomial ℂ => q.coeff k)
    (PowerSeries.trunc_trunc_mul (n := m) F ((1 - PowerSeries.X) ^ (d + 1)))
  simp only [PowerSeries.coeff_trunc, if_pos hk] at key
  rw [PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one] at key
  rw [coeff_sub, mul_comm, ← Polynomial.coeff_coe, Polynomial.coe_mul, hG, key, coeff_one,
    PowerSeries.coeff_one]
  simp

theorem iterate_derivative_jetUnit_eval_zero (n p o : ℕ) (ho : o < n) :
    (derivative^[o] (jetUnit n p)).eval 0 = if o = p then 1 else 0 := by
  by_cases hp : p < n
  · obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
    obtain ⟨R, hR⟩ := one_sub_pow_mul_choose_sum_sub_one d (d + 1 - p)
    have hsplit : jetUnit (d + 1) p = C ((p.factorial : ℂ)⁻¹) * X ^ p +
        (X - C 0) ^ (d + 1) * (C ((p.factorial : ℂ)⁻¹) * R) := by
      have h1 : (1 - X : Polynomial ℂ) ^ (d + 1) *
          (∑ s ∈ Finset.range (d + 1 - p), C ((Nat.choose (d + 1 - 1 + s) s : ℕ) : ℂ) * X ^ s) =
          1 + X ^ (d + 1 - p) * R := by
        rw [← hR]
        ring
      have h2 : (X : Polynomial ℂ) ^ (d + 1) = X ^ p * X ^ (d + 1 - p) := by
        rw [← pow_add]
        congr 1
        omega
      unfold jetUnit
      rw [mul_assoc (C _ * X ^ p), h1, map_zero, sub_zero, h2]
      ring
    rw [hsplit, iterate_map_add derivative, eval_add, eval_iterate_derivative_C_mul_X_pow_zero,
      eval_iterate_derivative_eq_zero_of_dvd (dvd_mul_right _ _) ho, add_zero]
    split_ifs
    · exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero p))
    · rfl
  · have h0 : jetUnit n p = 0 := by
      unfold jetUnit
      rw [show n - p = 0 by omega, Finset.range_zero, Finset.sum_empty, mul_zero]
    rw [h0, iterate_derivative_zero, eval_zero, if_neg (by omega)]

theorem iterate_derivative_jetUnit_eval_one (n p o : ℕ) (ho : o < n) :
    (derivative^[o] (jetUnit n p)).eval 1 = 0 := by
  apply eval_iterate_derivative_eq_zero_of_dvd _ ho
  have h1 : (X - C (1 : ℂ)) ∣ (1 - X) := ⟨-1, by rw [map_one]; ring⟩
  unfold jetUnit
  exact (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd h1 n) _).mul_right _

theorem iterate_derivative_nodalLeft_eval_left (n p o : ℕ) {a b : ℝ} (hab : a ≠ b) (ho : o < n) :
    (derivative^[o] (nodalLeft n p a b)).eval (a : ℂ) = if o = p then 1 else 0 := by
  have hba : ((b : ℂ) - a) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hab.symm)
  unfold nodalLeft
  rw [iterate_derivative_C_mul, iterate_derivative_comp_linear _ _ (((b - a)⁻¹ : ℝ) : ℂ) (by simp),
    eval_mul, eval_C, eval_mul, eval_C, eval_comp]
  simp only [eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]
  rw [iterate_derivative_jetUnit_eval_zero n p o ho]
  split_ifs with h
  · subst h
    push_cast
    rw [inv_pow, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hba)]
  · simp

theorem iterate_derivative_nodalLeft_eval_right (n p o : ℕ) {a b : ℝ} (hab : a ≠ b) (ho : o < n) :
    (derivative^[o] (nodalLeft n p a b)).eval (b : ℂ) = 0 := by
  have hba : ((b : ℂ) - a) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hab.symm)
  unfold nodalLeft
  rw [iterate_derivative_C_mul, iterate_derivative_comp_linear _ _ (((b - a)⁻¹ : ℝ) : ℂ) (by simp),
    eval_mul, eval_C, eval_mul, eval_C, eval_comp]
  simp only [eval_mul, eval_C, eval_sub, eval_X]
  push_cast
  rw [inv_mul_cancel₀ hba, iterate_derivative_jetUnit_eval_one n p o ho]
  simp

theorem iterate_derivative_nodalRight_eval_right (n p o : ℕ) {a b : ℝ} (hab : a ≠ b) (ho : o < n) :
    (derivative^[o] (nodalRight n p a b)).eval (b : ℂ) = if o = p then 1 else 0 := by
  have hba : ((b : ℂ) - a) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hab.symm)
  unfold nodalRight
  rw [iterate_derivative_C_mul, iterate_derivative_comp_linear _ _ (-(((b - a)⁻¹ : ℝ) : ℂ)) (by simp),
    eval_mul, eval_C, eval_mul, eval_C, eval_comp]
  simp only [eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]
  rw [iterate_derivative_jetUnit_eval_zero n p o ho]
  split_ifs with h
  · subst h
    push_cast
    rw [mul_one, ← mul_pow, show ((a : ℂ) - b) * -((b : ℂ) - a)⁻¹ = 1 by field_simp; ring, one_pow]
  · simp

theorem iterate_derivative_nodalRight_eval_left (n p o : ℕ) {a b : ℝ} (hab : a ≠ b) (ho : o < n) :
    (derivative^[o] (nodalRight n p a b)).eval (a : ℂ) = 0 := by
  have hba : ((b : ℂ) - a) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hab.symm)
  unfold nodalRight
  rw [iterate_derivative_C_mul, iterate_derivative_comp_linear _ _ (-(((b - a)⁻¹ : ℝ) : ℂ)) (by simp),
    eval_mul, eval_C, eval_mul, eval_C, eval_comp]
  simp only [eval_mul, eval_C, eval_sub, eval_X]
  push_cast
  rw [inv_mul_cancel₀ hba, iterate_derivative_jetUnit_eval_one n p o ho]
  simp

theorem iterate_derivative_bubblePoly_eval_left (n s o : ℕ) (a b : ℝ) (ho : o < n) :
    (derivative^[o] (bubblePoly n s a b)).eval (a : ℂ) = 0 := by
  apply eval_iterate_derivative_eq_zero_of_dvd _ ho
  unfold bubblePoly
  rw [mul_pow]
  exact Dvd.dvd.mul_right (dvd_mul_right ((X - C (a : ℂ)) ^ n) ((C (b : ℂ) - X) ^ n)) _

theorem iterate_derivative_bubblePoly_eval_right (n s o : ℕ) (a b : ℝ) (ho : o < n) :
    (derivative^[o] (bubblePoly n s a b)).eval (b : ℂ) = 0 := by
  apply eval_iterate_derivative_eq_zero_of_dvd _ ho
  have h1 : (X - C (b : ℂ)) ∣ (C (b : ℂ) - X) := ⟨-1, by ring⟩
  unfold bubblePoly
  rw [mul_pow]
  exact ((pow_dvd_pow_of_dvd h1 n).mul_left _).mul_right _

end GivenShape

end CertCell

end Breakdown
