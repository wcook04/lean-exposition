import Breakdown.CertCell.InstanceStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

namespace Internal

theorem integral_exp_full_period (ω L : ℝ) (k : ℤ) (h : ω * L = 2 * Real.pi * k) :
    ∫ t in (0 : ℝ)..L, Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) = if ω = 0 then (L : ℂ) else 0 := by
  split_ifs with hω
  · subst hω
    simp
  · have hc : (ω : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) Complex.I_ne_zero
    have e : ∀ t : ℝ, Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((ω : ℂ) * Complex.I) * (t : ℂ)) := by
      intro t
      congr 1
      push_cast
      ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have hL : (ω : ℂ) * (L : ℂ) = 2 * (Real.pi : ℂ) * (k : ℂ) := by exact_mod_cast h
    have h1 : Complex.exp (((ω : ℂ) * Complex.I) * (L : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I k]
      congr 1
      linear_combination Complex.I * hL
    simp [h1]

theorem integral_re_exp_full_period (ω L : ℝ) (k : ℤ) (h : ω * L = 2 * Real.pi * k) (c : ℂ) :
    ∫ t in (0 : ℝ)..L, (c * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)).re =
      if ω = 0 then L * c.re else 0 := by
  have hi : IntervalIntegrable (fun t : ℝ => c * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)) volume 0 L :=
    (by fun_prop : Continuous fun t : ℝ => c * Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)).intervalIntegrable _ _
  have hre := Complex.reCLM.intervalIntegral_comp_comm hi
  simp only [Complex.reCLM_apply] at hre
  rw [hre, intervalIntegral.integral_const_mul, integral_exp_full_period ω L k h]
  split_ifs
  · simp [mul_comm]
  · simp

theorem re_mul_re_eq (u w : ℂ) : u.re * w.re = (u * starRingEnd ℂ w).re / 2 + (u * w).re / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem exp_phase_add (x y : ℝ) :
    Complex.exp (((x + y : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((y : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_mul_conj (a b : ℝ) (A B : ℂ) :
    Complex.exp ((a : ℂ) * Complex.I) * A * starRingEnd ℂ (Complex.exp ((b : ℂ) * Complex.I) * B) =
      A * starRingEnd ℂ B * Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) := by
  rw [map_mul, ← Complex.exp_conj, sub_eq_add_neg, exp_phase_add]
  have hc : starRingEnd ℂ ((b : ℂ) * Complex.I) = ((-b : ℝ) : ℂ) * Complex.I := by simp
  rw [hc]
  ring

theorem phase_mul_phase (a b : ℝ) (A B : ℂ) :
    Complex.exp ((a : ℂ) * Complex.I) * A * (Complex.exp ((b : ℂ) * Complex.I) * B) =
      A * B * Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
  rw [exp_phase_add]
  ring

theorem angle_mean (ξ ζ : ℤ × ℤ) (A B : ℂ) (σ : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) * A).re *
        (Complex.exp (((2 * Real.pi * ζ.1 * σ + ζ.2 * θ : ℝ) : ℂ) * Complex.I) * B).re =
      Real.pi * ((if ξ.2 = ζ.2 then A * starRingEnd ℂ B else 0) *
          Complex.exp (((2 * Real.pi * ((ξ.1 - ζ.1 : ℤ) : ℝ) * σ : ℝ) : ℂ) * Complex.I)).re +
        Real.pi * ((if ξ.2 = -ζ.2 then A * B else 0) *
          Complex.exp (((2 * Real.pi * ((ξ.1 + ζ.1 : ℤ) : ℝ) * σ : ℝ) : ℂ) * Complex.I)).re := by
  have hpt : ∀ θ : ℝ,
      (Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) * A).re *
        (Complex.exp (((2 * Real.pi * ζ.1 * σ + ζ.2 * θ : ℝ) : ℂ) * Complex.I) * B).re =
      (A * starRingEnd ℂ B *
          Complex.exp (((2 * Real.pi * ((ξ.1 - ζ.1 : ℤ) : ℝ) * σ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((((ξ.2 - ζ.2 : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I)).re / 2 +
      (A * B *
          Complex.exp (((2 * Real.pi * ((ξ.1 + ζ.1 : ℤ) : ℝ) * σ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((((ξ.2 + ζ.2 : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I)).re / 2 := by
    intro θ
    rw [re_mul_re_eq, phase_mul_conj, phase_mul_phase]
    have e1 : (2 * Real.pi * ξ.1 * σ + ξ.2 * θ) - (2 * Real.pi * ζ.1 * σ + ζ.2 * θ) =
        2 * Real.pi * ((ξ.1 - ζ.1 : ℤ) : ℝ) * σ + ((ξ.2 - ζ.2 : ℤ) : ℝ) * θ := by
      push_cast
      ring
    have e2 : (2 * Real.pi * ξ.1 * σ + ξ.2 * θ) + (2 * Real.pi * ζ.1 * σ + ζ.2 * θ) =
        2 * Real.pi * ((ξ.1 + ζ.1 : ℤ) : ℝ) * σ + ((ξ.2 + ζ.2 : ℤ) : ℝ) * θ := by
      push_cast
      ring
    rw [e1, e2, exp_phase_add, exp_phase_add, ← mul_assoc, ← mul_assoc]
  simp_rw [hpt]
  have hint : ∀ (c : ℂ) (ω : ℝ), IntervalIntegrable
      (fun θ : ℝ => (c * Complex.exp (((ω * θ : ℝ) : ℂ) * Complex.I)).re / 2) volume 0 (2 * Real.pi) :=
    fun c ω => (by fun_prop : Continuous fun θ : ℝ =>
      (c * Complex.exp (((ω * θ : ℝ) : ℂ) * Complex.I)).re / 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hint _ _) (hint _ _), intervalIntegral.integral_div,
    intervalIntegral.integral_div,
    integral_re_exp_full_period _ _ (ξ.2 - ζ.2) (by ring),
    integral_re_exp_full_period _ _ (ξ.2 + ζ.2) (by ring)]
  have c1 : (((ξ.2 - ζ.2 : ℤ) : ℝ) = 0) ↔ ξ.2 = ζ.2 := by
    rw [Int.cast_eq_zero, sub_eq_zero]
  have c2 : (((ξ.2 + ζ.2 : ℤ) : ℝ) = 0) ↔ ξ.2 = -ζ.2 := by
    rw [Int.cast_eq_zero, eq_neg_iff_add_eq_zero]
  simp only [c1, c2]
  split_ifs <;> simp <;> ring

theorem mean_of_components (ξ ζ : ℤ × ℤ) (A B : ℂ) :
    Real.pi * (if 2 * Real.pi * ((ξ.1 - ζ.1 : ℤ) : ℝ) = 0 then
        1 * ((if ξ.2 = ζ.2 then A * starRingEnd ℂ B else 0)).re else 0) +
      Real.pi * (if 2 * Real.pi * ((ξ.1 + ζ.1 : ℤ) : ℝ) = 0 then
        1 * ((if ξ.2 = -ζ.2 then A * B else 0)).re else 0) =
      Real.pi * ((if ξ = ζ then A * starRingEnd ℂ B else 0) + (if ξ = -ζ then A * B else 0)).re := by
  have c1 : (2 * Real.pi * ((ξ.1 - ζ.1 : ℤ) : ℝ) = 0) ↔ ξ.1 = ζ.1 := by
    rw [mul_eq_zero, Int.cast_eq_zero, sub_eq_zero]
    simp [Real.pi_ne_zero]
  have c2 : (2 * Real.pi * ((ξ.1 + ζ.1 : ℤ) : ℝ) = 0) ↔ ξ.1 = -ζ.1 := by
    rw [mul_eq_zero, Int.cast_eq_zero, eq_neg_iff_add_eq_zero]
    simp [Real.pi_ne_zero]
  have d1 : ξ = ζ ↔ ξ.1 = ζ.1 ∧ ξ.2 = ζ.2 := Prod.ext_iff
  have d2 : ξ = -ζ ↔ ξ.1 = -ζ.1 ∧ ξ.2 = -ζ.2 := Prod.ext_iff
  simp only [c1, c2, d1, d2, Complex.add_re]
  simp only [ite_and, one_mul, apply_ite Complex.re, Complex.zero_re]
  ring

end Internal

open Internal in
theorem modeProduct_mean (ξ ζ : ℤ × ℤ) (A B : ℂ) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) * A).re *
        (Complex.exp (((2 * Real.pi * ζ.1 * σ + ζ.2 * θ : ℝ) : ℂ) * Complex.I) * B).re =
      Real.pi * ((if ξ = ζ then A * starRingEnd ℂ B else 0) + (if ξ = -ζ then A * B else 0)).re := by
  simp_rw [angle_mean ξ ζ A B]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hint : ∀ (c : ℂ) (ω : ℝ), IntervalIntegrable
      (fun σ : ℝ => Real.pi * (c * Complex.exp (((ω * σ : ℝ) : ℂ) * Complex.I)).re) volume 0 1 :=
    fun c ω => (by fun_prop : Continuous fun σ : ℝ =>
      Real.pi * (c * Complex.exp (((ω * σ : ℝ) : ℂ) * Complex.I)).re).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hint _ _) (hint _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_re_exp_full_period _ _ (ξ.1 - ζ.1) (by ring),
    integral_re_exp_full_period _ _ (ξ.1 + ζ.1) (by ring)]
  exact mean_of_components ξ ζ A B

end Instance

end CertCell

end Breakdown
