import Breakdown.CertTorus.KernelStatements

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

open Freq

namespace HeatKernelEstimate.Internal

theorem poly_mul_gaussian_le (a s : ℝ) (hs : 0 < s) :
    (a + s) ^ 10 * Real.exp (-(a ^ 2) / (4 * s ^ 2)) ≤ 40 ^ 5 * s ^ 10 := by
  set u := a ^ 2 / (4 * s ^ 2) with hu
  have hs2 : 0 < s ^ 2 := by positivity
  have hau : a ^ 2 = 4 * s ^ 2 * u := by rw [hu]; field_simp
  have h1 : (a + s) ^ 2 ≤ 40 * s ^ 2 * (1 + u / 5) := by
    nlinarith [sq_nonneg (a - s)]
  have h2 : 1 + u / 5 ≤ Real.exp (u / 5) := by linarith [Real.add_one_le_exp (u / 5)]
  have he : Real.exp (u / 5) ^ 5 = Real.exp u := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : (a + s) ^ 10 ≤ 40 ^ 5 * s ^ 10 * Real.exp u := by
    calc (a + s) ^ 10 = ((a + s) ^ 2) ^ 5 := by ring
      _ ≤ (40 * s ^ 2 * Real.exp (u / 5)) ^ 5 := by
        apply pow_le_pow_left₀ (sq_nonneg _)
        calc (a + s) ^ 2 ≤ 40 * s ^ 2 * (1 + u / 5) := h1
          _ ≤ 40 * s ^ 2 * Real.exp (u / 5) := by gcongr
      _ = 40 ^ 5 * s ^ 10 * Real.exp u := by rw [mul_pow, he]; ring
  have hneg : -(a ^ 2) / (4 * s ^ 2) = -u := by rw [hu]; ring
  rw [hneg]
  calc (a + s) ^ 10 * Real.exp (-u) ≤ 40 ^ 5 * s ^ 10 * Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = 40 ^ 5 * s ^ 10 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem pow_mul_gaussian_le (a s : ℝ) (ha : 0 ≤ a) (hs : 0 < s) (m : ℕ) (hm : m ≤ 10) :
    (a + s) ^ m * Real.exp (-(a ^ 2) / (4 * s ^ 2)) ≤ 40 ^ 5 * s ^ m := by
  have hle : (a + s) ^ m * s ^ (10 - m) ≤ (a + s) ^ 10 := by
    calc (a + s) ^ m * s ^ (10 - m) ≤ (a + s) ^ m * (a + s) ^ (10 - m) := by
          gcongr; linarith
      _ = (a + s) ^ 10 := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hE := (Real.exp_pos (-(a ^ 2) / (4 * s ^ 2))).le
  have key : (a + s) ^ m * Real.exp (-(a ^ 2) / (4 * s ^ 2)) * s ^ (10 - m) ≤
      40 ^ 5 * s ^ m * s ^ (10 - m) := by
    calc (a + s) ^ m * Real.exp (-(a ^ 2) / (4 * s ^ 2)) * s ^ (10 - m)
        = (a + s) ^ m * s ^ (10 - m) * Real.exp (-(a ^ 2) / (4 * s ^ 2)) := by ring
      _ ≤ (a + s) ^ 10 * Real.exp (-(a ^ 2) / (4 * s ^ 2)) := mul_le_mul_of_nonneg_right hle hE
      _ ≤ 40 ^ 5 * s ^ 10 := poly_mul_gaussian_le a s hs
      _ = 40 ^ 5 * s ^ m * s ^ (10 - m) := by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  exact le_of_mul_le_mul_right key (pow_pos hs _)

theorem heatKernel_eq (τ : ℝ) (hτ : 0 < τ) (x : Space) :
    heatKernel τ x = ((4 * π) ^ (3 / 2 : ℝ))⁻¹ * (√τ ^ 3)⁻¹ *
      Real.exp (-(‖x‖ ^ 2) / (4 * √τ ^ 2)) := by
  have h32 : τ ^ (3 / 2 : ℝ) = √τ ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hτ.le]; norm_num
  unfold heatKernel
  rw [Real.sq_sqrt hτ.le, Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) hτ.le, h32,
    mul_inv]

theorem coord_abs_le (x : Space) (k : Fin 3) : |x k| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x k
  rwa [Real.norm_eq_abs] at this

theorem ite_abs_le (p : Prop) [Decidable p] (x : Space) (k : Fin 3) :
    |(if p then x k else 0)| ≤ ‖x‖ := by
  split_ifs
  · exact coord_abs_le x k
  · simp

end HeatKernelEstimate.Internal

open HeatKernelEstimate.Internal in
theorem heatKernelBounds_holds : HeatKernelBounds := by
  refine ⟨((4 * π) ^ (3 / 2 : ℝ))⁻¹ * 40 ^ 5, fun τ hτ x => ?_⟩
  set c := ((4 * π) ^ (3 / 2 : ℝ))⁻¹ with hc
  have hc0 : 0 < c := by positivity
  set s := √τ with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hτ
  have hτs : τ = s ^ 2 := (Real.sq_sqrt hτ.le).symm
  set a := ‖x‖ with hadef
  have ha : 0 ≤ a := norm_nonneg x
  set E := Real.exp (-(a ^ 2) / (4 * s ^ 2)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hΓ : heatKernel τ x = c * (s ^ 3)⁻¹ * E := heatKernel_eq τ hτ x
  have hB : ∀ m : ℕ, m ≤ 10 → (a + s) ^ m * E ≤ 40 ^ 5 * s ^ m :=
    fun m hm => pow_mul_gaussian_le a s ha hs m hm
  have has : 0 < a + s := by linarith
  have hΓ0 : 0 ≤ heatKernel τ x := by rw [hΓ]; positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity), hΓ]
    have h3 := hB 3 (by norm_num)
    calc c * (s ^ 3)⁻¹ * E * (a + s) ^ 3 = c * ((a + s) ^ 3 * E) * (s ^ 3)⁻¹ := by ring
      _ ≤ c * (40 ^ 5 * s ^ 3) * (s ^ 3)⁻¹ := by gcongr
      _ = c * 40 ^ 5 := by field_simp
  · intro k
    rw [le_div_iff₀ (by positivity)]
    have h5 := hB 5 (by norm_num)
    have hk := coord_abs_le x k
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * τ), abs_of_nonneg hΓ0, hΓ, hτs]
    calc |x k| / (2 * s ^ 2) * (c * (s ^ 3)⁻¹ * E) * (a + s) ^ 4
        ≤ (a + s) / (2 * s ^ 2) * (c * (s ^ 3)⁻¹ * E) * (a + s) ^ 4 := by
          gcongr; linarith
      _ = c / 2 * ((a + s) ^ 5 * E) * (s ^ 5)⁻¹ := by field_simp
      _ ≤ c / 2 * (40 ^ 5 * s ^ 5) * (s ^ 5)⁻¹ := by gcongr
      _ = c / 2 * 40 ^ 5 := by field_simp
      _ ≤ c * 40 ^ 5 := by nlinarith
  · intro i j k
    rw [le_div_iff₀ (by positivity)]
    have h7 := hB 7 (by norm_num)
    have h9 := hB 9 (by norm_num)
    have hS : |(if j = k then x i else 0) + (if i = k then x j else 0) + (if i = j then x k else 0)|
        ≤ 3 * (a + s) := by
      have := abs_add_three (if j = k then x i else 0) (if i = k then x j else 0)
        (if i = j then x k else 0)
      have e1 := ite_abs_le (j = k) x i
      have e2 := ite_abs_le (i = k) x j
      have e3 := ite_abs_le (i = j) x k
      linarith
    have hP : |x i * x j * x k| ≤ (a + s) ^ 3 := by
      rw [abs_mul, abs_mul]
      have e1 := coord_abs_le x i
      have e2 := coord_abs_le x j
      have e3 := coord_abs_le x k
      calc |x i| * |x j| * |x k| ≤ (a + s) * (a + s) * (a + s) := by
            gcongr <;> linarith
        _ = (a + s) ^ 3 := by ring
    unfold heatKernelThird
    rw [hΓ, hτs]
    set S := (if j = k then x i else 0) + (if i = k then x j else 0) + (if i = j then x k else 0)
    set P := x i * x j * x k
    have hG0 : 0 ≤ c * (s ^ 3)⁻¹ * E := by positivity
    calc |S / (4 * (s ^ 2) ^ 2) * (c * (s ^ 3)⁻¹ * E) - P / (8 * (s ^ 2) ^ 3) * (c * (s ^ 3)⁻¹ * E)|
          * (a + s) ^ 6
        ≤ (|S| / (4 * (s ^ 2) ^ 2) * (c * (s ^ 3)⁻¹ * E) + |P| / (8 * (s ^ 2) ^ 3) *
            (c * (s ^ 3)⁻¹ * E)) * (a + s) ^ 6 := by
          gcongr
          calc _ ≤ |S / (4 * (s ^ 2) ^ 2) * (c * (s ^ 3)⁻¹ * E)| +
                |P / (8 * (s ^ 2) ^ 3) * (c * (s ^ 3)⁻¹ * E)| := abs_sub _ _
            _ = _ := by
              congr 1
              · rw [abs_mul, abs_div, abs_of_nonneg hG0,
                  abs_of_pos (by positivity : (0:ℝ) < 4 * (s ^ 2) ^ 2)]
              · rw [abs_mul, abs_div, abs_of_nonneg hG0,
                  abs_of_pos (by positivity : (0:ℝ) < 8 * (s ^ 2) ^ 3)]
      _ ≤ (3 * (a + s) / (4 * (s ^ 2) ^ 2) * (c * (s ^ 3)⁻¹ * E) + (a + s) ^ 3 / (8 * (s ^ 2) ^ 3) *
            (c * (s ^ 3)⁻¹ * E)) * (a + s) ^ 6 := by gcongr
      _ = 3 / 4 * c * (((a + s) ^ 7 * E) * (s ^ 7)⁻¹) + 1 / 8 * c * (((a + s) ^ 9 * E) * (s ^ 9)⁻¹) := by
          field_simp
      _ ≤ 3 / 4 * c * ((40 ^ 5 * s ^ 7) * (s ^ 7)⁻¹) + 1 / 8 * c * ((40 ^ 5 * s ^ 9) * (s ^ 9)⁻¹) := by
          gcongr
      _ = 7 / 8 * (c * 40 ^ 5) := by field_simp; ring
      _ ≤ c * 40 ^ 5 := by nlinarith

end Breakdown.FarField
