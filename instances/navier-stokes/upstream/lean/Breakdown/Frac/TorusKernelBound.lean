import Breakdown.Frac.StTorusBasic
import Breakdown.Torus.Trilinear
import Breakdown.Torus.TrigHs
import Breakdown.Torus.KernelBound

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace FracInternal.KernelSharp

open Internal.KernelEstimate

theorem factor_pos (α τ : ℝ) (k : Lattice) : 0 < fracLatticeFactor α τ k := Real.exp_pos _

theorem factor_le_one (α τ : ℝ) (k : Lattice) : fracLatticeFactor α τ k ≤ 1 := by
  rw [fracLatticeFactor, Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_max_right _ _)

theorem le_one_add_rpow {α y : ℝ} (hα : 1 ≤ α) (hy : 0 ≤ y) : y ≤ 1 + y ^ α := by
  rcases le_total y 1 with h | h
  · have := Real.rpow_nonneg hy α
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hα
    rw [Real.rpow_one] at this
    linarith

theorem sq_mul_rpow_le {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 ≤ τ) (s : ℝ) (hs : 0 ≤ s) :
    s ^ 2 * τ ^ α⁻¹ ≤ 1 + s ^ (2 * α) * τ := by
  have hα0 : 0 < α := by linarith
  have h1 := le_one_add_rpow hα (mul_nonneg (sq_nonneg s) (Real.rpow_nonneg hτ α⁻¹))
  have e : (s ^ 2 * τ ^ α⁻¹) ^ α = s ^ (2 * α) * τ := by
    rw [Real.mul_rpow (sq_nonneg s) (Real.rpow_nonneg hτ _), Real.rpow_inv_rpow hτ hα0.ne',
      Real.rpow_mul hs, Real.rpow_two]
  rw [e] at h1
  exact h1

theorem factor_eq {α τ : ℝ} (hτ : 0 ≤ τ) (k : Lattice) :
    fracLatticeFactor α τ k = Real.exp (-((2 * π * ‖freq k‖) ^ (2 * α) * τ)) := by
  rw [fracLatticeFactor, max_eq_left hτ]

theorem weight_eq (k : Lattice) : weight k = 1 + (2 * π * ‖freq k‖) ^ 2 := by
  rw [weight]
  ring

theorem scaled_weight_factor_le {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : Lattice) :
    τ ^ α⁻¹ * (weight k * fracLatticeFactor α τ k) ≤ 2 := by
  have hα0 : 0 < α := by linarith
  have hs0 : 0 ≤ 2 * π * ‖freq k‖ := by positivity
  have hy := sq_mul_rpow_le hα hτ.le _ hs0
  have ht : τ ^ α⁻¹ ≤ 1 := Real.rpow_le_one hτ.le hτ1 (inv_nonneg.mpr hα0.le)
  have hx0 : 0 ≤ (2 * π * ‖freq k‖) ^ (2 * α) * τ :=
    mul_nonneg (Real.rpow_nonneg hs0 _) hτ.le
  have hE := Real.add_one_le_exp ((2 * π * ‖freq k‖) ^ (2 * α) * τ)
  rw [weight_eq, factor_eq hτ.le]
  have hm : τ ^ α⁻¹ * (1 + (2 * π * ‖freq k‖) ^ 2) ≤
      2 * Real.exp ((2 * π * ‖freq k‖) ^ (2 * α) * τ) := by
    nlinarith
  calc τ ^ α⁻¹ * ((1 + (2 * π * ‖freq k‖) ^ 2) *
        Real.exp (-((2 * π * ‖freq k‖) ^ (2 * α) * τ)))
      = (τ ^ α⁻¹ * (1 + (2 * π * ‖freq k‖) ^ 2)) *
        Real.exp (-((2 * π * ‖freq k‖) ^ (2 * α) * τ)) := by ring
    _ ≤ (2 * Real.exp ((2 * π * ‖freq k‖) ^ (2 * α) * τ)) *
        Real.exp (-((2 * π * ‖freq k‖) ^ (2 * α) * τ)) :=
        mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ = 2 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem weight_factor_le {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : Lattice) :
    weight k * fracLatticeFactor α τ k ≤ 2 * τ ^ (-α⁻¹) := by
  have h := scaled_weight_factor_le hα hτ hτ1 k
  have hp : 0 < τ ^ α⁻¹ := Real.rpow_pos_of_pos hτ _
  rw [Real.rpow_neg hτ.le, ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
  exact h

theorem factor_le_heat {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 < τ) (k : Lattice) :
    fracLatticeFactor α τ k ≤ Real.exp 1 * heatFactor (τ ^ α⁻¹) k := by
  have hs0 : 0 ≤ 2 * π * ‖freq k‖ := by positivity
  have hy := sq_mul_rpow_le hα hτ.le _ hs0
  rw [factor_eq hτ.le, heatFactor, max_eq_left (Real.rpow_nonneg hτ.le _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have e : (2 * π * ‖freq k‖) ^ 2 = 4 * π ^ 2 * ‖freq k‖ ^ 2 := by ring
  rw [e] at hy
  linarith

theorem summable_factor {α τ : ℝ} (hα : 1 ≤ α) (hτ : 0 < τ) :
    Summable (fracLatticeFactor α τ) :=
  (((summable_heatFactor (Real.rpow_pos_of_pos hτ α⁻¹)).mul_left (Real.exp 1))).of_nonneg_of_le
    (fun k => (factor_pos α τ k).le) (fun k => factor_le_heat hα hτ k)

def fracTest (α τ : ℝ) (c : Lattice → Coef) (k : Lattice) : Coef :=
  (weight k * (-(1 / 2) * fracLatticeFactor α τ k)) • c k

theorem norm_fracTest (α τ : ℝ) (c : Lattice → Coef) (k : Lattice) :
    ‖fracTest α τ c k‖ = (1 / 2) * weight k * fracLatticeFactor α τ k * ‖c k‖ := by
  have h0 : 0 ≤ (1 / 2) * weight k * fracLatticeFactor α τ k :=
    mul_nonneg (mul_nonneg (by norm_num) (weight_pos k).le) (factor_pos α τ k).le
  rw [fracTest, norm_smul, Real.norm_eq_abs,
    show weight k * (-(1 / 2) * fracLatticeFactor α τ k) =
      -((1 / 2) * weight k * fracLatticeFactor α τ k) by ring,
    abs_neg, abs_of_nonneg h0]

theorem summable_norm_fracTest {α τ A : ℝ} (hα : 1 ≤ α) (hτ : 0 < τ)
    (hwF : ∀ k, weight k * fracLatticeFactor α τ k ≤ A) (c : Lattice → Coef)
    (hc : Summable (fun k => weight k * ‖c k‖ ^ 2)) :
    Summable (fun k => ‖fracTest α τ c k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((((summable_factor hα hτ).mul_left A).mul_left (1 / 4)).add (hc.mul_left (1 / 4)))
  have h1 := mul_le_mul_of_nonneg_right (hwF k) (factor_pos α τ k).le
  have hw := (weight_pos k).le
  have h2 := mul_nonneg hw (sq_nonneg (fracLatticeFactor α τ k - ‖c k‖))
  rw [norm_fracTest]
  nlinarith

theorem fracTest_sq_le {α τ A : ℝ} (hwF : ∀ k, weight k * fracLatticeFactor α τ k ≤ A)
    (c : Lattice → Coef) (k : Lattice) :
    ‖fracTest α τ c k‖ ^ 2 ≤ A * (weight k * ‖c k‖ ^ 2) := by
  have hX : 0 ≤ weight k * ‖c k‖ ^ 2 := mul_nonneg (weight_pos k).le (sq_nonneg _)
  have hF0 := (factor_pos α τ k).le
  have hF1 := factor_le_one α τ k
  have hwF0 : 0 ≤ weight k * fracLatticeFactor α τ k := mul_nonneg (weight_pos k).le hF0
  have hA : 0 ≤ A := hwF0.trans (hwF k)
  have h1 : weight k * fracLatticeFactor α τ k * fracLatticeFactor α τ k ≤ A :=
    (mul_le_mul (hwF k) hF1 hF0 hA).trans (le_of_eq (mul_one A))
  rw [norm_fracTest]
  calc ((1 / 2) * weight k * fracLatticeFactor α τ k * ‖c k‖) ^ 2
      = (1 / 4) * (weight k * fracLatticeFactor α τ k * fracLatticeFactor α τ k) *
        (weight k * ‖c k‖ ^ 2) := by ring
    _ ≤ (1 / 4) * A * (weight k * ‖c k‖ ^ 2) := by
        gcongr
    _ ≤ A * (weight k * ‖c k‖ ^ 2) := by nlinarith

theorem weight_fracTest_sq_le {α τ A : ℝ} (hwF : ∀ k, weight k * fracLatticeFactor α τ k ≤ A)
    (c : Lattice → Coef) (k : Lattice) :
    weight k * ‖fracTest α τ c k‖ ^ 2 ≤ A ^ 2 * (weight k * ‖c k‖ ^ 2) := by
  have hX : 0 ≤ weight k * ‖c k‖ ^ 2 := mul_nonneg (weight_pos k).le (sq_nonneg _)
  have hwF0 : 0 ≤ weight k * fracLatticeFactor α τ k :=
    mul_nonneg (weight_pos k).le (factor_pos α τ k).le
  have h1 : (weight k * fracLatticeFactor α τ k) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ hwF0 (hwF k) 2
  rw [norm_fracTest]
  calc weight k * ((1 / 2) * weight k * fracLatticeFactor α τ k * ‖c k‖) ^ 2
      = (1 / 4) * (weight k * fracLatticeFactor α τ k) ^ 2 * (weight k * ‖c k‖ ^ 2) := by ring
    _ ≤ (1 / 4) * A ^ 2 * (weight k * ‖c k‖ ^ 2) := by gcongr
    _ ≤ A ^ 2 * (weight k * ‖c k‖ ^ 2) := by nlinarith [sq_nonneg A]

theorem rpow_combine_gen {A N : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N) :
    (A * N ^ 2) ^ (1 / 4 : ℝ) * (A ^ 2 * N ^ 2) ^ (1 / 4 : ℝ) = A ^ (3 / 4 : ℝ) * N := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  have e : A * N ^ 2 * (A ^ 2 * N ^ 2) = (A ^ (3 / 4 : ℝ) * N) ^ (4 : ℕ) := by
    rw [mul_pow, ← Real.rpow_natCast (A ^ (3 / 4 : ℝ)), ← Real.rpow_mul hA,
      show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [e, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]

theorem norm_kernel_diag_le {α : ℝ} (hα : 1 ≤ α) (hK : FracTorusKernelAlgebra α) (C : ℝ)
    (hC : 0 < C)
    (hT : ∀ (u v : V) (φ : Lattice → Coef),
      Summable (fun k => ‖φ k‖) → Summable (fun k => weight k * ‖φ k‖ ^ 2) →
      ‖∑' k, inner ℂ (φ k) (advCoef u v k)‖ ≤
        C * ‖u‖ * ‖v‖ * (∑' k, ‖φ k‖ ^ 2) ^ (1 / 4 : ℝ) *
          (∑' k, weight k * ‖φ k‖ ^ 2) ^ (1 / 4 : ℝ))
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (u : V) :
    ‖fracTorusKernel α τ u u‖ ≤ 2 * (C * (2 * τ ^ (-α⁻¹)) ^ (3 / 4 : ℝ)) * ‖u‖ ^ 2 := by
  have hwF : ∀ k, weight k * fracLatticeFactor α τ k ≤ 2 * τ ^ (-α⁻¹) :=
    fun k => weight_factor_le hα hτ hτ1 k
  have hA : 0 ≤ 2 * τ ^ (-α⁻¹) := by
    have := Real.rpow_pos_of_pos hτ (-α⁻¹)
    positivity
  set A := 2 * τ ^ (-α⁻¹) with hAdef
  set K := fracTorusKernel α τ u u with hKdef
  have hXs := summable_weight_coeff K
  have hN := norm_sq_eq_tsum K
  have hterm : ∀ k, inner ℂ (fracTest α τ (coeff K) k) (advCoef u u k) =
      (((1 / 2) * (weight k * ‖coeff K k‖ ^ 2) : ℝ) : ℂ) := by
    intro k
    rw [fracTest, hKdef, hK.1 τ u u k, fracTorusKernelCoef, if_pos hτ]
    exact inner_term _ _ _ _
  have hsum : ∑' k, inner ℂ (fracTest α τ (coeff K) k) (advCoef u u k) =
      (((1 / 2) * ‖K‖ ^ 2 : ℝ) : ℂ) := by
    rw [tsum_congr hterm, ← Complex.ofReal_tsum, tsum_mul_left, hN]
  have hS2s : Summable (fun k => weight k * ‖fracTest α τ (coeff K) k‖ ^ 2) :=
    (hXs.mul_left (A ^ 2)).of_nonneg_of_le
      (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _))
      (fun k => weight_fracTest_sq_le hwF _ k)
  have hb := hT u u (fracTest α τ (coeff K))
    (summable_norm_fracTest hα hτ hwF _ hXs) hS2s
  rw [hsum, Complex.norm_of_nonneg (by positivity)] at hb
  have hN0 : 0 ≤ ‖K‖ := norm_nonneg _
  have hS1 : ∑' k, ‖fracTest α τ (coeff K) k‖ ^ 2 ≤ A * ‖K‖ ^ 2 := by
    rw [hN, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun k => fracTest_sq_le hwF _ k)
      ((hXs.mul_left A).of_nonneg_of_le (fun k => sq_nonneg _)
        (fun k => fracTest_sq_le hwF _ k)) (hXs.mul_left A)
  have hS2 : ∑' k, weight k * ‖fracTest α τ (coeff K) k‖ ^ 2 ≤ A ^ 2 * ‖K‖ ^ 2 := by
    rw [hN, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun k => weight_fracTest_sq_le hwF _ k) hS2s
      (hXs.mul_left (A ^ 2))
  have hS1' := Real.rpow_le_rpow (tsum_nonneg (fun k => sq_nonneg _)) hS1
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hS2' := Real.rpow_le_rpow
    (tsum_nonneg (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _))) hS2
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hprod := mul_le_mul hS1' hS2' (Real.rpow_nonneg
    (tsum_nonneg (fun k => mul_nonneg (weight_pos k).le (sq_nonneg _))) _)
    (Real.rpow_nonneg (by positivity) _)
  rw [rpow_combine_gen hA hN0] at hprod
  have hK0 : 0 ≤ C * ‖u‖ * ‖u‖ := by positivity
  have hmain : (1 / 2) * ‖K‖ ^ 2 ≤ (C * ‖u‖ * ‖u‖ * A ^ (3 / 4 : ℝ)) * ‖K‖ := by
    calc (1 / 2) * ‖K‖ ^ 2 ≤ _ := hb
      _ = C * ‖u‖ * ‖u‖ * ((∑' k, ‖fracTest α τ (coeff K) k‖ ^ 2) ^ (1 / 4 : ℝ) *
            (∑' k, weight k * ‖fracTest α τ (coeff K) k‖ ^ 2) ^ (1 / 4 : ℝ)) := by
          ring
      _ ≤ C * ‖u‖ * ‖u‖ * (A ^ (3 / 4 : ℝ) * ‖K‖) :=
          mul_le_mul_of_nonneg_left hprod hK0
      _ = (C * ‖u‖ * ‖u‖ * A ^ (3 / 4 : ℝ)) * ‖K‖ := by ring
  have hAp : 0 ≤ A ^ (3 / 4 : ℝ) := Real.rpow_nonneg hA _
  have h2 := le_two_mul_of_half_sq_le (by positivity) hmain
  calc ‖K‖ ≤ 2 * (C * ‖u‖ * ‖u‖ * A ^ (3 / 4 : ℝ)) := h2
    _ = 2 * (C * A ^ (3 / 4 : ℝ)) * ‖u‖ ^ 2 := by ring

theorem rpow_constant_le {α τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) :
    (2 * τ ^ (-α⁻¹)) ^ (3 / 4 : ℝ) ≤ 2 * τ ^ (-(3 / (4 * α))) := by
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hτ.le _), ← Real.rpow_mul hτ.le,
    show -α⁻¹ * (3 / 4 : ℝ) = -(3 / (4 * α)) by field_simp]
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (3 / 4 : ℝ) ≤ 1)
    rwa [Real.rpow_one] at this
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hτ.le _)

end FracInternal.KernelSharp

open FracInternal.KernelSharp Internal.KernelEstimate in
theorem fracTorusKernelSharpBound_of (α : ℝ) (h1 : 1 < α) (hK : FracTorusKernelAlgebra α) :
    FracTorusKernelSharpBound α := by
  obtain ⟨C, hC, hT⟩ := trilinearBound trigHs
  refine ⟨8 * C, by positivity, fun τ hτ hτ1 => ?_⟩
  have hα0 : 0 < α := by linarith
  have hD : 0 ≤ 2 * (C * (2 * τ ^ (-α⁻¹)) ^ (3 / 4 : ℝ)) := by
    have := Real.rpow_pos_of_pos hτ (-α⁻¹)
    positivity
  have hB := norm_le_of_diag (hK.2.1 τ) hD
    (fun u => norm_kernel_diag_le h1.le hK C hC hT hτ hτ1 u)
  have hc := rpow_constant_le hα0 hτ
  calc ‖fracTorusKernel α τ‖ ≤ 2 * (2 * (C * (2 * τ ^ (-α⁻¹)) ^ (3 / 4 : ℝ))) := hB
    _ ≤ 2 * (2 * (C * (2 * τ ^ (-(3 / (4 * α)))))) := by gcongr
    _ = 8 * C * τ ^ (-(3 / (4 * α))) := by ring

end Breakdown.Periodic
