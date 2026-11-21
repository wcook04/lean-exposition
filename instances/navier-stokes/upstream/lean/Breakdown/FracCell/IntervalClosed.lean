import Breakdown.FracCell.StSpectral
import Breakdown.FracCell.IntervalClosedBounds

open MeasureTheory Polynomial
open scoped Interval

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

namespace Internal

namespace IntervalClosedCut

def clampUnit (x : ℝ) : ℝ := max (-1) (min 1 x)

lemma clampUnit_mem (x : ℝ) : clampUnit x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clampUnit_eq {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : clampUnit x = x := by
  unfold clampUnit
  rw [min_eq_right hx.2, max_eq_right hx.1]

lemma clampUnit_slope : LipschitzWith 1 clampUnit :=
  (LipschitzWith.id.const_min 1).const_max (-1)

lemma slope_eval_clamp (P : ℝ[X]) : ∃ K, LipschitzWith K (fun x => P.eval (clampUnit x)) := by
  have hc : ContDiff ℝ 1 (fun x : ℝ => P.eval x) := by
    simpa using P.contDiff_aeval (𝕜 := ℝ) 1
  obtain ⟨K, hK⟩ := hc.contDiffOn.exists_lipschitzOnWith (s := Set.Icc (-1 : ℝ) 1)
    one_ne_zero (convex_Icc _ _) isCompact_Icc
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  calc dist (P.eval (clampUnit x)) (P.eval (clampUnit y)) ≤ K * dist (clampUnit x) (clampUnit y) :=
        hK.dist_le_mul _ (clampUnit_mem x) _ (clampUnit_mem y)
    _ ≤ K * dist x y := by
        gcongr
        simpa using clampUnit_slope.dist_le_mul x y

lemma deriv_eval_clamp (P : ℝ[X]) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun y => P.eval (clampUnit y)) x = (derivative P).eval x := by
  have h : (fun y => P.eval (clampUnit y)) =ᶠ[nhds x] fun y => P.eval y := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    rw [clampUnit_eq (Set.Ioo_subset_Icc_self hy)]
  rw [h.deriv_eq, Polynomial.deriv]

lemma integral_deriv_clamp_sq (P : ℝ[X]) :
    (∫ x in (-1 : ℝ)..1, deriv (fun y => P.eval (clampUnit y)) x ^ 2)
      = ∫ x in (-1 : ℝ)..1, (derivative P).eval x ^ 2 := by
  apply intervalIntegral.integral_congr_ae
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [h1] with x hx hmem
  rw [Set.uIoc_of_le (by norm_num)] at hmem
  rw [deriv_eval_clamp P ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩]

lemma integral_pow_unit (n : ℕ) : (∫ x in (-1 : ℝ)..1, x ^ (2 * n)) = 2 / (2 * n + 1) := by
  rw [integral_pow]
  have h : ((-1 : ℝ)) ^ (2 * n + 1) = -1 := Odd.neg_one_pow ⟨n, rfl⟩
  rw [h]
  push_cast
  ring

lemma pow_unit_bounds (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ x ^ (2 * k + 2) ∧ x ^ (2 * k + 2) ≤ 1 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
  exact ⟨pow_nonneg (sq_nonneg x) _, pow_le_one₀ (sq_nonneg x) hx2⟩

lemma eval_derivative_cut (k : ℕ) (p : ℝ[X]) (x : ℝ) :
    (derivative ((1 - X ^ (2 * k + 2)) * p)).eval x
      = (1 - x ^ (2 * k + 2)) * (derivative p).eval x - (2 * k + 2) * x ^ (2 * k + 1) * p.eval x := by
  simp [derivative_mul]
  ring

lemma integral_derivative_eval (F : ℝ[X]) :
    (∫ x in (-1 : ℝ)..1, (derivative F).eval x) = F.eval 1 - F.eval (-1) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => F.hasDerivAt x)
    ((Polynomial.continuous _).intervalIntegrable _ _)

lemma cut_identity (k : ℕ) (p : ℝ[X]) (x : ℝ) :
    (derivative ((1 - X ^ (2 * k + 2)) * p)).eval x ^ 2
      = (1 - x ^ (2 * k + 2)) ^ 2 * (derivative p).eval x ^ 2
        + (2 * k + 2) * (2 * k + 1) * (x ^ (2 * k) - x ^ (2 * (2 * k + 1))) * p.eval x ^ 2
        + (derivative ((1 - X ^ (2 * k + 2)) * derivative (1 - X ^ (2 * k + 2)) * p ^ 2)).eval x := by
  simp [derivative_mul, derivative_pow]
  ring

lemma cut_boundary (k : ℕ) (p : ℝ[X]) :
    ((1 - X ^ (2 * k + 2)) * derivative (1 - X ^ (2 * k + 2)) * p ^ 2).eval 1
      - ((1 - X ^ (2 * k + 2)) * derivative (1 - X ^ (2 * k + 2)) * p ^ 2).eval (-1) = 0 := by
  simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X, one_pow, sub_self, zero_mul]
  rw [Even.neg_one_pow ⟨k + 1, by ring⟩]
  ring

lemma cut_constant (k : ℕ) (s : ℝ) (hs0 : 0 < s) (hmle : (k : ℝ) + 1 ≤ s / 2)
    (hmlt : s / 2 < (k : ℝ) + 1 + 1) :
    2 / (4 * (k : ℝ) + 5) + 8 * ((k : ℝ) + 1) ^ 2 / ((4 * k + 3) * s ^ 2) ≤ 4 / Real.sqrt 3 * s⁻¹ := by
  have hK0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd5 : (0 : ℝ) < 4 * k + 5 := by positivity
  have hd3 : (0 : ℝ) < 4 * k + 3 := by positivity
  have hsq3 : Real.sqrt 3 ≤ 40 / 23 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hsq3p : 0 < Real.sqrt 3 := by positivity
  have h4 : (23 : ℝ) / 10 ≤ 4 / Real.sqrt 3 := by
    rw [le_div_iff₀ hsq3p]
    linarith
  have ha : 0 ≤ s - (2 * k + 2) := by linarith
  have hb : 0 ≤ (2 * k + 4) - s := by linarith
  have hfa : 2 * (4 * (k : ℝ) + 3) * (2 * k + 2) ^ 2 - 23 / 10 * (4 * k + 5) * (4 * k + 3) * (2 * k + 2)
      + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5) ≤ 0 := by
    nlinarith [mul_nonneg hK0 hK0, mul_nonneg (mul_nonneg hK0 hK0) hK0]
  have hfb : 2 * (4 * (k : ℝ) + 3) * (2 * k + 4) ^ 2 - 23 / 10 * (4 * k + 5) * (4 * k + 3) * (2 * k + 4)
      + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5) ≤ 0 := by
    nlinarith [mul_nonneg hK0 hK0, mul_nonneg (mul_nonneg hK0 hK0) hK0]
  have hf : 2 * (4 * (k : ℝ) + 3) * s ^ 2 - 23 / 10 * (4 * k + 5) * (4 * k + 3) * s
      + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5) ≤ 0 := by
    have hq : 0 ≤ (s - (2 * k + 2)) * ((2 * k + 4) - s) := mul_nonneg ha hb
    have e : 2 * (2 * (4 * (k : ℝ) + 3) * s ^ 2 - 23 / 10 * (4 * k + 5) * (4 * k + 3) * s
        + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5))
        = ((2 * k + 4) - s) * (2 * (4 * (k : ℝ) + 3) * (2 * k + 2) ^ 2
            - 23 / 10 * (4 * k + 5) * (4 * k + 3) * (2 * k + 2) + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5))
          + (s - (2 * k + 2)) * (2 * (4 * (k : ℝ) + 3) * (2 * k + 4) ^ 2
            - 23 / 10 * (4 * k + 5) * (4 * k + 3) * (2 * k + 4) + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5))
          - 4 * (4 * k + 3) * ((s - (2 * k + 2)) * ((2 * k + 4) - s)) := by ring
    have t1 := mul_nonpos_of_nonneg_of_nonpos hb hfa
    have t2 := mul_nonpos_of_nonneg_of_nonpos ha hfb
    have t3 : 0 ≤ 4 * (4 * (k : ℝ) + 3) * ((s - (2 * k + 2)) * ((2 * k + 4) - s)) := by positivity
    linarith
  have hlhs : 2 / (4 * (k : ℝ) + 5) + 8 * ((k : ℝ) + 1) ^ 2 / ((4 * k + 3) * s ^ 2)
      = (2 * (4 * k + 3) * s ^ 2 + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5)) / ((4 * k + 5) * (4 * k + 3) * s ^ 2) := by
    field_simp
  rw [hlhs, div_le_iff₀ (by positivity)]
  calc 2 * (4 * (k : ℝ) + 3) * s ^ 2 + 8 * ((k : ℝ) + 1) ^ 2 * (4 * k + 5)
      ≤ 23 / 10 * s⁻¹ * ((4 * k + 5) * (4 * k + 3) * s ^ 2) := by
        rw [show 23 / 10 * s⁻¹ * ((4 * k + 5) * (4 * k + 3) * s ^ 2) = 23 / 10 * (4 * k + 5) * (4 * k + 3) * s by
          field_simp]
        linarith
    _ ≤ 4 / Real.sqrt 3 * s⁻¹ * ((4 * k + 5) * (4 * k + 3) * s ^ 2) := by gcongr

lemma cut_algebra (Q N K s : ℝ) (hs : 0 < s) (hK : 0 ≤ K) :
    Q ^ 2 * N * (2 / (2 * (2 * K + 2) + 1))
        + (s ^ 2)⁻¹ * (Q ^ 4 / 2 * N
          + Q ^ 2 * N * ((2 * K + 2) * (2 * K + 1) * (2 / (2 * K + 1) - 2 / (2 * (2 * K + 1) + 1))))
      = Q ^ 2 * N * (2 / (4 * K + 5) + 8 * (K + 1) ^ 2 / ((4 * K + 3) * s ^ 2)) + 1 / 2 * Q ^ 4 * (s ^ 2)⁻¹ * N := by
  have h5 : 4 * K + 5 ≠ 0 := by positivity
  have h3 : 4 * K + 3 ≠ 0 := by positivity
  have h1 : 2 * K + 1 ≠ 0 := by positivity
  have h5' : 2 * (2 * K + 2) + 1 ≠ 0 := by positivity
  have h3' : 2 * (2 * K + 1) + 1 ≠ 0 := by positivity
  have hs' : s ≠ 0 := hs.ne'
  field_simp
  ring

end IntervalClosedCut

end Internal

open Internal.IntervalClosedCut IntervalClosedBounds

theorem intervalClosed_of (_h1 : IntervalIdentityStatement) (h2 : IntervalMinimalStatement) :
    IntervalClosedStatement := by
  intro q μ p hμ hp
  set N := ∫ x in (-1 : ℝ)..1, p.eval x ^ 2 with hN
  have hN0 : 0 ≤ N := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  set Q : ℝ := (q : ℝ) + 1 with hQ
  have hQ1 : 1 ≤ Q := by simp [hQ]
  set s := Real.sqrt μ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hμ
  have hss : s ^ 2 = μ := Real.sq_sqrt hμ.le
  have hr : μ ^ (-(1 / 2 : ℝ)) = s⁻¹ := by rw [Real.rpow_neg hμ.le, ← Real.sqrt_eq_rpow]
  have hsq3 : Real.sqrt 3 ≤ 15 / 8 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hsq3p : 0 < Real.sqrt 3 := by positivity
  unfold intervalClosed
  rw [hr]
  by_cases hsmall : μ < 4
  · have hV := h2 μ p hμ (fun _ => 0) ⟨0, LipschitzWith.const 0⟩ rfl rfl
    simp only [sub_zero, deriv_const', ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      intervalIntegral.integral_zero, mul_zero, add_zero] at hV
    have hs2 : s < 2 := by nlinarith
    have hinv : (1 : ℝ) / 2 ≤ s⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hs0 hs2.le
    have hc : 1 ≤ 4 / Real.sqrt 3 * Q ^ 2 * s⁻¹ + 1 / 2 * Q ^ 4 * μ⁻¹ := by
      have hQ2 : 1 ≤ Q ^ 2 := one_le_pow₀ hQ1
      have h43 : 2 ≤ 4 / Real.sqrt 3 := by
        rw [le_div_iff₀ hsq3p]
        linarith
      have ht : 0 ≤ 1 / 2 * Q ^ 4 * μ⁻¹ := by positivity
      have : 1 ≤ 4 / Real.sqrt 3 * Q ^ 2 * s⁻¹ := by
        calc (1 : ℝ) = 2 * 1 * (1 / 2) := by norm_num
          _ ≤ 4 / Real.sqrt 3 * Q ^ 2 * s⁻¹ := by gcongr
      linarith
    calc _ ≤ N := hV
      _ ≤ _ := le_mul_of_one_le_left hN0 hc
  · rw [not_lt] at hsmall
    have hs2 : 2 ≤ s := by
      rw [hs]
      calc (2 : ℝ) = Real.sqrt 4 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ Real.sqrt μ := Real.sqrt_le_sqrt hsmall
    set m := ⌊s / 2⌋₊ with hm
    have hm1 : 1 ≤ m := Nat.le_floor (by simp; linarith)
    have hmle : (m : ℝ) ≤ s / 2 := Nat.floor_le (by positivity)
    have hmlt : s / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hm1
    rw [hk] at hmle hmlt
    push_cast at hmle hmlt
    obtain ⟨P, hP⟩ : ∃ P : ℝ[X], P = (1 - X ^ (2 * k + 2)) * p := ⟨_, rfl⟩
    have hV := h2 μ p hμ (fun x => P.eval (clampUnit x)) (slope_eval_clamp P)
      (by
        rw [clampUnit_eq (by norm_num), hP]
        simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X]
        rw [Even.neg_one_pow ⟨k + 1, by ring⟩]
        ring)
      (by
        rw [clampUnit_eq (by norm_num), hP]
        simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X, one_pow]
        ring)
    rw [integral_deriv_clamp_sq P] at hV
    have hS : ∀ x ∈ Set.Icc (-1 : ℝ) 1, p.eval x ^ 2 ≤ Q ^ 2 * N := fun x hx => sq_eval_le q p hp x hx
    have hD : (∫ x in (-1 : ℝ)..1, (derivative p).eval x ^ 2) ≤ Q ^ 4 / 2 * N :=
      integral_derivative_sq_le q p hp
    have hA : (∫ x in (-1 : ℝ)..1, (p.eval x - P.eval (clampUnit x)) ^ 2)
        ≤ Q ^ 2 * N * (2 / (2 * ((2 * k + 2 : ℕ) : ℝ) + 1)) := by
      calc (∫ x in (-1 : ℝ)..1, (p.eval x - P.eval (clampUnit x)) ^ 2)
          = ∫ x in (-1 : ℝ)..1, x ^ (2 * (2 * k + 2)) * p.eval x ^ 2 := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le (by norm_num)] at hx
            simp only [clampUnit_eq hx, hP, eval_mul, eval_sub, eval_one, eval_pow, eval_X]
            rw [pow_mul]
            ring
        _ ≤ ∫ x in (-1 : ℝ)..1, x ^ (2 * (2 * k + 2)) * (Q ^ 2 * N) := by
            apply intervalIntegral.integral_mono_on (by norm_num)
            · exact ((continuous_pow _).mul ((Polynomial.continuous p).pow 2)).intervalIntegrable _ _
            · exact ((continuous_pow _).mul continuous_const).intervalIntegrable _ _
            intro x hx
            have h0 : 0 ≤ x ^ (2 * (2 * k + 2)) := by rw [pow_mul]; positivity
            exact mul_le_mul_of_nonneg_left (hS x hx) h0
        _ = _ := by
            rw [intervalIntegral.integral_mul_const, integral_pow_unit]
            ring
    have hB : (∫ x in (-1 : ℝ)..1, (derivative P).eval x ^ 2)
        ≤ Q ^ 4 / 2 * N + Q ^ 2 * N * ((2 * k + 2) * (2 * k + 1)
            * (2 / (2 * (k : ℝ) + 1) - 2 / (2 * ((2 * k + 1 : ℕ) : ℝ) + 1))) := by
      have hF := integral_derivative_eval ((1 - X ^ (2 * k + 2)) * derivative (1 - X ^ (2 * k + 2)) * p ^ 2)
      rw [cut_boundary] at hF
      have hc1 : Continuous fun x : ℝ => (1 - x ^ (2 * k + 2)) ^ 2 * (derivative p).eval x ^ 2
          + (2 * k + 2) * (2 * k + 1) * (x ^ (2 * k) - x ^ (2 * (2 * k + 1))) * p.eval x ^ 2 := by
        fun_prop
      calc (∫ x in (-1 : ℝ)..1, (derivative P).eval x ^ 2)
          = (∫ x in (-1 : ℝ)..1, ((1 - x ^ (2 * k + 2)) ^ 2 * (derivative p).eval x ^ 2
              + (2 * k + 2) * (2 * k + 1) * (x ^ (2 * k) - x ^ (2 * (2 * k + 1))) * p.eval x ^ 2))
            + ∫ x in (-1 : ℝ)..1, (derivative ((1 - X ^ (2 * k + 2)) * derivative (1 - X ^ (2 * k + 2))
                * p ^ 2)).eval x := by
            rw [← intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
              ((Polynomial.continuous _).intervalIntegrable _ _)]
            apply intervalIntegral.integral_congr
            intro x _
            rw [hP]
            exact cut_identity k p x
        _ = ∫ x in (-1 : ℝ)..1, ((1 - x ^ (2 * k + 2)) ^ 2 * (derivative p).eval x ^ 2
              + (2 * k + 2) * (2 * k + 1) * (x ^ (2 * k) - x ^ (2 * (2 * k + 1))) * p.eval x ^ 2) := by
            rw [hF, add_zero]
        _ ≤ ∫ x in (-1 : ℝ)..1, ((derivative p).eval x ^ 2
              + (2 * k + 2) * (2 * k + 1) * (Q ^ 2 * N) * (x ^ (2 * k) - x ^ (2 * (2 * k + 1)))) := by
            apply intervalIntegral.integral_mono_on (by norm_num) (hc1.intervalIntegrable _ _)
            · exact (((Polynomial.continuous _).pow 2).add
                (continuous_const.mul ((continuous_pow _).sub (continuous_pow _)))).intervalIntegrable _ _
            intro x hx
            obtain ⟨hc0, hc1'⟩ := pow_unit_bounds k hx
            have hpx := hS x hx
            have hw : 0 ≤ x ^ (2 * k) - x ^ (2 * (2 * k + 1)) := by
              have e : x ^ (2 * (2 * k + 1)) = x ^ (2 * k) * x ^ (2 * k + 2) := by ring
              have h2k : 0 ≤ x ^ (2 * k) := by rw [pow_mul]; positivity
              rw [e]
              nlinarith
            have hk : (0 : ℝ) ≤ (2 * k + 2) * (2 * k + 1) := by positivity
            have e1 : (1 - x ^ (2 * k + 2)) ^ 2 * (derivative p).eval x ^ 2 ≤ (derivative p).eval x ^ 2 := by
              have : (1 - x ^ (2 * k + 2)) ^ 2 ≤ 1 := by nlinarith
              nlinarith [sq_nonneg ((derivative p).eval x)]
            have e2 : (2 * k + 2) * (2 * k + 1) * (x ^ (2 * k) - x ^ (2 * (2 * k + 1))) * p.eval x ^ 2
                ≤ (2 * k + 2) * (2 * k + 1) * (x ^ (2 * k) - x ^ (2 * (2 * k + 1))) * (Q ^ 2 * N) :=
              mul_le_mul_of_nonneg_left hpx (mul_nonneg hk hw)
            linarith
        _ ≤ _ := by
            rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub,
              integral_pow_unit, integral_pow_unit]
            · linarith [hD]
            · exact (continuous_pow _).intervalIntegrable _ _
            · exact (continuous_pow _).intervalIntegrable _ _
            · exact ((Polynomial.continuous _).pow 2).intervalIntegrable _ _
            · exact (continuous_const.mul ((continuous_pow _).sub (continuous_pow _))).intervalIntegrable _ _
    rw [← hQ]
    push_cast at hA hB
    have hK0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hQN : 0 ≤ Q ^ 2 * N := by positivity
    have hmu : μ⁻¹ = (s ^ 2)⁻¹ := by rw [hss]
    have hmu0 : 0 ≤ μ⁻¹ := by positivity
    have hc := cut_constant k s hs0 hmle hmlt
    calc _ ≤ _ := hV
      _ ≤ Q ^ 2 * N * (2 / (2 * (2 * (k : ℝ) + 2) + 1))
          + μ⁻¹ * (Q ^ 4 / 2 * N + Q ^ 2 * N * ((2 * k + 2) * (2 * k + 1)
            * (2 / (2 * (k : ℝ) + 1) - 2 / (2 * (2 * k + 1) + 1)))) := by
          gcongr
      _ = Q ^ 2 * N * (2 / (4 * (k : ℝ) + 5) + 8 * ((k : ℝ) + 1) ^ 2 / ((4 * k + 3) * s ^ 2))
          + 1 / 2 * Q ^ 4 * μ⁻¹ * N := by
          rw [hmu]
          exact cut_algebra Q N k s hs0 hK0
      _ ≤ Q ^ 2 * N * (4 / Real.sqrt 3 * s⁻¹) + 1 / 2 * Q ^ 4 * μ⁻¹ * N := by
          gcongr
      _ = _ := by ring

end Spectral

end CellCert

end Breakdown
