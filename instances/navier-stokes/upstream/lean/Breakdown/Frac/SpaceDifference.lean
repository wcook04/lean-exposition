import Breakdown.Frac.StSpace
import Breakdown.Uniqueness.SimpleTerms
import Breakdown.Uniqueness.CubicTerm
import Breakdown.Uniqueness.MixedStress
import Breakdown.Uniqueness.SelfStress

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracDifferenceInternal

theorem cube_mul_le_fourth {M x z : ℝ} (hM : 0 ≤ M) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    M * x ^ 3 * z ≤ x ^ 4 + M ^ 4 * z ^ 4 := by
  have hy : 0 ≤ M * z := mul_nonneg hM hz
  have h := mul_nonneg (sq_nonneg (x - M * z))
    (by positivity : (0 : ℝ) ≤ 3 * x ^ 2 + 2 * x * (M * z) + (M * z) ^ 2)
  nlinarith [pow_nonneg hx 4, pow_nonneg hy 4]

theorem pow_three_le_sum (A : ℝ) : A ^ 3 ≤ A ^ 2 + A ^ 6 := by
  nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg (A ^ 2 - 1 / 2)),
    mul_nonneg (sq_nonneg A) (sq_nonneg (A - 1 / 2)), sq_nonneg A]

theorem pow_four_le_sum (A : ℝ) : A ^ 4 ≤ A ^ 2 + A ^ 6 := by
  nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg (A ^ 2 - 1 / 2)), sq_nonneg A]

theorem rpow_three_halves_eq {y : ℝ} (hy : 0 ≤ y) : y ^ (3 / 2 : ℝ) = √y ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

theorem cubic_absorb {D A r s S C : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hs : 0 ≤ s) (hS : 0 ≤ S) (hC : 0 ≤ C) (hso : s ≤ S * (A + √D)) :
    C * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) ≤
      D / 8 + (4 * C * √S ^ 3 * A ^ 3 + 8 ^ 3 * (4 * C * √S ^ 3) ^ 4 * A ^ 6) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  rw [rpow_three_halves_eq hs, rpow_three_halves_eq hA]
  have hσ0 := Real.sqrt_nonneg s
  have ha0 := Real.sqrt_nonneg A
  have hτ0 := Real.sqrt_nonneg (√D)
  have hL0 := Real.sqrt_nonneg S
  have hσ2 : √s ^ 2 = s := Real.sq_sqrt hs
  have ha2 : √A ^ 2 = A := Real.sq_sqrt hA
  have ht2 : √(√D) ^ 2 = √D := Real.sq_sqrt (Real.sqrt_nonneg D)
  have hD2 : √D ^ 2 = D := Real.sq_sqrt hD
  have hL2 : √S ^ 2 = S := Real.sq_sqrt hS
  set σ := √s
  set a := √A
  set τ := √(√D)
  set L := √S
  have hτ4 : τ ^ 4 = D := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ht2, hD2]
  have ha6 : a ^ 6 = A ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, ha2]
  have ha12 : a ^ 12 = A ^ 6 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, ha2]
  have hB0 : 0 ≤ L * (a + τ) := mul_nonneg hL0 (add_nonneg ha0 hτ0)
  have hsq : σ ^ 2 ≤ (L * (a + τ)) ^ 2 := by
    have e : (L * (a + τ)) ^ 2 = L ^ 2 * (a ^ 2 + τ ^ 2) + 2 * L ^ 2 * (a * τ) := by ring
    rw [e, hσ2, hL2, ha2, ht2]
    have : 0 ≤ 2 * S * (a * τ) := by positivity
    linarith
  have hσ : σ ≤ L * (a + τ) := by
    by_contra h
    rw [not_le] at h
    nlinarith [mul_lt_mul'' h h hB0 hB0]
  have hσ3 : σ ^ 3 ≤ (L * (a + τ)) ^ 3 := pow_le_pow_left₀ hσ0 hσ 3
  have hcube : (a + τ) ^ 3 ≤ 4 * (a ^ 3 + τ ^ 3) := by
    nlinarith [mul_nonneg (add_nonneg ha0 hτ0) (sq_nonneg (a - τ))]
  have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL0 3
  have ha3 : 0 ≤ a ^ 3 := pow_nonneg ha0 3
  have hprod : σ ^ 3 * a ^ 3 ≤ 4 * L ^ 3 * a ^ 6 + 4 * L ^ 3 * τ ^ 3 * a ^ 3 := by
    have h1 : σ ^ 3 * a ^ 3 ≤ (L * (a + τ)) ^ 3 * a ^ 3 := mul_le_mul_of_nonneg_right hσ3 ha3
    have h2 : (L * (a + τ)) ^ 3 * a ^ 3 ≤ L ^ 3 * (4 * (a ^ 3 + τ ^ 3)) * a ^ 3 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube hL3) ha3
    have e : L ^ 3 * (4 * (a ^ 3 + τ ^ 3)) * a ^ 3 = 4 * L ^ 3 * a ^ 6 + 4 * L ^ 3 * τ ^ 3 * a ^ 3 := by
      ring
    linarith
  set M := 4 * C * L ^ 3 with hMdef
  have hM : 0 ≤ M := by positivity
  have hZ : 0 ≤ a ^ 3 / r := div_nonneg ha3 hr0.le
  have hy := cube_mul_le_fourth (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hM) hτ0 hZ
  have hZ4 : (a ^ 3 / r) ^ 4 = A ^ 6 / r ^ 4 := by
    rw [div_pow, ← pow_mul, show 3 * 4 = 12 from rfl, ha12]
  have hr4 : r ≤ r ^ 4 := by
    have h1 : 1 ≤ r ^ 3 := one_le_pow₀ hr
    nlinarith
  have hA6 : A ^ 6 / r ^ 4 ≤ A ^ 6 / r :=
    div_le_div_of_nonneg_left (by positivity) hr0 hr4
  have hProductBound : M * τ ^ 3 * (a ^ 3 / r) ≤ D / 8 + 8 ^ 3 * M ^ 4 * (A ^ 6 / r) := by
    have e : (8 * M) ^ 4 = 8 * (8 ^ 3 * M ^ 4) := by ring
    rw [e, hZ4, hτ4] at hy
    have hM4 : 0 ≤ 8 ^ 3 * M ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left hA6 hM4
    nlinarith
  have hCr : C * (σ ^ 3 * a ^ 3 / r) ≤ C * ((4 * L ^ 3 * a ^ 6 + 4 * L ^ 3 * τ ^ 3 * a ^ 3) / r) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hprod hr0.le) hC
  have e2 : C * ((4 * L ^ 3 * a ^ 6 + 4 * L ^ 3 * τ ^ 3 * a ^ 3) / r) =
      M * A ^ 3 / r + M * τ ^ 3 * (a ^ 3 / r) := by
    rw [hMdef, ha6.symm]; ring
  have e3 : (M * A ^ 3 + 8 ^ 3 * M ^ 4 * A ^ 6) / r = M * A ^ 3 / r + 8 ^ 3 * M ^ 4 * (A ^ 6 / r) := by
    ring
  rw [e3]
  linarith

theorem quad_absorb {D A r s S c ρ : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hS : 0 ≤ S) (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / r) (hso : s ≤ S * (A + √D)) :
    c * (A ^ 2 * s * ρ) ≤ D / 8 + (c * S * A ^ 3 + 2 * c ^ 2 * S ^ 2 * A ^ 4) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hir : 1 / r ≤ 1 := by rw [div_le_one hr0]; exact hr
  have hρ1 : ρ ≤ 1 := hρ.trans hir
  have ht := Real.sqrt_nonneg D
  have hD2 : √D ^ 2 = D := Real.sq_sqrt hD
  have step1 : c * (A ^ 2 * s * ρ) ≤ c * (A ^ 2 * ρ) * (S * (A + √D)) := by
    calc c * (A ^ 2 * s * ρ) = c * (A ^ 2 * ρ) * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hso (by positivity)
  set b := c * S * A ^ 2 * ρ
  have hb : b * √D ≤ √D ^ 2 / 8 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (√D - 4 * b)]
  have hρ2 : ρ ^ 2 ≤ 1 / r := by nlinarith
  have hb2 : b ^ 2 ≤ c ^ 2 * S ^ 2 * A ^ 4 / r := by
    calc b ^ 2 = c ^ 2 * S ^ 2 * A ^ 4 * ρ ^ 2 := by ring
      _ ≤ c ^ 2 * S ^ 2 * A ^ 4 * (1 / r) := mul_le_mul_of_nonneg_left hρ2 (by positivity)
      _ = c ^ 2 * S ^ 2 * A ^ 4 / r := by ring
  have h3 : c * S * A ^ 3 * ρ ≤ c * S * A ^ 3 * (1 / r) :=
    mul_le_mul_of_nonneg_left hρ (by positivity)
  calc c * (A ^ 2 * s * ρ) ≤ c * (A ^ 2 * ρ) * (S * (A + √D)) := step1
    _ = c * S * A ^ 3 * ρ + b * √D := by ring
    _ ≤ c * S * A ^ 3 * (1 / r) + (√D ^ 2 / 8 + 2 * (c ^ 2 * S ^ 2 * A ^ 4 / r)) := by linarith
    _ = _ := by rw [hD2]; ring

theorem integrable_transport {r : ℝ} (hr : 0 < r) {v w : Space → Space}
    (hv : Continuous v) (hw : Continuous w) :
    Integrable (fun x => ‖w x‖ ^ 2 * inner ℝ (v x) (gradientAt (cutoffPow r) x)) := by
  have hcd : ContDiff ℝ ∞ (cutoffPow r) := (contDiff_radialCutoff hr).pow 4
  have hcs : HasCompactSupport (cutoffPow r) :=
    (hasCompactSupport_radialCutoff hr).mono fun x hx h0 => hx (by simp [cutoffPow, h0])
  have hf := hcd.continuous_fderiv (by simp)
  have hG : Continuous (gradientAt (cutoffPow r)) := by
    show Continuous (fun x => ∑ i : Fin 3, fderiv ℝ (cutoffPow r) x (unitVector i) • unitVector i)
    exact continuous_finsetSum _ fun i _ => (hf.clm_apply continuous_const).smul continuous_const
  have hGs : HasCompactSupport (gradientAt (cutoffPow r)) :=
    (hcs.fderiv (𝕜 := ℝ)).mono fun x hx h0 => hx (by simp [gradientAt, h0])
  exact Continuous.integrable_of_hasCompactSupport ((hw.norm.pow 2).mul (hv.inner hG))
    (hGs.mono fun x hx h0 => hx (by simp [h0]))

theorem combine_bounds {I D s E A U₀ U₁ r S C0 c2 c3 c4 c5 T Tu Tw St SS M1 M2 ρ σ : ℝ}
    (hr : 1 ≤ r) (hA : 0 ≤ A) (hU : 0 ≤ U₀) (hD : 0 ≤ D) (hs : 0 ≤ s) (hS : 0 ≤ S)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / r) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / r)
    (hso : s ≤ S * (A + √D)) (hI : (3 / 4) * D - C0 * A ^ 2 / r ^ 2 ≤ I)
    (hTu : |Tu| ≤ c2 * U₀ * A ^ 2 / r)
    (hTw : |Tw| ≤ c3 * s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) (hSt : |St| ≤ 2 * U₁ * E)
    (hSS : |SS| ≤ c4 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ))
    (hM : |M1 + M2| ≤ c5 * U₀ * A ^ 2 / r) (hT : T = Tu + Tw) :
    -I + T - St - (SS + M1 + M2) ≤
      2 * U₁ * E + (|C0| + |c2| + |c5| + |c4| + 4 * (|c3| + |c4|) * √S ^ 3 +
        8 ^ 3 * (4 * (|c3| + |c4|) * √S ^ 3) ^ 4 + |c4| * S + 2 * |c4| ^ 2 * S ^ 2) *
        (1 + U₀) * (A ^ 2 + A ^ 6) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hP : 0 ≤ s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by positivity
  have hQ : 0 ≤ s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ := by positivity
  have hC : 0 ≤ |c3| + |c4| := by positivity
  have hcub := cubic_absorb hD hA hr hs hS hC hso
  have hquad := quad_absorb hD hA hr hS (abs_nonneg c4) hρ0 hρ hso
  have hTw' : |Tw| ≤ |c3| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by
    calc |Tw| ≤ c3 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by
          rw [← mul_div_assoc, ← mul_assoc]; exact hTw
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self c3) hP
  have hSS' := hSS.trans (mul_le_mul_of_nonneg_right (le_abs_self c4) hQ)
  have hrr : r ≤ r ^ 2 := by nlinarith
  have hI' : C0 * A ^ 2 / r ^ 2 ≤ |C0| * A ^ 2 / r := by
    calc C0 * A ^ 2 / r ^ 2 ≤ |C0| * A ^ 2 / r ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C0) (sq_nonneg A))
            (by positivity)
      _ ≤ |C0| * A ^ 2 / r := div_le_div_of_nonneg_left (by positivity) hr0 hrr
  have hTu' : c2 * U₀ * A ^ 2 / r ≤ |c2| * U₀ * A ^ 2 / r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self c2) hU) (sq_nonneg A)) hr0.le
  have hM' : c5 * U₀ * A ^ 2 / r ≤ |c5| * U₀ * A ^ 2 / r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self c5) hU) (sq_nonneg A)) hr0.le
  have hσ' : |c4| * (A ^ 3 * σ) ≤ |c4| * A ^ 3 / r := by
    calc |c4| * (A ^ 3 * σ) ≤ |c4| * (A ^ 3 * (1 / r)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hσ (by positivity)) (abs_nonneg c4)
      _ = |c4| * A ^ 3 / r := by ring
  set k1 := 4 * (|c3| + |c4|) * √S ^ 3
  set k2 := 8 ^ 3 * (4 * (|c3| + |c4|) * √S ^ 3) ^ 4
  have hk1 : 0 ≤ k1 := by positivity
  have hk2 : 0 ≤ k2 := by positivity
  have hN : |C0| * A ^ 2 + |c2| * U₀ * A ^ 2 + |c5| * U₀ * A ^ 2 + |c4| * A ^ 3 +
      (k1 * A ^ 3 + k2 * A ^ 6) + (|c4| * S * A ^ 3 + 2 * |c4| ^ 2 * S ^ 2 * A ^ 4) ≤
      (|C0| + |c2| + |c5| + |c4| + k1 + k2 + |c4| * S + 2 * |c4| ^ 2 * S ^ 2) *
        (1 + U₀) * (A ^ 2 + A ^ 6) := by
    have h3 := pow_three_le_sum A
    have h4 := pow_four_le_sum A
    have hA2 : A ^ 2 ≤ A ^ 2 + A ^ 6 := le_add_of_nonneg_right (by positivity)
    have hA6 : A ^ 6 ≤ A ^ 2 + A ^ 6 := le_add_of_nonneg_left (by positivity)
    have hW : 0 ≤ A ^ 2 + A ^ 6 := by positivity
    have e1 := mul_le_mul_of_nonneg_left hA2 (abs_nonneg C0)
    have e2 := mul_le_mul_of_nonneg_left hA2 (mul_nonneg (abs_nonneg c2) hU)
    have e3 := mul_le_mul_of_nonneg_left hA2 (mul_nonneg (abs_nonneg c5) hU)
    have e4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg c4)
    have e5 := mul_le_mul_of_nonneg_left h3 hk1
    have e6 := mul_le_mul_of_nonneg_left hA6 hk2
    have e7 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ |c4| * S)
    have e8 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * |c4| ^ 2 * S ^ 2)
    have f1 : 0 ≤ |C0| * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f2 : 0 ≤ |c2| * (A ^ 2 + A ^ 6) := by positivity
    have f3 : 0 ≤ |c5| * (A ^ 2 + A ^ 6) := by positivity
    have f4 : 0 ≤ |c4| * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f5 : 0 ≤ k1 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f6 : 0 ≤ k2 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f7 : 0 ≤ |c4| * S * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f8 : 0 ≤ 2 * |c4| ^ 2 * S ^ 2 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    linarith
  have hNr := div_le_div_of_nonneg_right hN hr0.le
  have hNsplit : (|C0| * A ^ 2 + |c2| * U₀ * A ^ 2 + |c5| * U₀ * A ^ 2 + |c4| * A ^ 3 +
      (k1 * A ^ 3 + k2 * A ^ 6) + (|c4| * S * A ^ 3 + 2 * |c4| ^ 2 * S ^ 2 * A ^ 4)) / r =
      |C0| * A ^ 2 / r + |c2| * U₀ * A ^ 2 / r + |c5| * U₀ * A ^ 2 / r + |c4| * A ^ 3 / r +
      (k1 * A ^ 3 + k2 * A ^ 6) / r +
      (|c4| * S * A ^ 3 + 2 * |c4| ^ 2 * S ^ 2 * A ^ 4) / r := by ring
  have hlin : |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ) =
      |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) + |c4| * (A ^ 2 * s * ρ) +
        |c4| * (A ^ 3 * σ) := by ring
  have hlin2 : (|c3| + |c4|) * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) =
      |c3| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) +
        |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by ring
  have a1 := neg_abs_le SS
  have a2 := neg_abs_le (M1 + M2)
  have a4 := le_abs_self Tu
  have a5 := le_abs_self Tw
  have a6 := neg_abs_le St
  rw [hT]
  linarith

end FracDifferenceInternal

open FracDifferenceInternal in
theorem fracDifference_of (h1 : FracCutoffLowerBoundStatement) (h2 : FracSixthNormStatement)
    (h3 : FracGradientBoundStatement) : FracDifferenceStatement := by
  intro α hα1 hα2
  obtain ⟨r₀, C0, hr₀, hlow⟩ := h1 α hα1 hα2
  obtain ⟨S, hS, hsix⟩ := h2 α hα1 (by linarith)
  obtain ⟨c2, htr⟩ := transport_term_le
  obtain ⟨c3, hcub⟩ := cubic_term_le
  obtain ⟨c5, hmix⟩ := mixed_stress_le
  obtain ⟨c4, hself⟩ := self_stress_le
  refine ⟨|C0| + |c2| + |c5| + |c4| + 4 * (|c3| + |c4|) * √S ^ 3 +
      8 ^ 3 * (4 * (|c3| + |c4|) * √S ^ 3) ^ 4 + |c4| * S + 2 * |c4| ^ 2 * S ^ 2, r₀, hr₀, ?_⟩
  intro A U₀ U₁ u w hd r hr
  have hr1 : 1 ≤ r := hr₀.trans hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hWs : ContDiff ℝ ∞ (fun y => radialCutoff r y ^ 2 • w y) :=
    ((contDiff_radialCutoff hr0).pow 2).smul hd.field.smooth
  have hWc : HasCompactSupport (fun y => radialCutoff r y ^ 2 • w y) :=
    (hasCompactSupport_radialCutoff hr0).mono fun x hx h0 => hx (by simp [h0])
  have hD : 0 ≤ cutoffFracDissipation α r w := (h3 α hα1 (by linarith) _ hWs hWc).1
  have hs : 0 ≤ cutoffSixthNorm r w := Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  have hρ : r ^ (-(3 / 2) : ℝ) ≤ 1 / r := by
    rw [one_div, ← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
  have hσ : r ^ (-(5 / 2) : ℝ) ≤ 1 / r := by
    rw [one_div, ← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
  have hsplit : (1 / 2) * (∫ x, ‖w x‖ ^ 2 * inner ℝ (u x + w x) (gradientAt (cutoffPow r) x)) =
      (1 / 2) * (∫ x, ‖w x‖ ^ 2 * inner ℝ (u x) (gradientAt (cutoffPow r) x)) +
        (1 / 2) * ∫ x, ‖w x‖ ^ 2 * inner ℝ (w x) (gradientAt (cutoffPow r) x) := by
    rw [← mul_add, ← integral_add
      (integrable_transport hr0 hd.smooth_u.continuous hd.field.smooth.continuous)
      (integrable_transport hr0 hd.field.smooth.continuous hd.field.smooth.continuous)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [inner_add_left, mul_add]
  unfold fracDifferenceRHS
  exact combine_bounds hr1 hd.field.nonneg ((norm_nonneg _).trans (hd.bound_u 0)) hD hs hS
    (Real.rpow_nonneg hr0.le _) hρ (Real.rpow_nonneg hr0.le _) hσ (hsix A w hd.field r hr1)
    (hlow w hd.field.smooth A hd.field.nonneg hd.field.energy r hr)
    (htr A U₀ U₁ u w hd r hr1) (hcub A w hd.field r hr1)
    (stretching_term_le A U₀ U₁ u w hd r hr0) (hself A w hd.field r hr1)
    (hmix A U₀ U₁ u w hd r hr1) hsplit

end Breakdown
