import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem cube_mul_le_fourth {M x z : ℝ} (hM : 0 ≤ M) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    M * x ^ 3 * z ≤ x ^ 4 + M ^ 4 * z ^ 4 := by
  have hy : 0 ≤ M * z := mul_nonneg hM hz
  have h := mul_nonneg (sq_nonneg (x - M * z))
    (by positivity : (0 : ℝ) ≤ 3 * x ^ 2 + 2 * x * (M * z) + (M * z) ^ 2)
  nlinarith [pow_nonneg hx 4, pow_nonneg hy 4]

private theorem pow_three_le_sum (A : ℝ) : A ^ 3 ≤ A ^ 2 + A ^ 6 := by
  nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg (A ^ 2 - 1 / 2)),
    mul_nonneg (sq_nonneg A) (sq_nonneg (A - 1 / 2)), sq_nonneg A]

private theorem pow_four_le_sum (A : ℝ) : A ^ 4 ≤ A ^ 2 + A ^ 6 := by
  nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg (A ^ 2 - 1 / 2)), sq_nonneg A]

private theorem rpow_three_halves_eq {y : ℝ} (hy : 0 ≤ y) : y ^ (3 / 2 : ℝ) = √y ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

private theorem cubic_part_le {X A r s S c C : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hs : 0 ≤ s) (hS : 0 ≤ S) (hc : 0 ≤ c) (hC : 0 ≤ C) (hHs : s ≤ S * (√X + c * A / r)) :
    C * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) ≤
      X / 2 + (c ^ 2 / 2 * A ^ 2 + C ^ 4 * (4 * S ^ 2 + 1) ^ 3 * A ^ 6) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hq0 : 0 ≤ c * A / r := div_nonneg (mul_nonneg hc hA) hr0.le
  have hq : c * A / r ≤ c * A := div_le_self (mul_nonneg hc hA) hr
  have ha := Real.sqrt_nonneg X
  have hsX : √X ^ 2 = X := Real.sq_sqrt hX
  have hB : 0 ≤ S * (√X + c * A / r) := mul_nonneg hS (add_nonneg ha hq0)
  have hsB : s ^ (3 / 2 : ℝ) ≤ (S * (√X + c * A / r)) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hs hHs (by norm_num)
  rw [rpow_three_halves_eq hB] at hsB
  rw [rpow_three_halves_eq hA]
  have hx0 := Real.sqrt_nonneg (S * (√X + c * A / r))
  have hz0 : 0 ≤ √A ^ 3 := pow_nonneg (Real.sqrt_nonneg A) 3
  have hx4 : √(S * (√X + c * A / r)) ^ 4 = (S * (√X + c * A / r)) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hB]
  have hz4 : (√A ^ 3) ^ 4 = A ^ 6 := by
    rw [← pow_mul, show 3 * 4 = 2 * 6 from rfl, pow_mul, Real.sq_sqrt hA]
  have hk : 0 < 4 * S ^ 2 + 1 := by positivity
  have hy := cube_mul_le_fourth (mul_nonneg hC hk.le) hx0 hz0
  have hsq : (√X + c * A / r) ^ 2 ≤ 2 * (X + c ^ 2 * A ^ 2) := by
    nlinarith [sq_nonneg (√X - c * A / r), mul_le_mul hq hq hq0 (mul_nonneg hc hA)]
  have hB2 : (S * (√X + c * A / r)) ^ 2 ≤ 2 * S ^ 2 * (X + c ^ 2 * A ^ 2) := by
    calc (S * (√X + c * A / r)) ^ 2 = S ^ 2 * (√X + c * A / r) ^ 2 := by ring
      _ ≤ S ^ 2 * (2 * (X + c ^ 2 * A ^ 2)) := mul_le_mul_of_nonneg_left hsq (sq_nonneg S)
      _ = 2 * S ^ 2 * (X + c ^ 2 * A ^ 2) := by ring
  have hXA : 0 ≤ X + c ^ 2 * A ^ 2 := by positivity
  have hk2 := mul_le_mul_of_nonneg_right
    (show 2 * S ^ 2 ≤ (4 * S ^ 2 + 1) / 2 by linarith) hXA
  set x := √(S * (√X + c * A / r))
  set z := √A ^ 3
  set k := 4 * S ^ 2 + 1
  have hmain : C * (x ^ 3 * z) ≤ (X + c ^ 2 * A ^ 2) / 2 + C ^ 4 * k ^ 3 * A ^ 6 := by
    have h' : k * (C * (x ^ 3 * z)) ≤ k * ((X + c ^ 2 * A ^ 2) / 2 + C ^ 4 * k ^ 3 * A ^ 6) := by
      calc k * (C * (x ^ 3 * z)) = C * k * x ^ 3 * z := by ring
        _ ≤ x ^ 4 + (C * k) ^ 4 * z ^ 4 := hy
        _ = (S * (√X + c * A / r)) ^ 2 + C ^ 4 * k ^ 4 * A ^ 6 := by rw [hx4, mul_pow, hz4]; ring
        _ ≤ k / 2 * (X + c ^ 2 * A ^ 2) + C ^ 4 * k ^ 4 * A ^ 6 := by linarith
        _ = k * ((X + c ^ 2 * A ^ 2) / 2 + C ^ 4 * k ^ 3 * A ^ 6) := by ring
    exact le_of_mul_le_mul_left h' hk
  have hxz : s ^ (3 / 2 : ℝ) * z ≤ x ^ 3 * z := mul_le_mul_of_nonneg_right hsB hz0
  have h1 : C * (s ^ (3 / 2 : ℝ) * z / r) ≤
      ((X + c ^ 2 * A ^ 2) / 2 + C ^ 4 * k ^ 3 * A ^ 6) / r := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left hxz hC).trans hmain) hr0.le
  have h2 : X / 2 / r ≤ X / 2 := div_le_self (by positivity) hr
  calc C * (s ^ (3 / 2 : ℝ) * z / r) ≤ ((X + c ^ 2 * A ^ 2) / 2 + C ^ 4 * k ^ 3 * A ^ 6) / r := h1
    _ = X / 2 / r + (c ^ 2 / 2 * A ^ 2 + C ^ 4 * k ^ 3 * A ^ 6) / r := by ring
    _ ≤ _ := by linarith

private theorem quadratic_part_le {X A r s S c D ρ : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hS : 0 ≤ S) (hc : 0 ≤ c) (hD : 0 ≤ D) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / r)
    (hHs : s ≤ S * (√X + c * A / r)) :
    D * (A ^ 2 * s * ρ) ≤ X / 4 + (D ^ 2 * S ^ 2 * A ^ 4 + D * S * c * A ^ 3) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hir : 1 / r ≤ 1 := by rw [div_le_one hr0]; exact hr
  have hρ1 : ρ ≤ 1 := hρ.trans hir
  have ha := Real.sqrt_nonneg X
  have hsX : √X ^ 2 = X := Real.sq_sqrt hX
  have step1 : D * (A ^ 2 * s * ρ) ≤ D * (A ^ 2 * ρ) * (S * (√X + c * A / r)) := by
    calc D * (A ^ 2 * s * ρ) = D * (A ^ 2 * ρ) * s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hHs (by positivity)
  have hb : (D * S * A ^ 2 * ρ) * √X ≤ √X ^ 2 / 4 + (D * S * A ^ 2 * ρ) ^ 2 := by
    nlinarith [sq_nonneg (√X / 2 - D * S * A ^ 2 * ρ)]
  have hρ2 : ρ ^ 2 ≤ 1 / r := by nlinarith
  have hb2 : (D * S * A ^ 2 * ρ) ^ 2 ≤ D ^ 2 * S ^ 2 * A ^ 4 / r := by
    calc (D * S * A ^ 2 * ρ) ^ 2 = D ^ 2 * S ^ 2 * A ^ 4 * ρ ^ 2 := by ring
      _ ≤ D ^ 2 * S ^ 2 * A ^ 4 * (1 / r) := mul_le_mul_of_nonneg_left hρ2 (by positivity)
      _ = D ^ 2 * S ^ 2 * A ^ 4 / r := by ring
  have h3 : D * S * c * A ^ 3 * (ρ / r) ≤ D * S * c * A ^ 3 * (1 / r) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hρ1 hr0.le) (by positivity)
  calc D * (A ^ 2 * s * ρ) ≤ D * (A ^ 2 * ρ) * (S * (√X + c * A / r)) := step1
    _ = (D * S * A ^ 2 * ρ) * √X + D * S * c * A ^ 3 * (ρ / r) := by ring
    _ ≤ √X ^ 2 / 4 + D ^ 2 * S ^ 2 * A ^ 4 / r + D * S * c * A ^ 3 * (1 / r) := by linarith
    _ = _ := by rw [hsX]; ring

private theorem integrable_transport {r : ℝ} (hr : 0 < r) {v w : Space → Space}
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


private theorem combine_bounds {X s E A U₀ U₁ r S c c1 c2 c3 c4 c5 L T Tu Tw St SS M1 M2 ρ σ : ℝ}
    (hr : 1 ≤ r) (hA : 0 ≤ A) (hU : 0 ≤ U₀) (hX : 0 ≤ X) (hs : 0 ≤ s) (hS : 0 ≤ S) (hc : 0 ≤ c)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / r) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / r)
    (hso : s ≤ S * (√X + c * A / r)) (hL : |L| ≤ c1 * A ^ 2 / r) (hTu : |Tu| ≤ c2 * U₀ * A ^ 2 / r)
    (hTw : |Tw| ≤ c3 * s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) (hSt : |St| ≤ 2 * U₁ * E)
    (hSS : |SS| ≤ c4 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ))
    (hM : |M1 + M2| ≤ c5 * U₀ * A ^ 2 / r) (hT : T = Tu + Tw) :
    -X + L + T - St - (SS + M1 + M2) ≤
      2 * U₁ * E + (|c1| + |c2| + |c5| + |c4| + c ^ 2 / 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 +
      |c4| ^ 2 * S ^ 2 + |c4| * S * c) * (1 + U₀) * (A ^ 2 + A ^ 6) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hP : 0 ≤ s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by positivity
  have hQ : 0 ≤ s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ := by positivity
  have hC : 0 ≤ |c3| + |c4| := by positivity
  have hcub' := cubic_part_le hX hA hr hs hS hc hC hso
  have hquad := quadratic_part_le hX hA hr hS hc (abs_nonneg c4) hρ0 hρ hso
  have hTw' : |Tw| ≤ |c3| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by
    calc |Tw| ≤ c3 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by
          rw [← mul_div_assoc, ← mul_assoc]; exact hTw
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self c3) hP
  have hSS' := hSS.trans (mul_le_mul_of_nonneg_right (le_abs_self c4) hQ)
  have hL' : c1 * A ^ 2 / r ≤ |c1| * A ^ 2 / r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self c1) (sq_nonneg A)) hr0.le
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
  have hN : |c1| * A ^ 2 + |c2| * U₀ * A ^ 2 + |c5| * U₀ * A ^ 2 + |c4| * A ^ 3 +
      (c ^ 2 / 2 * A ^ 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 * A ^ 6) +
      (|c4| ^ 2 * S ^ 2 * A ^ 4 + |c4| * S * c * A ^ 3) ≤ (|c1| + |c2| + |c5| + |c4| + c ^ 2 / 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 +
      |c4| ^ 2 * S ^ 2 + |c4| * S * c) * (1 + U₀) * (A ^ 2 + A ^ 6) := by
    have h3 := pow_three_le_sum A
    have h4 := pow_four_le_sum A
    have hA2 : A ^ 2 ≤ A ^ 2 + A ^ 6 := le_add_of_nonneg_right (by positivity)
    have hA6 : A ^ 6 ≤ A ^ 2 + A ^ 6 := le_add_of_nonneg_left (by positivity)
    have hW : 0 ≤ A ^ 2 + A ^ 6 := by positivity
    have hk0 : 0 ≤ (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 := by positivity
    have e1 := mul_le_mul_of_nonneg_left hA2 (abs_nonneg c1)
    have e2 := mul_le_mul_of_nonneg_left hA2 (mul_nonneg (abs_nonneg c2) hU)
    have e3 := mul_le_mul_of_nonneg_left hA2 (mul_nonneg (abs_nonneg c5) hU)
    have e4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg c4)
    have e5 := mul_le_mul_of_nonneg_left hA2 (by positivity : (0 : ℝ) ≤ c ^ 2 / 2)
    have e6 := mul_le_mul_of_nonneg_left hA6 hk0
    have e7 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ |c4| ^ 2 * S ^ 2)
    have e8 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ |c4| * S * c)
    have f1 : 0 ≤ |c1| * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f2 : 0 ≤ |c2| * (A ^ 2 + A ^ 6) := by positivity
    have f3 : 0 ≤ |c5| * (A ^ 2 + A ^ 6) := by positivity
    have f4 : 0 ≤ |c4| * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f5 : 0 ≤ c ^ 2 / 2 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f6 : 0 ≤ (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f7 : 0 ≤ |c4| ^ 2 * S ^ 2 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f8 : 0 ≤ |c4| * S * c * U₀ * (A ^ 2 + A ^ 6) := by positivity
    linarith
  have hNr := div_le_div_of_nonneg_right hN hr0.le
  have hNsplit : (|c1| * A ^ 2 + |c2| * U₀ * A ^ 2 + |c5| * U₀ * A ^ 2 + |c4| * A ^ 3 +
      (c ^ 2 / 2 * A ^ 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 * A ^ 6) +
      (|c4| ^ 2 * S ^ 2 * A ^ 4 + |c4| * S * c * A ^ 3)) / r =
      |c1| * A ^ 2 / r + |c2| * U₀ * A ^ 2 / r + |c5| * U₀ * A ^ 2 / r + |c4| * A ^ 3 / r +
      (c ^ 2 / 2 * A ^ 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 * A ^ 6) / r +
      (|c4| ^ 2 * S ^ 2 * A ^ 4 + |c4| * S * c * A ^ 3) / r := by ring
  have hlin : |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ) =
      |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) + |c4| * (A ^ 2 * s * ρ) +
        |c4| * (A ^ 3 * σ) := by ring
  have hlin2 : (|c3| + |c4|) * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) =
      |c3| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) + |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by
    ring
  have a1 := neg_abs_le SS
  have a2 := neg_abs_le (M1 + M2)
  have a3 := le_abs_self L
  have a4 := le_abs_self Tu
  have a5 := le_abs_self Tw
  have a6 := neg_abs_le St
  rw [hT]
  linarith

theorem differenceRHS_le_of_bounds
    (hHs : ∃ S c : ℝ, 0 ≤ S ∧ 0 ≤ c ∧ ∀ (A : ℝ) (w : Space → Space),
      IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
        cutoffSixthNorm r w ≤ S * (Real.sqrt (cutoffDissipation r w) + c * A / r))
    (hssp : ∃ c : ℝ, ∀ (A : ℝ) (w : Space → Space),
      IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
        |(1 / 2) * ∫ x, ‖w x‖ ^ 2 * FundSol.scalarSumSecondPartials (cutoffPow r) x| ≤ c * A ^ 2 / r)
    (htr : ∃ c : ℝ, ∀ (A U₀ U₁ : ℝ) (u w : Space → Space),
      IsDifferenceData A U₀ U₁ u w → ∀ r : ℝ, 1 ≤ r →
        |(1 / 2) * ∫ x, ‖w x‖ ^ 2 * inner ℝ (u x) (gradientAt (cutoffPow r) x)| ≤
          c * U₀ * A ^ 2 / r)
    (hst : ∀ (A U₀ U₁ : ℝ) (u w : Space → Space),
      IsDifferenceData A U₀ U₁ u w → ∀ r : ℝ, 0 < r →
        |∫ x, cutoffPow r x * inner ℝ (w x) (fderiv ℝ u x (w x))| ≤ 2 * U₁ * cutoffEnergy r w)
    (hcub : ∃ c : ℝ, ∀ (A : ℝ) (w : Space → Space),
      IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
        |(1 / 2) * ∫ x, ‖w x‖ ^ 2 * inner ℝ (w x) (gradientAt (cutoffPow r) x)| ≤
          c * cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r)
    (hmix : ∃ c : ℝ, ∀ (A U₀ U₁ : ℝ) (u w : Space → Space),
      IsDifferenceData A U₀ U₁ u w → ∀ r : ℝ, 1 ≤ r →
        |stressPairing u w (FundSol.potential (cutoffSource r w)) +
          stressPairing w u (FundSol.potential (cutoffSource r w))| ≤ c * U₀ * A ^ 2 / r)
    (hself : ∃ c : ℝ, ∀ (A : ℝ) (w : Space → Space),
      IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
        |stressPairing w w (FundSol.potential (cutoffSource r w))| ≤
          c * (cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r +
            A ^ 2 * cutoffSixthNorm r w * r ^ (-(3 / 2) : ℝ) + A ^ 3 * r ^ (-(5 / 2) : ℝ))) :
    ∃ K : ℝ, ∀ (A U₀ U₁ : ℝ) (u w : Space → Space),
      IsDifferenceData A U₀ U₁ u w → ∀ r : ℝ, 1 ≤ r →
        differenceRHS r u w ≤ 2 * U₁ * cutoffEnergy r w + K * (1 + U₀) * (A ^ 2 + A ^ 6) / r := by
  obtain ⟨S, c, hS, hc, hHs⟩ := hHs
  obtain ⟨c1, h1⟩ := hssp
  obtain ⟨c2, h2⟩ := htr
  obtain ⟨c3, h3⟩ := hcub
  obtain ⟨c5, h5⟩ := hmix
  obtain ⟨c4, h4⟩ := hself
  refine ⟨(|c1| + |c2| + |c5| + |c4| + c ^ 2 / 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 +
      |c4| ^ 2 * S ^ 2 + |c4| * S * c), ?_⟩
  intro A U₀ U₁ u w hd r hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hX : 0 ≤ cutoffDissipation r w := integral_nonneg fun x =>
    mul_nonneg (pow_nonneg (radialCutoff_nonneg r x) 4)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hs : 0 ≤ cutoffSixthNorm r w := Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  have hρ : r ^ (-(3 / 2) : ℝ) ≤ 1 / r := by
    rw [one_div, ← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hσ : r ^ (-(5 / 2) : ℝ) ≤ 1 / r := by
    rw [one_div, ← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hsplit : (1 / 2) * (∫ x, ‖w x‖ ^ 2 * inner ℝ (u x + w x) (gradientAt (cutoffPow r) x)) =
      (1 / 2) * (∫ x, ‖w x‖ ^ 2 * inner ℝ (u x) (gradientAt (cutoffPow r) x)) +
        (1 / 2) * ∫ x, ‖w x‖ ^ 2 * inner ℝ (w x) (gradientAt (cutoffPow r) x) := by
    rw [← mul_add, ← integral_add
      (integrable_transport hr0 hd.smooth_u.continuous hd.field.smooth.continuous)
      (integrable_transport hr0 hd.field.smooth.continuous hd.field.smooth.continuous)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [inner_add_left, mul_add]
  unfold differenceRHS
  exact combine_bounds hr hd.field.nonneg ((norm_nonneg _).trans (hd.bound_u 0)) hX hs hS hc
    (Real.rpow_nonneg hr0.le _) hρ (Real.rpow_nonneg hr0.le _) hσ (hHs A w hd.field r hr)
    (h1 A w hd.field r hr) (h2 A U₀ U₁ u w hd r hr) (h3 A w hd.field r hr)
    (hst A U₀ U₁ u w hd r hr0) (h4 A w hd.field r hr) (h5 A U₀ U₁ u w hd r hr) hsplit

end Breakdown
