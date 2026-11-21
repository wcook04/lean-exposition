/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorOracle
import PCP.Algebraic.ThreeColorParameters
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Quantitative bounds for the three-color proof address space

The exact address formula gives an explicit binary exponent. For the concrete
parameter family, this exponent is linear in the logarithm of grid capacity.
These are cardinality bounds, not running-time or effective-indexing certificates.
-/

namespace PCP.Algebraic.ThreeColorResourceBounds

open Finset BinaryPolynomialSpace ThreeColorVerifier

/-- Cubic coefficient dimension is at most a simple cubic in the binary field dimension. -/
theorem cubic_dimension_le (t : ℕ) :
    (∑ k ∈ range 4, t.choose k) ≤ (t + 1) ^ 3 := by
  simp only [sum_range_succ, sum_range_zero, Nat.choose_zero_right,
    Nat.choose_one_right, zero_add]
  have h2 := Nat.choose_le_pow t 2
  have h3 := Nat.choose_le_pow t 3
  nlinarith

theorem card_cubic_le (t : ℕ) : Fintype.card (Coefficients t 3) ≤ 2 ^ ((t + 1) ^ 3) := by
  rw [card_coefficients]
  exact Nat.pow_le_pow_right (by decide) (cubic_dimension_le t)

theorem card_affine_le (t : ℕ) : Fintype.card (Coefficients t 1) ≤ 2 ^ ((t + 1) ^ 3) := by
  rw [card_coefficients]
  apply Nat.pow_le_pow_right (by decide)
  have h := cubic_dimension_le t
  simp only [sum_range_succ, sum_range_zero, Nat.choose_zero_right,
    Nat.choose_one_right, zero_add] at h ⊢
  omega

/-- Eight tables fit in this explicit power-of-two address bound. -/
theorem card_query_le {F : Type*} [Fintype F] {n m c t : ℕ}
    (hq : Fintype.card F = 2 ^ t) :
    Fintype.card (Query F n m c t) ≤ 2 ^ ((8 * n + c * m) * t + (t + 1) ^ 3 + 3) := by
  let q := Fintype.card F
  let C := 2 ^ ((t + 1) ^ 3)
  let M := q ^ (8 * n + c * m) * C
  have hqpos : 0 < q := by dsimp [q]; rw [hq]; positivity
  have hbound (k : ℕ) (hk : k ≤ 8 * n + c * m) (r : ℕ)
      (hr : Fintype.card (Coefficients t r) ≤ C) :
      q ^ k * Fintype.card (Coefficients t r) ≤ M :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hqpos hk) hr
  have h0 := hbound n (by omega) 3 (card_cubic_le t)
  have h1 := hbound (2 * n) (by omega) 3 (card_cubic_le t)
  have h2 := hbound (2 * n) (by omega) 1 (card_affine_le t)
  have h3 := hbound (4 * n) (by omega) 1 (card_affine_le t)
  have h4 := hbound (2 * n + c * m) (by omega) 1 (card_affine_le t)
  have h5 := hbound (4 * n + c * m) (by omega) 1 (card_affine_le t)
  have h6 := hbound (8 * n + c * m) (by omega) 1 (card_affine_le t)
  have hcard : Fintype.card (Query F n m c t) =
      q ^ n * Fintype.card (Coefficients t 3) +
      q ^ (2 * n) * Fintype.card (Coefficients t 3) +
      q ^ (2 * n) * Fintype.card (Coefficients t 1) +
      q ^ (4 * n) * Fintype.card (Coefficients t 1) +
      q ^ (2 * n + c * m) * Fintype.card (Coefficients t 1) +
      2 * (q ^ (4 * n + c * m) * Fintype.card (Coefficients t 1)) +
      q ^ (8 * n + c * m) * Fintype.card (Coefficients t 1) := by
    rw [card_query]
    dsimp [q]
    simp only [pow_add, pow_mul]
    ring
  have htotal : Fintype.card (Query F n m c t) ≤ 8 * M := by
    rw [hcard]
    omega
  apply htotal.trans_eq
  dsimp [M, C, q]
  rw [hq, Nat.mul_comm (8 * n + c * m) t, pow_add, pow_add, pow_mul]
  norm_num
  ring

/-- A uniform elementary bound used to control cubic binary-coordinate dimensions. -/
theorem square_le_four_pow_two (a : ℕ) : a ^ 2 ≤ 4 * 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    by_cases ha : a ≤ 2
    · interval_cases a <;> norm_num
    · have hstep : (a + 1) ^ 2 ≤ 2 * a ^ 2 := by nlinarith
      calc
        (a + 1) ^ 2 ≤ 2 * a ^ 2 := hstep
        _ ≤ 2 * (4 * 2 ^ a) := Nat.mul_le_mul_left 2 ih
        _ = 4 * 2 ^ (a + 1) := by rw [pow_succ]; ring

/-- For our field family, cubic label dimension is linear in logarithmic grid capacity. -/
theorem family_cubic_le {a : ℕ} (ha : 2 ≤ a) :
    (12 * a + 32 + 1) ^ 3 ≤ 131072 * (a * 2 ^ a) := by
  have ht : 12 * a + 32 + 1 ≤ 32 * a := by omega
  have hs := square_le_four_pow_two a
  calc
    (12 * a + 32 + 1) ^ 3 ≤ (32 * a) ^ 3 := Nat.pow_le_pow_left ht 3
    _ = 32768 * a * a ^ 2 := by ring
    _ ≤ 32768 * a * (4 * 2 ^ a) := Nat.mul_le_mul_left _ hs
    _ = 131072 * (a * 2 ^ a) := by ring

/-- An explicit proof-address exponent for the fixed degree-four family. -/
theorem family_proof_exponent_le {a : ℕ} (ha : 2 ≤ a) :
    (8 * 2 ^ a + 4 * 2 ^ a) * (12 * a + 32) +
      (12 * a + 32 + 1) ^ 3 + 3 ≤ 132000 * (a * 2 ^ a) := by
  have ht : 12 * a + 32 ≤ 32 * a := by omega
  have hlinear := Nat.mul_le_mul_left (12 * 2 ^ a) ht
  have hcubic := family_cubic_le ha
  have hpos : 0 < a * 2 ^ a := Nat.mul_pos (by omega) (by positivity)
  nlinarith

/-- The whole-field seed's closed exponent is also linear in logarithmic grid capacity. -/
theorem family_seed_exponent_le {a : ℕ} (ha : 2 ≤ a) :
    35 * (12 * a + 32) * 2 ^ a + 32 * (12 * a + 32) * 4 * 2 ^ a +
      73 * (12 * a + 32) + 50 + 8 * (12 * a + 32).choose 2 +
      6 * (12 * a + 32).choose 3 ≤ 1000000 * (a * 2 ^ a) := by
  let t := 12 * a + 32
  have ht : t ≤ 32 * a := by dsimp [t]; omega
  have hsq : t ^ 2 ≤ 4096 * 2 ^ a := calc
    t ^ 2 ≤ (32 * a) ^ 2 := Nat.pow_le_pow_left ht 2
    _ = 1024 * a ^ 2 := by ring
    _ ≤ 1024 * (4 * 2 ^ a) := Nat.mul_le_mul_left _ (square_le_four_pow_two a)
    _ = 4096 * 2 ^ a := by ring
  have hcube : t ^ 3 ≤ 131072 * (a * 2 ^ a) :=
    (Nat.pow_le_pow_left (Nat.le_succ t) 3).trans (family_cubic_le ha)
  have h2 := (Nat.choose_le_pow t 2).trans hsq
  have h3 := (Nat.choose_le_pow t 3).trans hcube
  have hlinear := Nat.mul_le_mul_right (2 ^ a) ht
  have hn : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have ha' : 1 ≤ a := by omega
  have han : a ≤ a * 2 ^ a := Nat.le_mul_of_pos_right _ hn
  have hna : 2 ^ a ≤ a * 2 ^ a := Nat.le_mul_of_pos_left _ ha'
  change 35 * t * 2 ^ a + 32 * t * 4 * 2 ^ a + 73 * t + 50 +
    8 * t.choose 2 + 6 * t.choose 3 ≤ _
  nlinarith

/-- The actual eight-table proof has at most this many bits. -/
theorem card_family_query_le {a : ℕ} (ha : 2 ≤ a) :
    Fintype.card (Query (ThreeColorParameters.Field a) (ThreeColorParameters.size a)
      (ThreeColorParameters.size a) 4 (ThreeColorParameters.binaryDimension a)) ≤
      2 ^ (132000 * (a * 2 ^ a)) := by
  have hq : Fintype.card (ThreeColorParameters.Field a) =
      2 ^ ThreeColorParameters.binaryDimension a := by
    rw [ThreeColorParameters.binaryDimension_eq, ThreeColorParameters.card_field_pow_two]
  apply (card_query_le hq).trans
  apply Nat.pow_le_pow_right (by decide)
  simpa only [ThreeColorParameters.size, ThreeColorParameters.binaryDimension_eq] using
    family_proof_exponent_le ha

/-- Rounding a base-two logarithm upward costs at most one binary factor. -/
theorem pow_clog_two_le (N : ℕ) : 2 ^ Nat.clog 2 N ≤ 2 * max 1 N := by
  by_cases hN : N ≤ 1
  · interval_cases N <;> norm_num
  · have hN' : 1 < N := by omega
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hN'
    have hc : 0 < Nat.clog 2 N := by
      rw [Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)]
      simpa using hN'
    calc
      2 ^ Nat.clog 2 N = 2 ^ (Nat.clog 2 N - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hc]
      _ ≤ N * 2 := Nat.mul_le_mul_right 2 hp.le
      _ ≤ 2 * max 1 N := by omega

/-- A fixed multiple of ceiling-logarithmic exponent gives a genuine polynomial bound. -/
theorem pow_logarithmic_le_polynomial (N K : ℕ) :
    2 ^ (K * (Nat.clog 2 N + 1)) ≤ (4 * max 1 N) ^ K := by
  rw [Nat.mul_comm K, pow_mul]
  apply Nat.pow_le_pow_left
  rw [pow_succ]
  have h := pow_clog_two_le N
  nlinarith

end PCP.Algebraic.ThreeColorResourceBounds
