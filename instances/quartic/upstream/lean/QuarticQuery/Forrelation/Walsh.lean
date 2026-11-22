module

public import QuarticQuery.Statement

/-!
# The Walsh matrix is Hadamard

`walshN n i j` is `walshSign` on natural-number indices, so that one recursion on
the top bit proves the character sum here and the butterfly in the circuit. The
matrices `W` and `H` are the objects of Section 2.1: `W` has `±1` entries, is
symmetric, `W Wᵀ = m I`, and `H = W / 2^t` is a real symmetric involution.
-/

@[expose] public section

namespace QuarticQuery.Forrelation

open Finset Matrix

/-- Ledger: def-walsh-sign. `walshSign` with the indices read as naturals. -/
def walshN (n i j : ℕ) : ℤ :=
  (-1 : ℤ) ^ (∑ b ∈ range n, if i.testBit b && j.testBit b then (1 : ℕ) else 0)

theorem walshSign_eq (t : ℕ) (i j : Fin (mValue t)) :
    walshSign t i j = walshN (2 * t) i j := rfl

@[simp] theorem bitSign_mul_self (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> simp [bitSign]

theorem walshN_succ (n i j : ℕ) :
    walshN (n + 1) i j = walshN n i j * bitSign (i.testBit n && j.testBit n) := by
  unfold walshN bitSign
  rw [sum_range_succ, pow_add]
  cases (i.testBit n && j.testBit n) <;> simp

theorem walshN_zero (i j : ℕ) : walshN 0 i j = 1 := by simp [walshN]

theorem walshN_eq_one_or (n i j : ℕ) : walshN n i j = 1 ∨ walshN n i j = -1 :=
  neg_one_pow_eq_or ℤ _

theorem walshN_comm (n i j : ℕ) : walshN n i j = walshN n j i := by
  simp [walshN, Bool.and_comm]

theorem walshN_congr_left {n i i' : ℕ} (h : ∀ b < n, i.testBit b = i'.testBit b) (j : ℕ) :
    walshN n i j = walshN n i' j := by
  unfold walshN
  congr 1
  exact sum_congr rfl fun b hb => by rw [h b (mem_range.1 hb)]

theorem walshN_congr_right {n j j' : ℕ} (h : ∀ b < n, j.testBit b = j'.testBit b) (i : ℕ) :
    walshN n i j = walshN n i j' := by
  rw [walshN_comm, walshN_congr_left h, walshN_comm]

theorem testBit_two_pow_add_low {n j b : ℕ} (hb : b < n) :
    (2 ^ n + j).testBit b = j.testBit b :=
  Nat.testBit_two_pow_add_gt hb j

theorem walshN_succ_low (n i : ℕ) {j : ℕ} (hj : j < 2 ^ n) :
    walshN (n + 1) i j = walshN n i j := by
  rw [walshN_succ, Nat.testBit_lt_two_pow hj]
  simp [bitSign]

theorem walshN_succ_high (n i : ℕ) {j : ℕ} (hj : j < 2 ^ n) :
    walshN (n + 1) i (2 ^ n + j) = bitSign (i.testBit n) * walshN n i j := by
  rw [walshN_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj,
    walshN_congr_right (fun b hb => testBit_two_pow_add_low hb) i]
  simp [mul_comm]

/-- Ledger: claim-butterfly. The transform of size `2^(n+1)` is a sum and a
difference of two transforms of size `2^n`, for any input sequence. -/
theorem sum_walshN_succ (n i : ℕ) (f : ℕ → ℤ) :
    ∑ j ∈ range (2 ^ (n + 1)), walshN (n + 1) i j * f j =
      ∑ j ∈ range (2 ^ n), walshN n i j * f j +
        bitSign (i.testBit n) * ∑ j ∈ range (2 ^ n), walshN n i j * f (2 ^ n + j) := by
  rw [pow_succ, mul_two, sum_range_add, mul_sum]
  congr 1
  · exact sum_congr rfl fun j hj => by rw [walshN_succ_low n i (mem_range.1 hj)]
  · refine sum_congr rfl fun j hj => ?_
    rw [walshN_succ_high n i (mem_range.1 hj)]
    ring

/-- Ledger: def-walsh-sign. The character sum over bit vectors. -/
theorem sum_walshN_mul (n i i' : ℕ) :
    ∑ j ∈ range (2 ^ n), walshN n i j * walshN n i' j =
      if ∀ b < n, i.testBit b = i'.testBit b then (2 : ℤ) ^ n else 0 := by
  induction n with
  | zero => simp [walshN_zero]
  | succ n ih =>
    have split : ∑ j ∈ range (2 ^ (n + 1)), walshN (n + 1) i j * walshN (n + 1) i' j =
        (1 + bitSign (i.testBit n) * bitSign (i'.testBit n)) *
          ∑ j ∈ range (2 ^ n), walshN n i j * walshN n i' j := by
      rw [pow_succ, mul_two, sum_range_add, add_mul, one_mul, mul_sum]
      congr 1
      · exact sum_congr rfl fun j hj => by
          rw [walshN_succ_low n i (mem_range.1 hj), walshN_succ_low n i' (mem_range.1 hj)]
      · refine sum_congr rfl fun j hj => ?_
        rw [walshN_succ_high n i (mem_range.1 hj), walshN_succ_high n i' (mem_range.1 hj)]
        ring
    rw [split, ih]
    by_cases hn : i.testBit n = i'.testBit n
    · have hiff : (∀ b < n + 1, i.testBit b = i'.testBit b) ↔
          ∀ b < n, i.testBit b = i'.testBit b :=
        ⟨fun h b hb => h b (by omega), fun h b hb => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
          · exact h b hb
          · exact hn⟩
      rw [if_congr hiff rfl rfl, hn, bitSign_mul_self]
      split_ifs <;> ring
    · have hs : (1 + bitSign (i.testBit n) * bitSign (i'.testBit n)) = 0 := by
        cases h1 : i.testBit n <;> cases h2 : i'.testBit n <;> simp_all [bitSign]
      have hno : ¬ ∀ b < n + 1, i.testBit b = i'.testBit b := fun h => hn (h n (by omega))
      simp only [hs, hno, ite_false, zero_mul]

theorem testBit_agree_iff {n i i' : ℕ} (hi : i < 2 ^ n) (hi' : i' < 2 ^ n) :
    (∀ b < n, i.testBit b = i'.testBit b) ↔ i = i' := by
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun b => ?_
    by_cases hb : b < n
    · exact h b hb
    · have l : 2 ^ n ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hi l),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hi' l)]
  · rintro rfl _ _
    rfl

/-! ## The matrices -/

/-- Ledger: def-walsh-sign. `W = √m H`, with integer entries. -/
def walshZ (t : ℕ) : Matrix (Fin (mValue t)) (Fin (mValue t)) ℤ :=
  Matrix.of (walshSign t)

/-- Ledger: def-walsh-sign. `W` over the reals. -/
noncomputable def W (t : ℕ) : Matrix (Fin (mValue t)) (Fin (mValue t)) ℝ :=
  (walshZ t).map (Int.castRingHom ℝ)

/-- Ledger: eq-3. The normalised Walsh–Hadamard matrix, `W / √m`, with
`√m = 2 ^ t`. -/
noncomputable def H (t : ℕ) : Matrix (Fin (mValue t)) (Fin (mValue t)) ℝ :=
  ((2 : ℝ) ^ t)⁻¹ • W t

theorem walshSign_eq_one_or (t : ℕ) (i j : Fin (mValue t)) :
    walshSign t i j = 1 ∨ walshSign t i j = -1 :=
  walshN_eq_one_or _ _ _

theorem walshSign_symm (t : ℕ) (i j : Fin (mValue t)) : walshSign t i j = walshSign t j i :=
  walshN_comm _ _ _

theorem walshZ_transpose (t : ℕ) : (walshZ t)ᵀ = walshZ t := by
  ext i j
  exact walshSign_symm t j i

theorem sum_range_mValue (t : ℕ) (f : ℕ → ℤ) :
    ∑ j : Fin (mValue t), f j = ∑ j ∈ range (2 ^ (2 * t)), f j :=
  Fin.sum_univ_eq_sum_range f (mValue t)

/-- Ledger: def-walsh-sign. Rows are orthogonal: `W Wᵀ = m I` over the integers. -/
theorem walshZ_mul_transpose (t : ℕ) :
    walshZ t * (walshZ t)ᵀ = (mValue t : ℤ) • (1 : Matrix _ _ ℤ) := by
  ext i i'
  have hi : i.val < 2 ^ (2 * t) := i.isLt
  have hi' : i'.val < 2 ^ (2 * t) := i'.isLt
  have key := sum_walshN_mul (2 * t) i.val i'.val
  rw [if_congr (testBit_agree_iff hi hi') rfl rfl] at key
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  change ∑ j : Fin (mValue t), walshN (2 * t) i j * walshN (2 * t) i' j = _
  rw [sum_range_mValue t (fun j => walshN (2 * t) i j * walshN (2 * t) i' j), key]
  by_cases h : i = i'
  · subst h
    simp only [↓reduceIte, mul_one]
    simp [mValue]
  · have : i.val ≠ i'.val := fun e => h (Fin.ext e)
    simp only [h, this, ite_false, mul_zero]

theorem W_transpose (t : ℕ) : (W t)ᵀ = W t := by
  rw [W, ← Matrix.transpose_map, walshZ_transpose]

/-- Ledger: def-walsh-sign. `W Wᵀ = m I` over the reals. -/
theorem W_mul_transpose (t : ℕ) :
    W t * (W t)ᵀ = (mValue t : ℝ) • (1 : Matrix _ _ ℝ) := by
  have h := congrArg (fun A => A.map (Int.castRingHom ℝ)) (walshZ_mul_transpose t)
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  rw [W, h]
  ext i j
  by_cases e : i = j
  · subst e
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Int.coe_castRingHom, Int.cast_natCast]
  · simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_ne e, smul_eq_mul, mul_zero,
      Int.coe_castRingHom, Int.cast_zero]

theorem H_transpose (t : ℕ) : (H t)ᵀ = H t := by
  rw [H, Matrix.transpose_smul, W_transpose]

theorem mValue_cast (t : ℕ) : (mValue t : ℝ) = (2 : ℝ) ^ t * (2 : ℝ) ^ t := by
  simp [mValue, two_mul, pow_add]

/-- Ledger: eq-3. `H` is an involution. -/
theorem H_mul_H (t : ℕ) : H t * H t = 1 := by
  have hW := W_mul_transpose t
  rw [W_transpose] at hW
  have h2 : ((2 : ℝ) ^ t) ≠ 0 := by positivity
  rw [H, Matrix.smul_mul, Matrix.mul_smul, hW, mValue_cast, smul_smul, smul_smul]
  have : ((2 : ℝ) ^ t)⁻¹ * ((2 : ℝ) ^ t)⁻¹ * ((2 : ℝ) ^ t * (2 : ℝ) ^ t) = 1 := by
    field_simp
  rw [this, one_smul]

/-- Ledger: eq-3. `H` is real orthogonal. -/
theorem H_mem_orthogonalGroup (t : ℕ) :
    H t ∈ Matrix.orthogonalGroup (Fin (mValue t)) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, H_transpose, H_mul_H]

end QuarticQuery.Forrelation
