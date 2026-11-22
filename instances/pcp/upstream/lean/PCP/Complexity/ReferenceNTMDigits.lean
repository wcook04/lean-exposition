import PCP.Complexity.ReferenceNTMList
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Size

/-!
# Base-four storage for the reference machine

The reference alphabet has four symbols. A tape is represented by its finite
base-four numeral, with blank digit zero. These lemmas certify random access
and replacement of one digit using only natural-number arithmetic.
-/

namespace PCP.ReferenceNTM

/-- The digit at a cell address. -/
def digit (code i : ℕ) : ℕ := code / 4 ^ i % 4

/-- Replace one digit by arithmetic on the finite tape numeral. -/
def setDigit (code i a : ℕ) : ℕ := code - digit code i * 4 ^ i + a * 4 ^ i

theorem ofDigits_setCell_add (xs : List ℕ) (i a : ℕ) :
    Nat.ofDigits 4 (setCell 0 xs i a) + cell 0 xs i * 4 ^ i =
      Nat.ofDigits 4 xs + a * 4 ^ i := by
  induction i generalizing xs with
  | zero => cases xs <;> simp [setCell, Nat.ofDigits, Nat.add_comm, Nat.add_left_comm]
  | succ i ih =>
      cases xs with
      | nil =>
          have h := ih []
          simp only [setCell, List.headD_nil, List.tail_nil, Nat.ofDigits_cons,
            zero_add, cell_nil, zero_mul, Nat.ofDigits_nil,
            pow_succ] at h ⊢
          nlinarith
      | cons b bs =>
          have h := ih bs
          simp only [setCell, List.headD_cons, List.tail_cons, Nat.ofDigits_cons,
            cell_cons_succ, pow_succ]
          nlinarith

theorem cell_mul_pow_le (xs : List ℕ) (i : ℕ) :
    cell 0 xs i * 4 ^ i ≤ Nat.ofDigits 4 xs := by
  induction i generalizing xs with
  | zero => cases xs <;> simp [Nat.ofDigits]
  | succ i ih =>
      cases xs with
      | nil => simp
      | cons b bs =>
          have h := ih bs
          simp only [cell_cons_succ, pow_succ, Nat.ofDigits_cons]
          nlinarith

theorem ofDigits_setCell (xs : List ℕ) (i a : ℕ) :
    Nat.ofDigits 4 (setCell 0 xs i a) =
      Nat.ofDigits 4 xs - cell 0 xs i * 4 ^ i + a * 4 ^ i := by
  have h := ofDigits_setCell_add xs i a
  have hle := cell_mul_pow_le xs i
  omega

theorem digit_ofDigits (xs : List ℕ) (h : ∀ a ∈ xs, a < 4) (i : ℕ) :
    digit (Nat.ofDigits 4 xs) i = cell 0 xs i := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => simp [digit]
      | cons a as =>
          have ha := h a (by simp)
          simp [digit, Nat.ofDigits_cons, Nat.add_mod, Nat.mod_eq_of_lt ha]
  | succ i ih =>
      rw [digit, pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.ofDigits_div_eq_ofDigits_tail (by decide) xs h]
      cases xs with
      | nil => simp
      | cons a as =>
          simpa [digit] using ih as (fun b hb => h b (by simp [hb]))

theorem setCell_digits_lt (xs : List ℕ) (h : ∀ a ∈ xs, a < 4)
    (i a : ℕ) (ha : a < 4) : ∀ b ∈ setCell 0 xs i a, b < 4 := by
  induction i generalizing xs with
  | zero =>
      intro b hb
      simp only [setCell, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ha
      · exact h b (List.mem_of_mem_tail hb)
  | succ i ih =>
      intro b hb
      simp only [setCell, List.mem_cons] at hb
      rcases hb with rfl | hb
      · cases xs with
        | nil => decide
        | cons c cs => exact h c (by simp)
      · exact ih xs.tail (fun c hc => h c (List.mem_of_mem_tail hc)) b hb

theorem digit_setDigit (code i a j : ℕ) (ha : a < 4) :
    digit (setDigit code i a) j = if j = i then a else digit code j := by
  let xs := Nat.digits 4 code
  have hx : ∀ b ∈ xs, b < 4 := fun b hb => Nat.digits_lt_base (by decide) hb
  have he : Nat.ofDigits 4 xs = code := Nat.ofDigits_digits 4 code
  have hd := digit_ofDigits xs hx i
  rw [he] at hd
  have hs : setDigit code i a = Nat.ofDigits 4 (setCell 0 xs i a) := by
    rw [ofDigits_setCell, he, ← hd]
    rfl
  rw [hs, digit_ofDigits _ (setCell_digits_lt xs hx i a ha), cell_setCell]
  have hj := digit_ofDigits xs hx j
  rw [he] at hj
  rw [hj]

theorem setDigit_lt_pow (code i a B : ℕ) (hc : code < 4 ^ B)
    (hi : i < B) (ha : a < 4) : setDigit code i a < 4 ^ B := by
  let xs := Nat.digitsAppend 4 B code
  have hx : ∀ b ∈ xs, b < 4 := fun b hb => Nat.lt_of_mem_digitsAppend (by decide) B b hb
  have he : Nat.ofDigits 4 xs = code := by
    simp [xs, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  have hl : xs.length = B := Nat.length_digitsAppend (by decide) B hc
  have hd := digit_ofDigits xs hx i
  rw [he] at hd
  have hs : setDigit code i a = Nat.ofDigits 4 (setCell 0 xs i a) := by
    rw [ofDigits_setCell, he, ← hd]
    rfl
  rw [hs]
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 4)
    (setCell_digits_lt xs hx i a ha)
  simpa [length_setCell, hl, max_eq_left (by omega : i + 1 ≤ B)] using h

theorem size_le_of_lt_four_pow (code B : ℕ) (h : code < 4 ^ B) :
    Nat.size code ≤ 2 * B := by
  apply Nat.size_le.mpr
  simpa only [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul] using h

end PCP.ReferenceNTM
