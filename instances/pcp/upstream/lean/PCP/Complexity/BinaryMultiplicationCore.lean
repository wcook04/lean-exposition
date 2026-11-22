import PCP.Complexity.BinaryAdditionMachine

/-!
# Binary multiplication arithmetic and trace bounds

Reading the multiplier from high bits to low bits performs Horner steps
`a ↦ 2*a + bit*n`. The accumulator remains canonical and its bit length grows
by at most two per pass. The bound below counts the exact retained-input adder
runtime used by the concrete machine, rather than treating natural addition
as a constant-time operation.
-/

namespace PCP.Machine.BinaryMultiplication

open PCP.Lang

def stepValue (n a : ℕ) (b : Bool) : ℕ := 2 * a + if b then n else 0

def value (n a : ℕ) : List Bool → ℕ
  | [] => a
  | b :: bs => value n (stepValue n a b) bs

@[simp] theorem value_append (n a : ℕ) (xs ys : List Bool) :
    value n a (xs ++ ys) = value n (value n a xs) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih => exact ih _

/-- Canonical binary digits, reversed once, compute the actual natural product. -/
theorem value_bits (n m : ℕ) : value n 0 m.bits.reverse = n * m := by
  induction m using Nat.binaryRec' with
  | zero => simp [value]
  | bit b m hm ih =>
    rw [Nat.bits_append_bit m b hm, List.reverse_cons, value_append, ih]
    cases b <;> simp [value, stepValue, Nat.bit] <;> ring

theorem size_double (a : ℕ) : Nat.size (2 * a) ≤ Nat.size a + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self a
  omega

theorem size_add (n a : ℕ) : Nat.size (n + a) ≤ max (Nat.size n) (Nat.size a) + 1 := by
  rw [Nat.size_le, pow_succ]
  have hn : n < 2 ^ max (Nat.size n) (Nat.size a) :=
    (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have ha : a < 2 ^ max (Nat.size n) (Nat.size a) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  omega

theorem size_step (n a : ℕ) (b : Bool) :
    Nat.size (stepValue n a b) ≤ max (Nat.size n) (Nat.size a) + 2 := by
  have hd := size_double a
  cases b with
  | false => simp only [stepValue, Bool.false_eq_true, ite_false, Nat.add_zero]; omega
  | true =>
    simp only [stepValue, ite_true]
    have hs := size_add (2 * a) n
    omega

/-- Exact steps of the retained-input adder, including both materialization passes. -/
def additionTime (n a : ℕ) : ℕ :=
  max (Nat.size n) (Nat.size a) + max (Nat.size n) (Nat.size (n + a)) + 2

theorem additionTime_le (n a : ℕ) :
    additionTime n a ≤ 2 * max (Nat.size n) (Nat.size a) + 3 := by
  have := size_add n a
  unfold additionTime
  omega

def runtime (n a : ℕ) : List Bool → ℕ
  | [] => 1
  | b :: bs => runtime n (stepValue n a b) bs + (if b then additionTime n (2 * a) else 0) + 1

/-- The full bit loop, including every actual call to the binary adder. -/
theorem runtime_le (n a : ℕ) (bs : List Bool) :
    runtime n a bs ≤
      (2 * (max (Nat.size n) (Nat.size a) + 2 * bs.length) + 6) * bs.length + 1 := by
  induction bs generalizing a with
  | nil => simp [runtime]
  | cons b bs ih =>
    let M := max (Nat.size n) (Nat.size a)
    have hs := size_step n a b
    have hm : max (Nat.size n) (Nat.size (stepValue n a b)) ≤ M + 2 := by dsimp [M]; omega
    have hi := ih (stepValue n a b)
    have hcoef : 2 * (max (Nat.size n) (Nat.size (stepValue n a b)) + 2 * bs.length) + 6 ≤
        2 * (M + 2 * (bs.length + 1)) + 6 := by omega
    have hib := hi.trans (Nat.add_le_add_right (Nat.mul_le_mul_right bs.length hcoef) 1)
    have hc : (if b then additionTime n (2 * a) else 0) + 1 ≤
        2 * (M + 2 * (bs.length + 1)) + 6 := by
      have hadd := additionTime_le n (2 * a)
      have hd := size_double a
      dsimp [M]
      cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> omega
    simp only [runtime, List.length_cons]
    change _ ≤ (2 * (M + 2 * (bs.length + 1)) + 6) * (bs.length + 1) + 1
    nlinarith

/-- Reversal plus the complete Horner loop is quadratic in operand bit lengths. -/
theorem full_runtime_le (n m : ℕ) :
    Nat.size m + 1 + runtime n 0 m.bits.reverse ≤
      10 * (Nat.size n + Nat.size m + 1) ^ 2 := by
  have hm : m.bits.reverse.length = Nat.size m := by
    simpa only [natTape, binDigits_eq_bits, length_ofBits, List.length_reverse] using
      natTape_length m
  have h := runtime_le n 0 m.bits.reverse
  rw [hm] at h
  simp only [Nat.size_zero, Nat.max_zero] at h
  nlinarith

end PCP.Machine.BinaryMultiplication
