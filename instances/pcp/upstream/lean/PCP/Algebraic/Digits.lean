import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Basic

/-!
# Fixed-width base digits

The digit arithmetic used in Definition 3.1 of Amireddy–Behera–Srinivasan–Sudan–
Willumsgaard, *A Simple Algebraic Proof of the PCP Theorem* (PCP-SOSA27).
Positions are little-endian: position `i` has weight `m ^ i`.

Truncating to `c` digits recovers `k % m ^ c`. Recovering `k` itself requires
`k < m ^ c`; this hypothesis must not disappear in the polynomial encoding.
-/

namespace PCP.Algebraic

open Finset

/-- The `i`th base-`m` digit, including leading zeroes. -/
def digit (m : ℕ) [NeZero m] (k i : ℕ) : Fin m :=
  ⟨k / m ^ i % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

/-- The first `c` digits reconstruct the residue modulo `m ^ c`. -/
theorem sum_div_mod_mul_pow (m c k : ℕ) :
    ∑ i ∈ range c, (k / m ^ i % m) * m ^ i = k % m ^ c := by
  induction c with
  | zero => simp only [sum_range_zero, pow_zero, Nat.mod_one]
  | succ c ih =>
    rw [sum_range_succ, ih, pow_succ, Nat.mod_mul]
    rw [Nat.mul_comm (k / m ^ c % m)]

theorem sum_digit_mul_pow (m : ℕ) [NeZero m] (c k : ℕ) :
    ∑ i : Fin c, (digit m k i : ℕ) * m ^ (i : ℕ) = k % m ^ c := by
  change ∑ i : Fin c, (k / m ^ (i : ℕ) % m) * m ^ (i : ℕ) = _
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (k / m ^ i % m) * m ^ i)]
  exact sum_div_mod_mul_pow m c k

/-- Reconstruction without truncation, at the width used in the paper. -/
theorem sum_digit_mul_pow_of_lt (m : ℕ) [NeZero m] (c k : ℕ) (hk : k < m ^ c) :
    ∑ i : Fin c, (digit m k i : ℕ) * m ^ (i : ℕ) = k := by
  rw [sum_digit_mul_pow, Nat.mod_eq_of_lt hk]

end PCP.Algebraic
