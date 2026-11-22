/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Verifier.Reduction
import PCP.Complexity.Bounds
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Canonical logarithmic randomness under polynomial input reductions

A polynomial output-size bound supplies explicit constant coefficients for the
source verifier's canonical randomness. Proof-address bounds compose as ordinary
polynomials. This is resource algebra, independent of the cost of constructing
the reduced input.
-/

namespace PCP.Verifier.Reduction

open Polynomial

/-- The coefficient sum controls evaluation by a single power. -/
theorem eval_le_coefficientSum (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ p.eval 1 * (n + 2) ^ p.natDegree := by
  rw [eval_eq_sum, eval_eq_sum, Polynomial.sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simp only [one_pow, mul_one]
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left (by omega : n ≤ n + 2) i).trans
    (Nat.pow_le_pow_right (by omega : 0 < n + 2) (le_natDegree_of_mem_supp i hi))

/-- An explicit affine ceiling-log bound for every natural-coefficient polynomial. -/
theorem clog_eval_add_two_le (p : Polynomial ℕ) (n : ℕ) :
    Nat.clog 2 (p.eval n + 2) ≤
      p.natDegree * Nat.clog 2 (n + 2) + Nat.clog 2 (p.eval 1 + 2) := by
  rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
  have hbase : 1 ≤ (n + 2) ^ p.natDegree := Nat.one_le_pow _ _ (by omega)
  have heval := eval_le_coefficientSum p n
  calc
    p.eval n + 2 ≤ (p.eval 1 + 2) * (n + 2) ^ p.natDegree := by nlinarith
    _ ≤ 2 ^ Nat.clog 2 (p.eval 1 + 2) *
        (2 ^ Nat.clog 2 (n + 2)) ^ p.natDegree :=
      Nat.mul_le_mul (Nat.le_pow_clog (by decide) _)
        (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _)
    _ = 2 ^ (p.natDegree * Nat.clog 2 (n + 2) + Nat.clog 2 (p.eval 1 + 2)) := by
      rw [pow_add, ← pow_mul, Nat.mul_comm (Nat.clog 2 (n + 2)) p.natDegree]
      ac_rfl

/-- The new slope and intercept depend only on the fixed reduction bound. -/
def budget (p : Polynomial ℕ) (a b n : ℕ) : ℕ :=
  (a * p.natDegree) * Nat.clog 2 (n + 2) + (a * Nat.clog 2 (p.eval 1 + 2) + b)

theorem randomness_le_budget (V : Verifier) {a b : ℕ} (hr : V.CanonicalRandomness a b)
    (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hp : ∀ x, (f x).length ≤ p.eval x.length) (x : List Bool) :
    V.randomness (f x).length ≤ budget p a b x.length := by
  rw [hr]
  have h := (Nat.clog_mono_right 2 (Nat.add_le_add_right (hp x) 2)).trans
    (clog_eval_add_two_le p x.length)
  have hm := Nat.mul_le_mul_left a h
  dsimp [budget]
  nlinarith

/-- Polynomially bounded reduction, with a canonical source randomness budget. -/
def canonicalVerifier (V : Verifier) {a b : ℕ} (hr : V.CanonicalRandomness a b)
    (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hp : ∀ x, (f x).length ≤ p.eval x.length) : Verifier :=
  verifier V f (budget p a b) (randomness_le_budget V hr f p hp)

theorem canonicalVerifier_randomness (V : Verifier) {a b : ℕ}
    (hr : V.CanonicalRandomness a b) (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hp : ∀ x, (f x).length ≤ p.eval x.length) :
    (canonicalVerifier V hr f p hp).CanonicalRandomness
      (a * p.natDegree) (a * Nat.clog 2 (p.eval 1 + 2) + b) := fun _ => rfl

/-- The composed proof-length polynomial bounds every branch and every random seed. -/
theorem canonicalVerifier_readsBelow (V : Verifier) {a b : ℕ}
    (hr : V.CanonicalRandomness a b) (f : List Bool → List Bool) (p q : Polynomial ℕ)
    (hp : ∀ x, (f x).length ≤ p.eval x.length)
    (hq : ∀ y, V.ReadsBelow y (q.eval y.length)) (x : List Bool) :
    (canonicalVerifier V hr f p hp).ReadsBelow x ((q.comp p).eval x.length) := by
  intro r j hj
  have h := readsBelow V f (budget p a b) (randomness_le_budget V hr f p hp) x
    (hq (f x)) r j hj
  exact h.trans_le (by rw [eval_comp]; exact Machine.eval_mono q (hp x))

end PCP.Verifier.Reduction
