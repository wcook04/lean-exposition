/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Computable arithmetic on fixed-length binary coefficient words

The shift register reduces multiplication by `X` modulo a monic polynomial whose
lower coefficient word is supplied explicitly. Multiplication is a finite sum of
iterated shifts. These definitions are executable without polynomial operations or
chosen quotient representatives. Evaluation in any commutative binary algebra proves
their correctness whenever the algebra element satisfies the modulus relation.

The function type retains its usual pointwise instances; this module does not put a
field structure on it and makes no running-time assertion.
-/

namespace PCP.Algebraic.BinaryWordArithmetic

/-- Coefficients in increasing order of degree. -/
abbrev Word (t : ℕ) := Fin t → ZMod 2

/-- Evaluation of a coefficient word at a chosen algebra element. -/
def evalWord {t : ℕ} {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (θ : A) (v : Word t) : A :=
  ∑ i, algebraMap (ZMod 2) A (v i) * θ ^ i.val

/-- The coefficient word of the constant one. -/
def one (t : ℕ) : Word t := fun i => if i.val = 0 then 1 else 0

/-- The constant-one word with a nonempty-word interface. -/
def oneWord {t : ℕ} (_ht : 0 < t) : Word t := one t

/-- Shift the coefficients up by one, discarding the highest coefficient. -/
def shiftUp {t : ℕ} (v : Word t) : Word t := fun i =>
  if h : i.val = 0 then 0 else v ⟨i.val - 1, by omega⟩

/-- The highest coefficient of a nonempty word. -/
def top {t : ℕ} (ht : 0 < t) (v : Word t) : ZMod 2 := v ⟨t - 1, by omega⟩

/-- Multiplication by `X` reduced by `X^t + ∑ i, m i * X^i`. -/
def shift {t : ℕ} (ht : 0 < t) (m v : Word t) : Word t :=
  shiftUp v - top ht v • m

/-- Multiplication by repeated reduced shifts and coefficient accumulation. -/
def mul {t : ℕ} (ht : 0 < t) (m v w : Word t) : Word t :=
  ∑ i : Fin t, v i • (shift ht m)^[i.val] w

section Evaluation

variable {t : ℕ} {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
variable (θ : A)

@[simp] theorem evalWord_zero : evalWord θ (0 : Word t) = 0 := by
  simp [evalWord]

@[simp] theorem evalWord_add (v w : Word t) :
    evalWord θ (v + w) = evalWord θ v + evalWord θ w := by
  simp [evalWord, add_mul, Finset.sum_add_distrib]

@[simp] theorem evalWord_sub (v w : Word t) :
    evalWord θ (v - w) = evalWord θ v - evalWord θ w := by
  simp [evalWord, sub_mul, Finset.sum_sub_distrib]

@[simp] theorem evalWord_neg (v : Word t) :
    evalWord θ (-v) = -evalWord θ v := by
  simp only [evalWord, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

@[simp] theorem evalWord_smul (c : ZMod 2) (v : Word t) :
    evalWord θ (c • v) = algebraMap (ZMod 2) A c * evalWord θ v := by
  simp [evalWord, Finset.mul_sum, mul_assoc]

@[simp] theorem evalWord_one (ht : 0 < t) : evalWord θ (one t) = 1 := by
  cases t with
  | zero => omega
  | succ n => simp [evalWord, one]

@[simp] theorem evalWord_oneWord (ht : 0 < t) : evalWord θ (oneWord ht) = 1 :=
  evalWord_one θ ht

/-- Discarded highest coefficient accounts exactly for the lost highest power. -/
theorem evalWord_shiftUp (ht : 0 < t) (v : Word t) :
    evalWord θ (shiftUp v) =
      θ * evalWord θ v - algebraMap (ZMod 2) A (top ht v) * θ ^ t := by
  cases t with
  | zero => omega
  | succ n =>
    have hs : evalWord θ (shiftUp v) =
        ∑ i : Fin n, algebraMap (ZMod 2) A (v i.castSucc) * θ ^ (i.val + 1) := by
      simp only [evalWord, Fin.sum_univ_succ, shiftUp, Fin.val_zero, ↓reduceDIte,
        map_zero, zero_mul, Fin.val_succ, Nat.add_one_ne_zero, Nat.add_sub_cancel, zero_add]
      apply Finset.sum_congr rfl
      intro i hi
      rfl
    rw [hs]
    rw [evalWord, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, top, Nat.add_sub_cancel]
    rw [mul_add, Finset.mul_sum]
    simp_rw [pow_succ]
    have hsum : (∑ i : Fin n, θ * (algebraMap (ZMod 2) A (v i.castSucc) * θ ^ i.val)) =
        ∑ i : Fin n, algebraMap (ZMod 2) A (v i.castSucc) * (θ ^ i.val * θ) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
    simp only [hlast]
    ring

/-- The shift register implements multiplication by the chosen root. -/
theorem evalWord_shift (ht : 0 < t) (m v : Word t)
    (hθ : θ ^ t + evalWord θ m = 0) :
    evalWord θ (shift ht m v) = θ * evalWord θ v := by
  rw [shift, evalWord_sub, evalWord_smul, evalWord_shiftUp θ ht]
  have h := congrArg (fun a : A => algebraMap (ZMod 2) A (top ht v) * a) hθ
  simp only [mul_add, mul_zero] at h
  linear_combination -h

/-- Iterating the shift register evaluates as multiplication by powers of the root. -/
theorem evalWord_iterate_shift (ht : 0 < t) (m v : Word t)
    (hθ : θ ^ t + evalWord θ m = 0) (n : ℕ) :
    evalWord θ ((shift ht m)^[n] v) = θ ^ n * evalWord θ v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', evalWord_shift θ ht m _ hθ, ih, pow_succ]
    ring

/-- Finite coefficient accumulation respects evaluation. -/
theorem evalWord_sum {ι : Type*} (s : Finset ι) (v : ι → Word t) :
    evalWord θ (∑ i ∈ s, v i) = ∑ i ∈ s, evalWord θ (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

/-- The computable coefficient multiplication agrees with multiplication in every
commutative algebra where the specified monic polynomial vanishes. -/
theorem evalWord_mul (ht : 0 < t) (m v w : Word t)
    (hθ : θ ^ t + evalWord θ m = 0) :
    evalWord θ (mul ht m v w) = evalWord θ v * evalWord θ w := by
  rw [mul, evalWord_sum]
  simp_rw [evalWord_smul, evalWord_iterate_shift θ ht m w hθ]
  simp [evalWord, Finset.sum_mul, mul_assoc]

end Evaluation

end PCP.Algebraic.BinaryWordArithmetic
