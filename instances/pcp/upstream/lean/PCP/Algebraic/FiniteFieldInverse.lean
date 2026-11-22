/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# Inversion by a specified finite-field cardinality

The operation `inverse q` uses only a zero test, one and repeated multiplication.
It does not require a field structure on its input type. An injective map preserving
zero, one and multiplication into a field of cardinality `q` proves that this
operation is an inverse. In particular, these lemmas can establish the inverse
axioms when constructing a field on concrete coefficient words.

Computability is relative to the supplied equality test and elementary operations.
No bound on their machine running time is asserted here.
-/

namespace PCP.Algebraic.FiniteFieldInverse

variable {A F : Type*}

/-- Repeated multiplication gives inversion, with a separate zero branch.
The explicit recursion avoids any prerequisite algebraic laws on the input type. -/
def inverse [Zero A] [One A] [Mul A] [DecidableEq A] (q : ℕ) (x : A) : A :=
  if x = 0 then 0 else npowRec (q - 2) x

@[simp]
theorem inverse_zero [Zero A] [One A] [Mul A] [DecidableEq A] (q : ℕ) :
    inverse q (0 : A) = 0 := by
  simp [inverse]

section Field

variable [Field F] [Finite F] {q : ℕ}

/-- The exponent `q - 2` supplies a multiplicative inverse of every nonzero element. -/
theorem mul_pow_card_sub_two (hq : Nat.card F = q) {x : F} (hx : x ≠ 0) :
    x * x ^ (q - 2) = 1 := by
  let := Fintype.ofFinite F
  have hq2 : 2 ≤ q := by
    have : 1 < Nat.card F := by
      simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
    omega
  rw [← pow_succ', show q - 2 + 1 = q - 1 by omega, ← hq,
    Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one x hx

/-- The computed power agrees with the semantic field inverse away from zero. -/
theorem pow_card_sub_two_eq_inv (hq : Nat.card F = q) {x : F} (hx : x ≠ 0) :
    x ^ (q - 2) = x⁻¹ :=
  eq_inv_of_mul_eq_one_right (mul_pow_card_sub_two hq hx)

end Field

/-- A map preserving one and multiplication takes explicit power recursion to powers. -/
theorem map_npowRec [One A] [Mul A] [Monoid F] (f : A → F)
    (hone : f 1 = 1) (hmul : ∀ x y, f (x * y) = f x * f y)
    (x : A) (n : ℕ) : f (npowRec n x) = f x ^ n := by
  induction n with
  | zero => simpa only [npowRec, pow_zero] using hone
  | succ n ih =>
    change f (npowRec n x * x) = f x ^ (n + 1)
    rw [hmul, ih, pow_succ]

/-- Correctness of inversion on a concrete representation, before it has field laws. -/
theorem map_inverse [Zero A] [One A] [Mul A] [DecidableEq A]
    [Field F] [Finite F] {q : ℕ} (f : A → F) (hf : Function.Injective f)
    (hzero : f 0 = 0) (hone : f 1 = 1)
    (hmul : ∀ x y, f (x * y) = f x * f y)
    (hq : Nat.card F = q) (x : A) : f (inverse q x) = (f x)⁻¹ := by
  by_cases hx : x = 0
  · simp [inverse, hx, hzero]
  · have hfx : f x ≠ 0 := fun h => hx (hf (h.trans hzero.symm))
    rw [inverse, ite_eq_right hx, map_npowRec f hone hmul,
      pow_card_sub_two_eq_inv hq hfx]

/-- The nonzero inverse axiom transported to the concrete operations. -/
theorem mul_inverse_cancel [Zero A] [One A] [Mul A] [DecidableEq A]
    [Field F] [Finite F] {q : ℕ} (f : A → F) (hf : Function.Injective f)
    (hzero : f 0 = 0) (hone : f 1 = 1)
    (hmul : ∀ x y, f (x * y) = f x * f y)
    (hq : Nat.card F = q) {x : A} (hx : x ≠ 0) : x * inverse q x = 1 := by
  apply hf
  have hfx : f x ≠ 0 := fun h => hx (hf (h.trans hzero.symm))
  rw [hmul, map_inverse f hf hzero hone hmul hq, hone, mul_inv_cancel₀ hfx]

/-- In a finite field, the elementary algorithm agrees with its existing inverse. -/
theorem inverse_eq_inv [Field F] [Finite F] [DecidableEq F]
    {q : ℕ} (hq : Nat.card F = q) (x : F) : inverse q x = x⁻¹ :=
  map_inverse id Function.injective_id rfl rfl (fun _ _ => rfl) hq x

end PCP.Algebraic.FiniteFieldInverse
