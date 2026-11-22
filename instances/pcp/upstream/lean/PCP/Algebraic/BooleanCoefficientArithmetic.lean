/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.HadamardTest
import PCP.Algebraic.BooleanCoefficientIndex

/-!
# Computable arithmetic on bounded Boolean coefficient vectors

The executable definitions below operate directly on squarefree coefficient
coordinates. Products combine coefficients with the same union of supports,
implementing reduction by `X i ^ 2 = X i`. Equality theorems identify every
operation with the existing polynomial semantics. Formal polynomials occur only
in those proofs, never in the computed data. No machine-time bound is asserted.
-/

namespace PCP.Algebraic.BooleanCoefficientArithmetic

open Finset BinaryPolynomialSpace

variable {t a b r : ℕ}

/-- The constant occupies exactly the empty support. -/
def constant (z : ZMod 2) : Coefficients t r :=
  fun s => if s.val = ∅ then z else 0

/-- One coordinate variable occupies exactly its singleton support. -/
def variableCoeff (_hr : 1 ≤ r) (i : Fin t) : Coefficients t r :=
  fun s => if s.val = {i} then 1 else 0

/-- Evaluation is the finite sum of squarefree monomial evaluations. -/
def evaluate (x : Fin t → ZMod 2) (p : Coefficients t r) : ZMod 2 :=
  ∑ s : Monomials t r, p s * ∏ i ∈ s.val, x i

/-- Homogeneous linear evaluation is the binary dot product. -/
def linearEncode (x w : Fin t → ZMod 2) : ZMod 2 :=
  ∑ i, x i * w i

/-- Store a homogeneous linear label in the larger coefficient space. -/
def homogeneousIndex (hr : 1 ≤ r) (w : Fin t → ZMod 2) : Coefficients t r :=
  ∑ i, w i • variableCoeff hr i

/-- Include a coefficient word in a larger degree bound by padding with zero. -/
def embed (_h : a ≤ b) (p : Coefficients t a) : Coefficients t b :=
  fun s => if hs : s.val.card ≤ a then p ⟨s.val, hs⟩ else 0

/-- Squarefree multiplication accumulates every pair with the same union of supports. -/
def mixedProduct (_h : a + b ≤ r) (p : Coefficients t a)
    (q : Coefficients t b) : Coefficients t r :=
  fun s => ∑ u : Monomials t a, ∑ v : Monomials t b,
    if u.val ∪ v.val = s.val then p u * q v else 0

@[simp] theorem constant_eq (z : ZMod 2) :
    constant (t := t) (r := r) z = BinaryPolynomialSpace.constant z := by
  funext s
  simp [constant, BinaryPolynomialSpace.constant, Pi.single_apply, Subtype.ext_iff]

@[simp] theorem variableCoeff_eq (hr : 1 ≤ r) (i : Fin t) :
    variableCoeff hr i = BinaryPolynomialSpace.variableCoeff hr i := by
  funext s
  simp [variableCoeff, BinaryPolynomialSpace.variableCoeff, Pi.single_apply,
    Subtype.ext_iff]

@[simp] theorem evaluate_eq (x : Fin t → ZMod 2) (p : Coefficients t r) :
    evaluate x p = BinaryPolynomialSpace.evaluate x p := by
  classical
  rw [BinaryPolynomialSpace.evaluate_apply, polynomial_apply, map_sum]
  unfold evaluate
  apply Finset.sum_congr rfl
  intro s hs
  rw [MvPolynomial.eval_monomial, Finsupp.prod, support_exponent]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp [hi]

@[simp] theorem linearEncode_eq (x w : Fin t → ZMod 2) :
    linearEncode x w = Hadamard.linearEncode x w :=
  (Hadamard.linearEncode_apply x w).symm

@[simp] theorem homogeneousIndex_eq (hr : 1 ≤ r) (w : Fin t → ZMod 2) :
    homogeneousIndex hr w = Hadamard.homogeneousIndex hr w := by
  simp [homogeneousIndex, Hadamard.homogeneousIndex]

@[simp] theorem embed_eq (h : a ≤ b) (p : Coefficients t a) :
    embed h p = BinaryPolynomialSpace.embed h p := by
  classical
  funext s
  change (if hs : s.val.card ≤ a then p ⟨s.val, hs⟩ else 0) =
    (polynomial t a p).coeff (exponent s.val)
  by_cases hs : s.val.card ≤ a
  · simpa only [dite_eq_left hs] using (coeff_polynomial p ⟨s.val, hs⟩).symm
  · rw [dite_eq_right hs, polynomial_apply, MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    rw [MvPolynomial.coeff_monomial]
    have hne : exponent u.val ≠ exponent s.val := by
      intro he
      have he' := exponent_injective he
      exact hs (he' ▸ u.property)
    simp [hne]

/-- Truncating the sum of two squarefree exponents takes their support union. -/
theorem multilinearExponent_add (u v : Finset (Fin t)) :
    multilinearExponent (exponent u + exponent v) = exponent (u ∪ v) := by
  ext i
  simp only [multilinearExponent_apply, Finsupp.add_apply, exponent_apply, mem_union]
  by_cases hu : i ∈ u <;> by_cases hv : i ∈ v <;> simp [hu, hv]

@[simp] theorem mixedProduct_eq (h : a + b ≤ r) (p : Coefficients t a)
    (q : Coefficients t b) :
    mixedProduct h p q = BinaryPolynomialSpace.mixedProduct h p q := by
  classical
  funext s
  unfold mixedProduct BinaryPolynomialSpace.mixedProduct coefficients
  rw [polynomial_apply, polynomial_apply, Finset.sum_mul]
  simp_rw [Finset.mul_sum, map_sum, MvPolynomial.coeff_sum,
    MvPolynomial.monomial_mul_monomial, multilinearReduction_monomial,
    multilinearExponent_add, MvPolynomial.coeff_monomial, exponent_injective.eq_iff]

/-- The computed product has the intended multiplication law on every Boolean input. -/
theorem evaluate_mixedProduct (h : a + b ≤ r) (x : Fin t → ZMod 2)
    (p : Coefficients t a) (q : Coefficients t b) :
    evaluate x (mixedProduct h p q) = evaluate x p * evaluate x q := by
  simp

/-- The computed degree embedding preserves evaluation. -/
theorem evaluate_embed (h : a ≤ b) (x : Fin t → ZMod 2) (p : Coefficients t a) :
    evaluate x (embed h p) = evaluate x p := by
  simp

/-- The computed homogeneous label observes the supplied binary dot product. -/
theorem evaluate_homogeneousIndex (hr : 1 ≤ r) (x w : Fin t → ZMod 2) :
    evaluate x (homogeneousIndex hr w) = linearEncode x w := by
  simp only [evaluate_eq, homogeneousIndex_eq, linearEncode_eq]
  exact Hadamard.encode_homogeneousIndex hr x w

end PCP.Algebraic.BooleanCoefficientArithmetic
