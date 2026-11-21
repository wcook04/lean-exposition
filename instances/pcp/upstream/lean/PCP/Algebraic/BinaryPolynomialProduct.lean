/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryPolynomialSpace

/-!
# Degree-bounded products of binary polynomial queries

The query space is not closed under arbitrary multiplication. A product is supplied
only with a proof that the sum of the two representative degrees fits the bound.
Repeated powers are reduced before their coefficients are read, so the resulting
query represents the pointwise product on the Boolean cube.
-/

namespace PCP.Algebraic.BinaryPolynomialSpace

open MvPolynomial

variable {t r : ℕ}

@[simp] theorem totalDegree_polynomial_single_one (s : Monomials t r) :
    (polynomial t r (Pi.single s 1)).totalDegree = s.val.card := by
  rw [polynomial_single, totalDegree_monomial _ one_ne_zero]
  exact sum_exponent s.val

/-- A product in the same query space, with the degree condition from Claim 3.9. -/
noncomputable def boundedProduct (p q : Coefficients t r)
    (_h : (polynomial t r p).totalDegree + (polynomial t r q).totalDegree ≤ r) :
    Coefficients t r :=
  coefficients (multilinearReduction (polynomial t r p * polynomial t r q))

theorem polynomial_boundedProduct (p q : Coefficients t r)
    (h : (polynomial t r p).totalDegree + (polynomial t r q).totalDegree ≤ r) :
    polynomial t r (boundedProduct p q h) =
      multilinearReduction (polynomial t r p * polynomial t r q) := by
  apply polynomial_coefficients _ (multilinearReduction_isMultilinear _)
  exact (totalDegree_multilinearReduction_le _).trans ((totalDegree_mul _ _).trans h)

@[simp] theorem evaluate_boundedProduct (x : Fin t → ZMod 2) (p q : Coefficients t r)
    (h : (polynomial t r p).totalDegree + (polynomial t r q).totalDegree ≤ r) :
    evaluate x (boundedProduct p q h) = evaluate x p * evaluate x q := by
  simp only [evaluate_apply, polynomial_boundedProduct, eval_multilinearReduction, map_mul]

theorem boundedProduct_comm (p q : Coefficients t r)
    (h : (polynomial t r p).totalDegree + (polynomial t r q).totalDegree ≤ r) :
    boundedProduct p q h = boundedProduct q p (by simpa [add_comm] using h) := by
  apply evaluation_injective
  funext x
  simp only [evaluate_boundedProduct, mul_comm]

end PCP.Algebraic.BinaryPolynomialSpace
