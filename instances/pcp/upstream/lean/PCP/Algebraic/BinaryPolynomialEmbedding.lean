/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryPolynomialProduct

/-!
# Changing degree bounds for binary polynomial queries

The inclusions preserve the formal multilinear representative. Products between
different degree bounds are reduced before taking coefficients, and have the
expected pointwise evaluation on the Boolean cube.
-/

namespace PCP.Algebraic.BinaryPolynomialSpace

open MvPolynomial

variable {t a b c r : ℕ}

/-- Include a query in a larger degree space, padding its coefficients by zero. -/
noncomputable def embed (_h : a ≤ b) : Coefficients t a →ₗ[ZMod 2] Coefficients t b where
  toFun p := coefficients (polynomial t a p)
  map_add' p q := by ext s; simp [coefficients]
  map_smul' z p := by ext s; simp [coefficients]

@[simp] theorem polynomial_embed (h : a ≤ b) (p : Coefficients t a) :
    polynomial t b (embed h p) = polynomial t a p :=
  polynomial_coefficients _ (polynomial_isMultilinear p)
    ((totalDegree_polynomial_le p).trans h)

@[simp] theorem evaluate_embed (h : a ≤ b) (x : Fin t → ZMod 2)
    (p : Coefficients t a) : evaluate x (embed h p) = evaluate x p := by
  simp only [evaluate_apply, polynomial_embed]

theorem embed_injective (h : a ≤ b) : Function.Injective (embed (t := t) h) := by
  intro p q hpq
  apply polynomial_injective
  simpa only [polynomial_embed] using congrArg (polynomial t b) hpq

@[simp] theorem embed_refl (p : Coefficients t a) : embed (le_refl a) p = p := by
  apply polynomial_injective
  exact polynomial_embed _ p

@[simp] theorem embed_embed (hab : a ≤ b) (hbc : b ≤ c) (p : Coefficients t a) :
    embed hbc (embed hab p) = embed (hab.trans hbc) p := by
  apply polynomial_injective
  simp only [polynomial_embed]

@[simp] theorem embed_constant (h : a ≤ b) (z : ZMod 2) :
    embed (t := t) h (constant z) = constant z := by
  apply evaluation_injective
  funext x
  simp

@[simp] theorem embed_variableCoeff (h : a ≤ b) (ha : 1 ≤ a) (i : Fin t) :
    embed h (variableCoeff ha i) = variableCoeff (ha.trans h) i := by
  apply evaluation_injective
  funext x
  simp

/-- A product of queries from two degree spaces, included in a common target space. -/
noncomputable def mixedProduct (_h : a + b ≤ r)
    (p : Coefficients t a) (q : Coefficients t b) : Coefficients t r :=
  coefficients (multilinearReduction (polynomial t a p * polynomial t b q))

theorem polynomial_mixedProduct (h : a + b ≤ r)
    (p : Coefficients t a) (q : Coefficients t b) :
    polynomial t r (mixedProduct h p q) =
      multilinearReduction (polynomial t a p * polynomial t b q) := by
  apply polynomial_coefficients _ (multilinearReduction_isMultilinear _)
  exact (totalDegree_multilinearReduction_le _).trans
    ((totalDegree_mul _ _).trans
      ((Nat.add_le_add (totalDegree_polynomial_le p) (totalDegree_polynomial_le q)).trans h))

@[simp] theorem evaluate_mixedProduct (h : a + b ≤ r) (x : Fin t → ZMod 2)
    (p : Coefficients t a) (q : Coefficients t b) :
    evaluate x (mixedProduct h p q) = evaluate x p * evaluate x q := by
  simp only [evaluate_apply, polynomial_mixedProduct, eval_multilinearReduction, map_mul]

theorem mixedProduct_add_left (h : a + b ≤ r)
    (p p' : Coefficients t a) (q : Coefficients t b) :
    mixedProduct h (p + p') q = mixedProduct h p q + mixedProduct h p' q := by
  apply evaluation_injective
  funext x
  simp only [evaluate_mixedProduct, map_add, add_mul]

theorem mixedProduct_add_right (h : a + b ≤ r)
    (p : Coefficients t a) (q q' : Coefficients t b) :
    mixedProduct h p (q + q') = mixedProduct h p q + mixedProduct h p q' := by
  apply evaluation_injective
  funext x
  simp only [evaluate_mixedProduct, map_add, mul_add]

end PCP.Algebraic.BinaryPolynomialSpace
