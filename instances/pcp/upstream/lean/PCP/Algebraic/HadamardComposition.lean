/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Hadamard
import PCP.Algebraic.PolynomialSubstitution
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Translating a univariate polynomial query into a binary Hadamard query

Claim 3.7 / Appendix A. A binary linear coordinate equivalence expresses a
univariate polynomial over the coefficient algebra as binary coordinate
polynomials without increasing its degree. Substitution into an affine binary
query, followed by multilinear reduction, constructs the required bounded query.
The construction includes affine constants and degree zero. No construction-time
certificate is asserted.

The claim's final homogeneity clause is not formalized: with multilinear query
labels it fails in general (over `GF(4)` with coordinates in the basis `1, ω`,
`P = Y^3` and `L = Z₁` give `Z₁ + Z₂ + Z₁Z₂`). Only the scalar case `P = η·Y` is
used, where the label is homogeneous linear; it is `HadamardWeights.scaleLabel`,
a bijection for `η ≠ 0`.
-/

namespace PCP.Algebraic.HadamardComposition

open Finset MvPolynomial BinaryPolynomialSpace

variable {F σ : Type*} [CommRing F] [Algebra (ZMod 2) F]

/-- Apply a binary linear functional to every formal coefficient. This operation
is linear, but is deliberately not assumed to preserve multiplication. -/
noncomputable def mapCoefficients (ℓ : F →ₗ[ZMod 2] ZMod 2)
    (q : MvPolynomial σ F) : MvPolynomial σ (ZMod 2) :=
  ∑ s ∈ q.support, monomial s (ℓ (q.coeff s))

theorem totalDegree_mapCoefficients_le (ℓ : F →ₗ[ZMod 2] ZMod 2)
    (q : MvPolynomial σ F) : (mapCoefficients ℓ q).totalDegree ≤ q.totalDegree := by
  classical
  apply totalDegree_finsetSum_le
  intro s hs
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree hs)

/-- Binary evaluation commutes with a binary-linear map of coefficients. -/
theorem eval_mapCoefficients (ℓ : F →ₗ[ZMod 2] ZMod 2)
    (q : MvPolynomial σ F) (x : σ → ZMod 2) :
    eval x (mapCoefficients ℓ q) =
      ℓ (eval (fun i => algebraMap (ZMod 2) F (x i)) q) := by
  classical
  rw [mapCoefficients, map_sum, eval_eq, map_sum]
  apply sum_congr rfl
  intro s _
  rw [eval_monomial, Finsupp.prod]
  have h := ℓ.map_smul (∏ i ∈ s.support, x i ^ s i) (q.coeff s)
  simpa only [smul_eq_mul, Algebra.smul_def, map_prod, map_pow, mul_comm] using h.symm

variable {t r : ℕ}

/-- The formal linear polynomial reconstructing an algebra element from binary coordinates. -/
noncomputable def coordinatePolynomial (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) :
    MvPolynomial (Fin t) F :=
  ∑ i, monomial (Finsupp.single i 1) (ρ.symm (Pi.single i 1))

theorem totalDegree_coordinatePolynomial_le
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) :
    (coordinatePolynomial ρ).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_monomial_le _ _).trans (by simp)

theorem eval_coordinatePolynomial
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (x : Fin t → ZMod 2) :
    eval (fun i => algebraMap (ZMod 2) F (x i)) (coordinatePolynomial ρ) = ρ.symm x := by
  have hx : (∑ i : Fin t, x i • Pi.single i (1 : ZMod 2)) = x := by
    funext j
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  have h := congrArg ρ.symm hx
  simp only [map_sum, map_smul] at h
  simpa [coordinatePolynomial, eval_monomial, Algebra.smul_def, mul_comm] using h

/-- Substitute the coordinate reconstruction into the given univariate polynomial. -/
noncomputable def fieldPolynomial
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F) :
    MvPolynomial (Fin t) F := P.eval₂ C (coordinatePolynomial ρ)

theorem totalDegree_fieldPolynomial_le
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F) :
    (fieldPolynomial ρ P).totalDegree ≤ P.natDegree := by
  rw [fieldPolynomial, Polynomial.eval₂_eq_sum_range]
  apply totalDegree_finsetSum_le
  intro k hk
  calc
    _ ≤ (C (P.coeff k) : MvPolynomial (Fin t) F).totalDegree +
        (coordinatePolynomial ρ ^ k).totalDegree := totalDegree_mul _ _
    _ = (coordinatePolynomial ρ ^ k).totalDegree := by simp
    _ ≤ k * (coordinatePolynomial ρ).totalDegree := totalDegree_pow _ _
    _ ≤ k * 1 := Nat.mul_le_mul_left k (totalDegree_coordinatePolynomial_le ρ)
    _ ≤ P.natDegree := by simpa only [mul_one] using Nat.le_of_lt_succ (mem_range.mp hk)

theorem eval_fieldPolynomial
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F) (x : Fin t → ZMod 2) :
    eval (fun i => algebraMap (ZMod 2) F (x i)) (fieldPolynomial ρ P) =
      P.eval (ρ.symm x) := by
  rw [fieldPolynomial, Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]
  simp only [map_sum, map_mul, map_pow, eval_C, eval_coordinatePolynomial]

/-- A formal binary polynomial for one output coordinate of the univariate evaluation. -/
noncomputable def outputCoordinate
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F) (i : Fin t) :
    MvPolynomial (Fin t) (ZMod 2) :=
  mapCoefficients ((LinearMap.proj i).comp ρ.toLinearMap) (fieldPolynomial ρ P)

theorem totalDegree_outputCoordinate_le
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F) (i : Fin t) :
    (outputCoordinate ρ P i).totalDegree ≤ P.natDegree :=
  (totalDegree_mapCoefficients_le _ _).trans (totalDegree_fieldPolynomial_le ρ P)

@[simp] theorem eval_outputCoordinate
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F) (x : Fin t → ZMod 2)
    (i : Fin t) : eval x (outputCoordinate ρ P i) = ρ (P.eval (ρ.symm x)) i := by
  simp [outputCoordinate, eval_mapCoefficients, eval_fieldPolynomial]

/-- The affine query after substituting the coordinate polynomials. -/
noncomputable def formalQuery
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F)
    (L : Coefficients t 1) : MvPolynomial (Fin t) (ZMod 2) :=
  eval₂Hom C (outputCoordinate ρ P) (polynomial t 1 L)

theorem totalDegree_formalQuery_le
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F) (L : Coefficients t 1) :
    (formalQuery ρ P L).totalDegree ≤ P.natDegree := by
  apply (totalDegree_substitution_le _ _ P.natDegree
    (totalDegree_outputCoordinate_le ρ P)).trans
  exact (Nat.mul_le_mul_right _ (totalDegree_polynomial_le L)).trans_eq (one_mul _)

theorem eval_formalQuery
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F)
    (L : Coefficients t 1) (x : Fin t → ZMod 2) :
    eval x (formalQuery ρ P L) = evaluate (ρ (P.eval (ρ.symm x))) L := by
  change eval x (eval₂ C (outputCoordinate ρ P) (polynomial t 1 L)) = _
  rw [← eval_assoc]
  simp only [Function.comp_def, eval_outputCoordinate, evaluate_apply]

/-- The actual bounded query of Claim 3.7, stored in finite binary coefficient coordinates. -/
noncomputable def query
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F)
    (L : Coefficients t 1) (_hP : P.natDegree ≤ r) : Coefficients t r :=
  coefficients (multilinearReduction (formalQuery ρ P L))

theorem polynomial_query
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F)
    (L : Coefficients t 1) (hP : P.natDegree ≤ r) :
    polynomial t r (query ρ P L hP) = multilinearReduction (formalQuery ρ P L) :=
  polynomial_coefficients _ (multilinearReduction_isMultilinear _)
    ((totalDegree_multilinearReduction_le _).trans
      ((totalDegree_formalQuery_le ρ P L).trans hP))

/-- Claim 3.7: one degree-`r` binary query evaluates the affine observation of `P(u)`. -/
theorem evaluate_query
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F)
    (L : Coefficients t 1) (hP : P.natDegree ≤ r) (u : F) :
    evaluate (ρ u) (query ρ P L hP) = evaluate (ρ (P.eval u)) L := by
  rw [query, evaluate_reduced_coefficients _ ((totalDegree_formalQuery_le ρ P L).trans hP),
    eval_formalQuery, ρ.symm_apply_apply]

/-- The same translation identity in the paper's Hadamard-encoding notation. -/
theorem encode_query
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F)
    (L : Coefficients t 1) (hP : P.natDegree ≤ r) (u : F) :
    Hadamard.encode r (ρ u) (query ρ P L hP) =
      Hadamard.encode 1 (ρ (P.eval u)) L :=
  evaluate_query ρ P L hP u

/-- Claim 3.7 supplies one query that works simultaneously for every input. -/
theorem exists_query
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F)
    (L : Coefficients t 1) (hP : P.natDegree ≤ r) :
    ∃ Λ : Coefficients t r, ∀ u : F,
      Hadamard.encode r (ρ u) Λ = Hadamard.encode 1 (ρ (P.eval u)) L :=
  ⟨query ρ P L hP, encode_query ρ P L hP⟩

/-- Canonical reduced query coordinates make the translation unique. -/
theorem query_unique
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (P : Polynomial F)
    (L : Coefficients t 1) (hP : P.natDegree ≤ r) (Λ : Coefficients t r)
    (hΛ : ∀ u : F, evaluate (ρ u) Λ = evaluate (ρ (P.eval u)) L) :
    Λ = query ρ P L hP := by
  apply evaluation_injective
  funext x
  rw [← ρ.apply_symm_apply x]
  exact (hΛ (ρ.symm x)).trans (evaluate_query ρ P L hP (ρ.symm x)).symm

end PCP.Algebraic.HadamardComposition
