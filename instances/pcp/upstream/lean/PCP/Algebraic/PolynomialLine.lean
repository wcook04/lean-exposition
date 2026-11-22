/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PolynomialSubstitution
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Restricting a multivariate polynomial to an affine line

Definition 2.6: the lines table stores the univariate polynomial obtained by
substituting `uᵢ + X vᵢ` in each coordinate. Evaluation agrees at every point,
and the degree never exceeds the original total degree. The zero direction and
empty coordinate type are allowed. No uniqueness from finite evaluations is used.
-/

namespace PCP.Algebraic.PolynomialLine

open Finset

variable {R σ : Type*} [CommSemiring R]

/-- The point with parameter `a` on the line through `u` in direction `v`. -/
def point (u v : σ → R) (a : R) : σ → R := u + a • v

@[simp] theorem point_apply (u v : σ → R) (a : R) (i : σ) :
    point u v a i = u i + a * v i := rfl

@[simp] theorem point_zero (u v : σ → R) : point u v 0 = u := by
  simp [point]

/-- The formal univariate polynomial stored at one entry of the lines table. -/
noncomputable def restrict (u v : σ → R) : MvPolynomial σ R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (u i) + Polynomial.X * Polynomial.C (v i))

@[simp] theorem restrict_C (u v : σ → R) (a : R) :
    restrict u v (MvPolynomial.C a) = Polynomial.C a := by simp [restrict]

@[simp] theorem restrict_X (u v : σ → R) (i : σ) :
    restrict u v (MvPolynomial.X i) =
      Polynomial.C (u i) + Polynomial.X * Polynomial.C (v i) := by simp [restrict]

/-- Restriction is an identity of evaluations for every parameter, over any commutative semiring. -/
@[simp] theorem eval_restrict (u v : σ → R) (p : MvPolynomial σ R) (a : R) :
    (restrict u v p).eval a = MvPolynomial.eval (point u v a) p := by
  have h : (Polynomial.evalRingHom a).comp (restrict u v) =
      MvPolynomial.eval (point u v a) := by
    ext i <;> simp [restrict]
    ac_rfl
  exact congrArg (fun f : MvPolynomial σ R →+* R => f p) h

/-- Substitution by affine univariate polynomials cannot increase total degree. -/
theorem natDegree_restrict_le (u v : σ → R) (p : MvPolynomial σ R) :
    (restrict u v p).natDegree ≤ p.totalDegree := by
  classical
  have hq (i : σ) :
      (Polynomial.C (u i) + Polynomial.X * Polynomial.C (v i)).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simpa using Polynomial.natDegree_X_le)
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  simp only [restrict, MvPolynomial.eval₂Hom_monomial, Finsupp.prod]
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ s.support,
        ((Polynomial.C (u i) + Polynomial.X * Polynomial.C (v i)) ^ s i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ s.support, s i := by
      apply sum_le_sum
      intro i _
      exact Polynomial.natDegree_pow_le.trans
        ((Nat.mul_le_mul_left _ (hq i)).trans_eq (Nat.mul_one _))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hs

/-- Each entry of a degree-bounded lines table really is a degree-bounded univariate polynomial. -/
theorem natDegree_restrict_le_of_totalDegree_le (u v : σ → R)
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.totalDegree ≤ d) :
    (restrict u v p).natDegree ≤ d := (natDegree_restrict_le u v p).trans hp

end PCP.Algebraic.PolynomialLine
