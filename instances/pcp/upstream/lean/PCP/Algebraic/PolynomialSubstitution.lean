/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Total degree under polynomial substitution

Substituting polynomials of total degree at most `d` multiplies the total-degree
bound by at most `d`. This applies to the certificate substitutions in Appendix D
and to affine line restrictions. It is a bound on formal polynomials.
-/

namespace PCP.Algebraic

open Finset MvPolynomial

variable {R σ τ : Type*} [CommSemiring R]

/-- A uniform bound on the degrees of substituted polynomials controls total degree. -/
theorem totalDegree_substitution_le (p : MvPolynomial σ R)
    (q : σ → MvPolynomial τ R) (d : ℕ) (hq : ∀ i, (q i).totalDegree ≤ d) :
    (eval₂Hom C q p).totalDegree ≤ p.totalDegree * d := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro s hs
  rw [eval₂Hom_monomial, Finsupp.prod]
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ s.support, (q i ^ s i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ s.support, s i * d := by
      apply sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hq i))
    _ = (s.sum fun _ n => n) * d := by rw [Finsupp.sum, sum_mul]
    _ ≤ p.totalDegree * d := Nat.mul_le_mul_right _ (le_totalDegree hs)

/-- Affine substitution never increases total degree. -/
theorem totalDegree_substitution_le_of_affine (p : MvPolynomial σ R)
    (q : σ → MvPolynomial τ R) (hq : ∀ i, (q i).totalDegree ≤ 1) :
    (eval₂Hom C q p).totalDegree ≤ p.totalDegree := by
  simpa using totalDegree_substitution_le p q 1 hq

end PCP.Algebraic
