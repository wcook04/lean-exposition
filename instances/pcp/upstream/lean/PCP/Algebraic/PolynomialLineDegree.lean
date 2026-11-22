/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PolynomialLine
import PCP.Algebraic.GridInterpolation
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Detecting total degree on lines through the origin

The coefficients of an origin-line restriction are evaluations of homogeneous
components. Consequently, over a finite field, a polynomial of total degree below
the field size cannot conceal a higher total degree on all origin lines.
-/

namespace PCP.Algebraic.PolynomialLine

open Finset MvPolynomial

variable {F σ : Type*} [Field F]

/-- An origin-line restriction of one monomial is a univariate monomial. -/
theorem restrict_zero_monomial (v : σ → F) (s : σ →₀ ℕ) (a : F) :
    restrict 0 v (monomial s a) =
      Polynomial.monomial s.degree (eval v (monomial s a)) := by
  classical
  have hs : s.degree = ∑ i ∈ s.support, s i := rfl
  rw [hs]
  simp only [restrict, eval₂Hom_monomial, Pi.zero_apply, Polynomial.C_0, zero_add,
    eval_monomial, Finsupp.prod, mul_pow, prod_mul_distrib,
    ← Polynomial.C_pow, ← map_prod, prod_pow_eq_pow_sum,
    ← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
  ring

/-- Coefficients along an origin line are the homogeneous pieces evaluated at its direction. -/
theorem coeff_restrict_zero (v : σ → F) (p : MvPolynomial σ F) (k : ℕ) :
    (restrict 0 v p).coeff k = eval v (homogeneousComponent k p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial s a =>
      rw [restrict_zero_monomial,
        homogeneousComponent_of_mem (isHomogeneous_monomial a rfl)]
      by_cases h : k = s.degree
      · subst k
        simp
      · simp [Polynomial.coeff_monomial, h, Ne.symm h]

variable [Fintype F]

/-- Formal degree bounds on every origin line bound the original total degree,
provided the original polynomial has total degree below the field size. -/
theorem totalDegree_le_of_origin_restrictions {n d : ℕ}
    (p : MvPolynomial (Fin n) F) (hp : p.totalDegree < Fintype.card F)
    (hline : ∀ v, (restrict 0 v p).natDegree ≤ d) : p.totalDegree ≤ d := by
  classical
  rw [totalDegree, Finset.sup_le_iff]
  intro s hs
  by_contra h
  have hds : d < s.degree := by
    change ¬s.degree ≤ d at h
    omega
  have hz : homogeneousComponent s.degree p = 0 := by
    apply GridInterpolation.eq_zero_of_eval_grid_eq_zero univ
    · intro i
      apply (degreeOf_le_totalDegree _ i).trans_lt
      have hsupport : (homogeneousComponent s.degree p).support ⊆ p.support := by
        rw [support_homogeneousComponent]
        exact filter_subset _ _
      simpa using (totalDegree_le_of_support_subset hsupport).trans_lt hp
    · intro a
      rw [← coeff_restrict_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hline _).trans_lt hds)
  have hc := congrArg (fun p => p.coeff s) hz
  simp [coeff_homogeneousComponent, mem_support_iff.mp hs] at hc

end PCP.Algebraic.PolynomialLine
