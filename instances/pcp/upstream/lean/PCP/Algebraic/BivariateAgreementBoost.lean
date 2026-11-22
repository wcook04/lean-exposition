/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BivariateAgreementFromRectangle

/-!
# Sharpening coarse bivariate proximity

An actual bivariate polynomial close enough to a word is within four times the
row/column approximation error. The proof charges each differing formal row
against crossing discrepancies, using polynomial separation and a uniform
transverse bound supplied by the column polynomials.

The nearby polynomial and its coarse distance bound are explicit inputs.
This module proves the sharpening step; it does not assume or establish the
existence of that initial polynomial. Rows `R y` vary in `X`, while columns
`C x` vary in `Y`, matching the clean-rectangle modules' source orientation.
-/

namespace PCP.Algebraic.BivariateAgreementBoost

open Finset PointLineCrossing AffineLineSampling
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

/-- Uniform transverse error turns polynomial separation into a weighted bound
on the fraction of differing formal rows. -/
theorem rowDistance_mul_le (R C : F → Polynomial F)
    (hR : ∀ y, (R y).natDegree ≤ d)
    (P : MvPolynomial (Fin 2) F) (hP : ∀ j, P.degreeOf j ≤ d) {κ : ℚ}
    (htrans : ∀ y, relativeDistance (fun x => (C x).eval y)
      (fun x => MvPolynomial.eval ![x, y] P) ≤ κ) :
    (1 - (d : ℚ) / Fintype.card F - κ) * relativeDistance R (columnPolynomial P) ≤
      relativeDistance (fun z : F × F => (R z.2).eval z.1)
        (fun z => (C z.1).eval z.2) := by
  classical
  have hslice (y : F) : (columnPolynomial P y).natDegree ≤ d :=
    (natDegree_axisRestrict_le _ _ _).trans (hP 0)
  have hpoint (y : F) :
      (1 - (d : ℚ) / Fintype.card F - κ) *
        (if R y ≠ columnPolynomial P y then (1 : ℚ) else 0) ≤
      relativeDistance (R y).eval (fun x => (C x).eval y) := by
    split_ifs with hy
    · simp only [mul_one]
      have hsep := PointLineTest.univariate_distance_ge
        (R y) (columnPolynomial P y) (hR y) (hslice y) hy
      have ht := relativeDistance_triangle (R y).eval (fun x => (C x).eval y)
        (columnPolynomial P y).eval
      have htrans' := htrans y
      simp only [eval_columnPolynomial] at hsep ht
      linarith
    · simp only [mul_zero]
      exact relativeDistance_nonneg _ _
  have hmean := expect_le_expect (s := univ) (fun y _ => hpoint y)
  rw [← mul_expect, ← fraction_eq_expect, fraction_ne_eq_relativeDistance] at hmean
  have he : (𝔼 y, relativeDistance (R y).eval (fun x => (C x).eval y)) =
      relativeDistance (fun z : F × F => (R z.2).eval z.1)
        (fun z => (C z.1).eval z.2) := by
    rw [Fintype.expect_eq_sum_div_card]
    have h := relativeDistance_comp_equiv (Equiv.prodComm F F)
      (fun z : F × F => (R z.2).eval z.1) (fun z => (C z.1).eval z.2)
    rw [relativeDistance_prod] at h
    exact h
  rwa [he] at hmean

/-- Close polynomial columns control the comparison error on every fixed `Y` row. -/
theorem transverse_error_le (f : F × F → F) (C : F → Polynomial F)
    (hC : ∀ x, (C x).natDegree ≤ d)
    (P : MvPolynomial (Fin 2) F) (hP : ∀ j, P.degreeOf j ≤ d) {ε ρ : ℚ}
    (hcols : relativeDistance f (fun z => (C z.1).eval z.2) ≤ ε)
    (hnear : relativeDistance f (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ ρ)
    (y : F) :
    relativeDistance (fun x => (C x).eval y) (fun x => MvPolynomial.eval ![x, y] P) ≤
      ε + ρ + (d : ℚ) / Fintype.card F := by
  have hslice (x : F) : (rowPolynomial P x).natDegree ≤ d :=
    (natDegree_axisRestrict_le _ _ _).trans (hP 1)
  have htrans := polynomial_transverse_distance_le C (rowPolynomial P) hC hslice y
  simp only [eval_rowPolynomial] at htrans
  have ht := relativeDistance_triangle (fun z : F × F => (C z.1).eval z.2) f
    (fun z => MvPolynomial.eval ![z.1, z.2] P)
  rw [relativeDistance_comm (fun z : F × F => (C z.1).eval z.2) f] at ht
  linarith

/-- Under the coarse proximity threshold, at most `3ε` of the formal rows differ. -/
theorem rowDistance_le_three_mul (f : F × F → F) (R C : F → Polynomial F)
    (hR : ∀ y, (R y).natDegree ≤ d) (hC : ∀ x, (C x).natDegree ≤ d)
    (P : MvPolynomial (Fin 2) F) (hP : ∀ j, P.degreeOf j ≤ d) {ε ρ : ℚ}
    (hrows : relativeDistance f (fun z => (R z.2).eval z.1) ≤ ε)
    (hcols : relativeDistance f (fun z => (C z.1).eval z.2) ≤ ε)
    (hnear : relativeDistance f (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ ρ)
    (hsmall : ρ + ε + 2 * ((d : ℚ) / Fintype.card F) ≤ 1 / 3) :
    relativeDistance R (columnPolynomial P) ≤ 3 * ε := by
  have hweighted := rowDistance_mul_le R C hR P hP
    (transverse_error_le f C hC P hP hcols hnear)
  have hcross := relativeDistance_triangle (fun z : F × F => (R z.2).eval z.1) f
    (fun z => (C z.1).eval z.2)
  rw [relativeDistance_comm (fun z : F × F => (R z.2).eval z.1) f] at hcross
  have hm := relativeDistance_nonneg R (columnPolynomial P)
  nlinarith

/-- A supplied coarse approximation sharpens to the `4ε` bivariate agreement bound. -/
theorem distance_le_four_mul (f : F × F → F) (R C : F → Polynomial F)
    (hR : ∀ y, (R y).natDegree ≤ d) (hC : ∀ x, (C x).natDegree ≤ d)
    (P : MvPolynomial (Fin 2) F) (hP : ∀ j, P.degreeOf j ≤ d) {ε ρ : ℚ}
    (hrows : relativeDistance f (fun z => (R z.2).eval z.1) ≤ ε)
    (hcols : relativeDistance f (fun z => (C z.1).eval z.2) ≤ ε)
    (hnear : relativeDistance f (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ ρ)
    (hsmall : ρ + ε + 2 * ((d : ℚ) / Fintype.card F) ≤ 1 / 3) :
    relativeDistance f (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ 4 * ε := by
  have hrow := rowDistance_le_three_mul f R C hR hC P hP hrows hcols hnear hsmall
  have hgrid := BivariateAgreementFromRectangle.gridDistance_le_rowDistance R P
  have ht := relativeDistance_triangle f (fun z : F × F => (R z.2).eval z.1)
    (fun z => MvPolynomial.eval ![z.1, z.2] P)
  linarith

end PCP.Algebraic.BivariateAgreementBoost
