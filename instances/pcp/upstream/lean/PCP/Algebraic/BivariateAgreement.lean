/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BerlekampWelchCertificate
import PCP.Algebraic.BivariateCleanRectangle
import PCP.Algebraic.BivariateAgreementFromRectangle
import PCP.Algebraic.BivariateColumnSelection
import PCP.Algebraic.BivariateAgreementBoost

/-!
# Bivariate agreement with explicit constants

The row--column agreement theorem used as ALMSS Theorem 69: a table within
`ε ≤ 1/100` of degree-`d` polynomial rows and columns is within `4ε` of a
bivariate polynomial of individual degrees at most `d`. Here `d > 0` and
`|F| ≥ 1000*d^3`. The approximating rows and columns need not be optimal.

The two-variable Arora--Safra construction: if all rows have degree at most `d`
and `10d` distinct columns each have a degree-`d` approximation with error at
most `1/10`, then there is an actual bivariate polynomial of individual degree
at most `d` within distance `1/9`. We use the explicit sufficient field size
`1000*d^3` and require `d > 0`.

The proof constructs the error-locator certificate by polynomial linear algebra,
selects nonzero columns, counts clean rows, and interpolates. No clean rectangle,
certificate, or nearby polynomial is supplied as a hypothesis.
-/

namespace PCP.Algebraic.BivariateAgreement

open Finset AffineLineSampling PointLineCrossing BivariateCleanRectangle

/-- One explicit cubic field-size constant satisfies the algebraic and counting bounds. -/
theorem fieldSize_bounds {d q : ℕ} (hd : 0 < d) (hq : 1000 * d ^ 3 ≤ q) :
    2 * ((5 * d + 2) * d) < q ∧ 2 * d < q ∧ (5 * d + 1) * d < q ∧
      10 * (d + 1) * ((5 * d + 1) * d) ≤ q ∧ 20 * d ≤ q := by
  have hd1 : 1 ≤ d := hd
  have hs : d ≤ d * d := by nlinarith
  have hc : d * d ≤ d * d * d := by
    have h := Nat.mul_le_mul_left (d * d) hd1
    simpa only [mul_one] using h
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

/-- Close polynomial columns and exact polynomial rows construct a nearby bivariate
polynomial. This is the two-dimensional coarse agreement theorem, with all its
algebraic existence steps proved rather than supplied. -/
theorem exists_nearby_of_close_columns (hd : 0 < d)
    (hq : 1000 * d ^ 3 ≤ Fintype.card F)
    (a : Fin (10 * d) → F) (ha : Function.Injective a)
    (C : Fin (10 * d) → Polynomial F) (hC : ∀ i, (C i).natDegree ≤ d)
    (R : F → Polynomial F) (hR : ∀ y, (R y).natDegree ≤ d)
    (hcol : ∀ i, relativeDistance (fun y => (R y).eval (a i)) (C i).eval ≤ (1 : ℚ) / 10) :
    ∃ P : MvPolynomial (Fin 2) F, (∀ j, P.degreeOf j ≤ d) ∧
      (∀ i, rowPolynomial P (a i) = C i) ∧
      relativeDistance R (columnPolynomial P) ≤ (1 : ℚ) / 9 ∧
      relativeDistance (fun z : F × F => (R z.2).eval z.1)
        (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ (1 : ℚ) / 9 := by
  classical
  obtain ⟨hlarge, hex, hey, hzero, hdq⟩ := fieldSize_bounds hd hq
  have hqpos : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  let S := univ.filter (fun y => rowErrors a C R y ≤ 2 * d)
  have hbad := fraction_many_rowErrors_le a C R (2 * d) hcol
  have hratio : (Fintype.card (Fin (10 * d)) : ℚ) * (1 / 10) /
      ((2 * d : ℕ) + 1) ≤ 1 / 2 := by
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 * d + 1)).mpr
    ring_nf
    linarith
  have hgood := fraction_good_ge (fun y => 2 * d < rowErrors a C R y)
    (fun _ : F => False) (fun y => rowErrors a C R y ≤ 2 * d)
    (fun _ hy _ => le_of_not_gt hy)
  have hf : fraction (fun _ : F => False) = 0 := by simp [fraction_eq_expect]
  have hS : (1 : ℚ) / 2 ≤ fraction (fun y => rowErrors a C R y ≤ 2 * d) := by
    rw [hf] at hgood
    linarith [hbad.trans hratio]
  rw [fraction_eq_card_filter] at hS
  have hScount : (Fintype.card F : ℚ) / 2 ≤ S.card := by
    have h := (le_div_iff₀ hqpos).mp hS
    simpa only [S, one_div_mul_eq_div] using h
  have hSlarge : (d + 2 * (2 * d) + 2) * d < S.card := by
    have hlarge' : (2 : ℚ) * ((5 * d + 2) * d) < Fintype.card F := by
      exact_mod_cast hlarge
    have h : ((d + 2 * (2 * d) + 2) * d : ℚ) < S.card := by nlinarith
    exact_mod_cast h
  have hgoodRows : ∀ y ∈ S, ∃ s : Polynomial F, s.natDegree ≤ d ∧
      (BerlekampWelch.errors a (fun i => (C i).eval y) s).card ≤ 2 * d := by
    intro y hy
    refine ⟨R y, hR y, ?_⟩
    simpa only [BerlekampWelch.errors, rowErrors, hammingDist] using (mem_filter.mp hy).2
  obtain ⟨E, N, hEnz, hEx, hNx, hEy, _, heq⟩ :=
    BerlekampWelchCertificate.exists_certificate_of_good_specializations a ha C hC S hSlarge
      hgoodRows (by simp only [Fintype.card_fin]; omega)
  have hEy' : E.degreeOf 1 ≤ (5 * d + 1) * d := by
    convert hEy using 1; ring
  have hsize : ∀ j, E.degreeOf j < Fintype.card F := by
    intro j
    fin_cases j
    · exact hEx.trans_lt hex
    · exact hEy'.trans_lt hey
  obtain ⟨b, hb⟩ := exists_nonzero_columns (d := d) a ha E hEnz hEx hsize
    (by simp only [Fintype.card_fin]; omega)
  let J := (univ : Finset (Fin (d + 1))).map b
  have hJ : J.card = d + 1 := by simp [J]
  let B := univ.filter (fun y => ∀ i ∈ J, (R y).eval (a i) = (C i).eval y)
  have hBfrac := fraction_clean_rows_ge a ha C R E N J hR hEx hNx hEy' heq
    (by intro i hi; obtain ⟨j, _, rfl⟩ := mem_map.mp hi; exact hb j)
    (by simp only [Fintype.card_fin]; omega) hcol
  have hzero' : (J.card : ℚ) * ((5 * d + 1) * d : ℕ) / Fintype.card F ≤ 1 / 10 := by
    apply (div_le_iff₀ hqpos).mpr
    rw [hJ]
    have h : (10 : ℚ) * (d + 1) * ((5 * d + 1) * d) ≤ Fintype.card F := by
      exact_mod_cast hzero
    push_cast
    nlinarith
  have hBcount : (2 : ℚ) / 5 * Fintype.card F ≤ B.card := by
    have h : (2 : ℚ) / 5 ≤ fraction
        (fun y => ∀ i ∈ J, (R y).eval (a i) = (C i).eval y) := by
      linarith
    rw [fraction_eq_card_filter] at h
    exact (le_div_iff₀ hqpos).mp h
  apply BivariateAgreementFromRectangle.exists_nearby_polynomial_one_ninth
    a ha C hC R hR b b.injective B ?_ hcol ?_ (Fintype.card_fin (10 * d))
  · intro y hy j
    exact (mem_filter.mp hy).2 (b j) (mem_map.mpr ⟨j, mem_univ j, rfl⟩)
  · have h : (20 : ℚ) * d ≤ Fintype.card F := by exact_mod_cast hdq
    nlinarith

/-- The bivariate agreement theorem used as ALMSS Theorem 69, with explicit
constants. Approximating polynomial rows and columns are arbitrary; they need
not be optimal. The conclusion constructs the comparison polynomial. -/
theorem exists_polynomial_of_row_column_agreement (hd : 0 < d)
    (hq : 1000 * d ^ 3 ≤ Fintype.card F)
    (f : F × F → F) (R C : F → Polynomial F)
    (hR : ∀ y, (R y).natDegree ≤ d) (hC : ∀ x, (C x).natDegree ≤ d)
    {ε : ℚ} (hrows : relativeDistance f (fun z => (R z.2).eval z.1) ≤ ε)
    (hcols : relativeDistance f (fun z => (C z.1).eval z.2) ≤ ε)
    (hε : ε ≤ 1 / 100) :
    ∃ P : MvPolynomial (Fin 2) F, (∀ j, P.degreeOf j ≤ d) ∧
      relativeDistance f (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ 4 * ε := by
  have hdq := (fieldSize_bounds hd hq).2.2.2.2
  obtain ⟨a, ha⟩ := BivariateColumnSelection.exists_good_columns f R C hrows hcols hε hdq
  obtain ⟨P, hP, _, _, hclose⟩ := exists_nearby_of_close_columns hd hq a a.injective
    (fun i => C (a i)) (fun i => hC (a i)) R hR ha
  have hnear : relativeDistance f (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤
      ε + 1 / 9 :=
    (relativeDistance_triangle f (fun z => (R z.2).eval z.1) _).trans
      (add_le_add hrows hclose)
  refine ⟨P, hP, BivariateAgreementBoost.distance_le_four_mul f R C hR hC P hP
    hrows hcols hnear ?_⟩
  have hqpos : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hfrac : (d : ℚ) / Fintype.card F ≤ 1 / 20 := by
    apply (div_le_iff₀ hqpos).mpr
    have h : (20 : ℚ) * d ≤ Fintype.card F := by exact_mod_cast hdq
    linarith
  linarith

end PCP.Algebraic.BivariateAgreement
