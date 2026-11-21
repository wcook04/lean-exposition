/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BerlekampWelch
import PCP.Algebraic.PointLineCrossing
import PCP.Algebraic.PointedLineSampling
import PCP.Algebraic.GridInterpolation

/-!
# Clean rows from a bivariate error-locator certificate

Rows are polynomials in `X`, indexed by `y`; columns are polynomials in `Y`,
indexed by distinct parameters `a i`. A Berlekamp--Welch certificate identifies
the numerator with the row polynomial times the error locator on every row with
few errors. On selected columns where the locator is a nonzero polynomial,
the root bound excludes only a controlled fraction of rows. The remaining rows
agree with every selected column, giving a clean rectangle.

This is the counting and cancellation step in Arora--Safra Lemma 5.2.2. The
polynomial certificate is an explicit input to the counting bound. This file
also selects nonzero columns from its degree bounds; `BerlekampWelchCertificate`
constructs the certificate, and `BivariateAgreement` assembles these steps.
-/

namespace PCP.Algebraic.BivariateCleanRectangle

open Finset AffineLineSampling PointedLineSampling PointLineCrossing
open scoped BigOperators

section Fractions

variable {A I : Type*} [Fintype A]

/-- A finite union has fraction at most the sum of its constituent fractions. -/
theorem fraction_exists_mem_le (J : Finset I) (E : I → A → Prop) :
    fraction (fun x => ∃ i ∈ J, E i x) ≤ ∑ i ∈ J, fraction (E i) := by
  classical
  have hpoint (x : A) :
      (if ∃ i ∈ J, E i x then (1 : ℚ) else 0) ≤
        ∑ i ∈ J, if E i x then (1 : ℚ) else 0 := by
    by_cases hx : ∃ i ∈ J, E i x
    · obtain ⟨i, hi, hei⟩ := hx
      rw [ite_eq_left ⟨i, hi, hei⟩]
      calc
        _ = if E i x then (1 : ℚ) else 0 := by simp [hei]
        _ ≤ _ := single_le_sum (f := fun j : I => if E j x then (1 : ℚ) else 0)
          (fun j _ => by split_ifs <;> norm_num) hi
    · rw [ite_eq_right hx]
      exact sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  have h := expect_le_expect (s := univ) (fun x _ => hpoint x)
  simpa only [expect_sum_comm, ← fraction_eq_expect] using h

/-- Removing two exceptional events leaves at least one minus their total fraction. -/
theorem fraction_good_ge [Nonempty A] (B D G : A → Prop)
    (hgood : ∀ x, ¬ B x → ¬ D x → G x) :
    1 - fraction B - fraction D ≤ fraction G := by
  classical
  have hpoint (x : A) :
      (1 : ℚ) - (if B x then 1 else 0) - (if D x then 1 else 0) ≤
        if G x then 1 else 0 := by
    by_cases hb : B x <;> by_cases hd : D x
    all_goals simp only [hb, hd, ↓reduceIte]
    · split_ifs <;> norm_num
    · split_ifs <;> norm_num
    · split_ifs <;> norm_num
    · simp [hgood x hb hd]
  have h := expect_le_expect (s := univ) (fun x _ => hpoint x)
  simpa only [expect_sub_distrib, Fintype.expect_const, ← fraction_eq_expect] using h

end Fractions

section RowErrors

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I]

/-- The number of disagreements in a row, restricted to the given columns. -/
def rowErrors (a : I → F) (C : I → Polynomial F) (R : F → Polynomial F) (y : F) : ℕ :=
  hammingDist (fun i => (R y).eval (a i)) (fun i => (C i).eval y)

/-- Averaging errors by columns bounds the mean number of errors in a row. -/
theorem expect_rowErrors_le (a : I → F) (C : I → Polynomial F) (R : F → Polynomial F)
    {ε : ℚ} (hcol : ∀ i, relativeDistance (fun y => (R y).eval (a i)) (C i).eval ≤ ε) :
    (𝔼 y, (rowErrors a C R y : ℚ)) ≤ Fintype.card I * ε := by
  classical
  have hrow (y : F) : (rowErrors a C R y : ℚ) =
      ∑ i, if (R y).eval (a i) ≠ (C i).eval y then (1 : ℚ) else 0 := by
    simp only [rowErrors, hammingDist, natCast_card_filter]
  simp_rw [hrow]
  rw [expect_sum_comm]
  have hmean (i : I) :
      (𝔼 y, if (R y).eval (a i) ≠ (C i).eval y then (1 : ℚ) else 0) =
        relativeDistance (fun y => (R y).eval (a i)) (C i).eval := by
    rw [← fraction_eq_expect, fraction_ne_eq_relativeDistance]
  simp_rw [hmean]
  calc
    _ ≤ ∑ _i : I, ε := sum_le_sum (fun i _ => hcol i)
    _ = _ := by simp

/-- Markov's inequality controls the fraction of rows with more than `e` errors. -/
theorem fraction_many_rowErrors_le (a : I → F) (C : I → Polynomial F)
    (R : F → Polynomial F) (e : ℕ) {ε : ℚ}
    (hcol : ∀ i, relativeDistance (fun y => (R y).eval (a i)) (C i).eval ≤ ε) :
    fraction (fun y => e < rowErrors a C R y) ≤ (Fintype.card I * ε) / (e + 1) := by
  have he : (0 : ℚ) < (e : ℚ) + 1 := by positivity
  have h := fraction_ge_le (fun y => (rowErrors a C R y : ℚ))
    (fun _ => Nat.cast_nonneg _) ((e : ℚ) + 1) he
  have hsub : fraction (fun y => e < rowErrors a C R y) ≤
      fraction (fun y => (e : ℚ) + 1 ≤ rowErrors a C R y) := by
    apply fraction_mono
    intro y hy
    exact_mod_cast Nat.succ_le_of_lt hy
  exact (hsub.trans h).trans
    (div_le_div_of_nonneg_right (expect_rowErrors_le a C R hcol) he.le)

omit [Fintype I] [DecidableEq F] in
/-- A union of zero sets of nonzero bounded-degree column polynomials is small. -/
theorem fraction_exists_column_zero_le (J : Finset I) (E : I → Polynomial F) (D : ℕ)
    (hne : ∀ i ∈ J, E i ≠ 0) (hdeg : ∀ i ∈ J, (E i).natDegree ≤ D) :
    fraction (fun y => ∃ i ∈ J, (E i).eval y = 0) ≤ J.card * D / Fintype.card F := by
  classical
  apply (fraction_exists_mem_le J (fun i y => (E i).eval y = 0)).trans
  have hi (i : I) (hi : i ∈ J) :
      fraction (fun y => (E i).eval y = 0) ≤ (D : ℚ) / Fintype.card F := by
    rw [fraction_eq_card_filter]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (UnivariateDistance.card_eval_zero_le (E i) (hne i hi)).trans (hdeg i hi)
  calc
    _ ≤ ∑ _i ∈ J, (D : ℚ) / Fintype.card F := sum_le_sum hi
    _ = _ := by simp [mul_div_assoc]

end RowErrors

section Certificate

variable {F I : Type*} [Field F] [Fintype I] {d e D : ℕ}

/-- On a row with at most `e` errors, the certificate numerator is exactly the
row polynomial times the certificate locator. The identity includes zero slices. -/
theorem certificate_row_eq (a : I → F) (ha : Function.Injective a)
    (C : I → Polynomial F) (R : F → Polynomial F)
    (E N : MvPolynomial (Fin 2) F)
    (hR : ∀ y, (R y).natDegree ≤ d)
    (hE : E.degreeOf 0 ≤ e) (hN : N.degreeOf 0 ≤ d + e)
    (heq : ∀ i, rowPolynomial N (a i) = C i * rowPolynomial E (a i))
    (hcard : d + 2 * e < Fintype.card I) (y : F)
    (herr : (BerlekampWelch.errors a (fun i => (C i).eval y) (R y)).card ≤ e) :
    columnPolynomial N y = R y * columnPolynomial E y := by
  apply BerlekampWelch.numerator_eq_mul_of_error_bound a (fun i => (C i).eval y) ha
    (R y) (columnPolynomial E y) (columnPolynomial N y) (hR y)
    ((natDegree_axisRestrict_le ![0, y] 0 E).trans hE)
    ((natDegree_axisRestrict_le ![0, y] 0 N).trans hN) ?_ herr hcard
  intro i
  have h := congrArg (fun p : Polynomial F => p.eval y) (heq i)
  simpa only [eval_rowPolynomial, eval_columnPolynomial, Polynomial.eval_mul] using h

omit [Fintype I] in
/-- Cancelling a nonzero locator evaluation forces agreement at a selected column. -/
theorem agreement_of_certificate_row (a : I → F) (C : I → Polynomial F)
    (R : F → Polynomial F) (E N : MvPolynomial (Fin 2) F)
    (heq : ∀ i, rowPolynomial N (a i) = C i * rowPolynomial E (a i))
    (y : F) (hrow : columnPolynomial N y = R y * columnPolynomial E y)
    (i : I) (hne : (rowPolynomial E (a i)).eval y ≠ 0) :
    (R y).eval (a i) = (C i).eval y := by
  have hr := congrArg (fun p : Polynomial F => p.eval (a i)) hrow
  have hc := congrArg (fun p : Polynomial F => p.eval y) (heq i)
  simp only [eval_columnPolynomial, eval_rowPolynomial, Polynomial.eval_mul] at hr hc hne
  exact mul_right_cancel₀ hne (hr.symm.trans hc)

variable [Fintype F] [DecidableEq F]

/-- A certificate produces many rows agreeing at every selected nonzero column.

This is the clean-rectangle counting step. Construction of `E,N` and selection of
the nonzero column set `J` are explicit remaining inputs, not assumed soundness. -/
theorem fraction_clean_rows_ge (a : I → F) (ha : Function.Injective a)
    (C : I → Polynomial F) (R : F → Polynomial F)
    (E N : MvPolynomial (Fin 2) F) (J : Finset I)
    (hR : ∀ y, (R y).natDegree ≤ d)
    (hE : E.degreeOf 0 ≤ e) (hN : N.degreeOf 0 ≤ d + e)
    (hEy : E.degreeOf 1 ≤ D)
    (heq : ∀ i, rowPolynomial N (a i) = C i * rowPolynomial E (a i))
    (hne : ∀ i ∈ J, rowPolynomial E (a i) ≠ 0)
    (hcard : d + 2 * e < Fintype.card I) {ε : ℚ}
    (hcol : ∀ i, relativeDistance (fun y => (R y).eval (a i)) (C i).eval ≤ ε) :
    1 - (Fintype.card I * ε) / (e + 1) - J.card * D / Fintype.card F ≤
      fraction (fun y => ∀ i ∈ J, (R y).eval (a i) = (C i).eval y) := by
  classical
  have hgood := fraction_good_ge
    (fun y => e < rowErrors a C R y)
    (fun y => ∃ i ∈ J, (rowPolynomial E (a i)).eval y = 0)
    (fun y => ∀ i ∈ J, (R y).eval (a i) = (C i).eval y) ?_
  · have hbad := fraction_many_rowErrors_le a C R e hcol
    have hzero := fraction_exists_column_zero_le J (fun i => rowPolynomial E (a i)) D
      hne (fun i _ => (natDegree_axisRestrict_le ![a i, 0] 1 E).trans hEy)
    linarith
  · intro y hy hn i hi
    have herr : (BerlekampWelch.errors a (fun i => (C i).eval y) (R y)).card ≤ e := by
      simpa only [BerlekampWelch.errors, rowErrors, hammingDist] using le_of_not_gt hy
    have hrow := certificate_row_eq a ha C R E N hR hE hN heq hcard y herr
    exact agreement_of_certificate_row a C R E N heq y hrow i
      (fun hz => hn ⟨i, hi, hz⟩)

end Certificate

section NonzeroColumns

variable {F I : Type*} [Field F] [Fintype F] [Fintype I] {d e : ℕ}

open scoped Classical in
/-- A nonzero bivariate polynomial has at most its `X` degree many identically
zero selected `Y`-columns. The field-size premise prevents zero polynomial functions. -/
theorem card_zero_columns_le (a : I → F) (ha : Function.Injective a)
    (E : MvPolynomial (Fin 2) F) (hne : E ≠ 0) (hx : E.degreeOf 0 ≤ e)
    (hsize : ∀ j, E.degreeOf j < Fintype.card F) :
    (univ.filter (fun i => rowPolynomial E (a i) = 0)).card ≤ e := by
  classical
  by_contra hlarge
  let Z := univ.filter (fun i => rowPolynomial E (a i) = 0)
  have hZ : e < Z.card := by simpa only [Z] using Nat.lt_of_not_ge hlarge
  have hrows (y : F) : columnPolynomial E y = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (f := fun i : {i // i ∈ Z} => a i) (ha.comp Subtype.val_injective)
    · intro i
      have hi : rowPolynomial E (a i) = 0 := (mem_filter.mp i.property).2
      rw [eval_columnPolynomial, ← eval_rowPolynomial, hi, Polynomial.eval_zero]
    · have hdeg := (natDegree_axisRestrict_le ![0, y] 0 E).trans hx
      exact hdeg.trans_lt (by simpa only [Fintype.card_coe] using hZ)
  apply hne
  apply GridInterpolation.eq_zero_of_eval_grid_eq_zero (univ : Finset F) E
    (by simpa only [card_univ] using hsize)
  intro z
  have hv : ![(z 0 : F), (z 1 : F)] = fun i => (z i : F) := by
    funext i
    fin_cases i <;> rfl
  rw [← hv, ← eval_columnPolynomial, hrows, Polynomial.eval_zero]

/-- Enough nodes supply `d+1` distinct columns on which the locator is a nonzero
formal polynomial. The selection is constructed from the preceding root bound. -/
theorem exists_nonzero_columns (a : I → F) (ha : Function.Injective a)
    (E : MvPolynomial (Fin 2) F) (hne : E ≠ 0) (hx : E.degreeOf 0 ≤ e)
    (hsize : ∀ j, E.degreeOf j < Fintype.card F)
    (hcard : d + e < Fintype.card I) :
    ∃ b : Fin (d + 1) ↪ I, ∀ i, rowPolynomial E (a (b i)) ≠ 0 := by
  classical
  let J := univ.filter (fun i => rowPolynomial E (a i) ≠ 0)
  have hzero := card_zero_columns_le a ha E hne hx hsize
  have hpartition := card_filter_add_card_filter_not (s := (univ : Finset I))
    (fun i => rowPolynomial E (a i) = 0)
  have hpartition' : (univ.filter (fun i => rowPolynomial E (a i) = 0)).card +
      J.card = Fintype.card I := by
    simpa only [J, ne_eq, card_univ] using hpartition
  have hJ : d + 1 ≤ J.card := by
    omega
  have hc : Fintype.card (Fin (d + 1)) ≤ Fintype.card {i // i ∈ J} := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hJ
  obtain ⟨b⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨b.trans (Function.Embedding.subtype (fun i => i ∈ J)), ?_⟩
  intro i
  exact (mem_filter.mp (b i).property).2

end NonzeroColumns

end PCP.Algebraic.BivariateCleanRectangle
