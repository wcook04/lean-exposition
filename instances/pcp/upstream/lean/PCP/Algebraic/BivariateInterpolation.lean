/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.GridInterpolation
import PCP.Algebraic.PointLineCrossing

/-!
# Bivariate interpolation and extrapolation from a clean rectangle

The algebraic step in Arora--Safra, §5.2, Corollary 5.2.3: interpolate `d+1`
polynomials in `Y` at distinct `X` coordinates. The resulting formal polynomial
has degree at most `d` in each variable. Rows agreeing at all selected coordinates
are recovered everywhere; sufficiently many such rows determine other columns.

We keep `PointLineCrossing`'s coordinate convention: `rowPolynomial P x` fixes
`X=x` and varies `Y`, whereas `columnPolynomial P y` fixes `Y=y` and varies `X`.
Thus the source's selected columns are called `rowPolynomial` in this API.
This module proves the interpolation/extrapolation implication, not existence
of the clean rectangle or the full proximity conclusion of the source corollary.
-/

namespace PCP.Algebraic.BivariateInterpolation

open Finset PointLineCrossing

variable {F : Type*} [Field F] {d : ℕ}

section Restriction

variable {σ : Type*} [DecidableEq σ]

/-- Restricting in the embedded variable preserves the formal univariate polynomial. -/
theorem axisRestrict_toMvPolynomial_self (u : σ → F) (i : σ) (p : Polynomial F) :
    axisRestrict u i (p.toMvPolynomial i) = p := by
  have h : (axisRestrict u i).comp (Polynomial.toMvPolynomial i).toRingHom =
      RingHom.id (Polynomial F) := by
    ext z <;> simp [axisRestrict]
  exact DFunLike.congr_fun h p

/-- A different coordinate restriction evaluates the embedded polynomial to a constant. -/
theorem axisRestrict_toMvPolynomial_of_ne (u : σ → F) (i j : σ) (hij : i ≠ j)
    (p : Polynomial F) :
    axisRestrict u j (p.toMvPolynomial i) = Polynomial.C (p.eval (u i)) := by
  have h : (axisRestrict u j).comp (Polynomial.toMvPolynomial i).toRingHom =
      Polynomial.C.comp (Polynomial.evalRingHom (u i)) := by
    ext z <;> simp [axisRestrict, hij]
  exact DFunLike.congr_fun h p

end Restriction

/-- Lagrange interpolation of the selected `Y`-polynomials in the `X` coordinate. -/
noncomputable def interpolate (a : Fin (d + 1) → F)
    (C : Fin (d + 1) → Polynomial F) : MvPolynomial (Fin 2) F :=
  ∑ i, (Lagrange.basis univ a i).toMvPolynomial 0 * (C i).toMvPolynomial 1

/-- The interpolating polynomial has the advertised explicit evaluation formula. -/
theorem eval_interpolate (a : Fin (d + 1) → F) (C : Fin (d + 1) → Polynomial F)
    (x y : F) :
    MvPolynomial.eval ![x, y] (interpolate a C) =
      ∑ i, (Lagrange.basis univ a i).eval x * (C i).eval y := by
  simp [interpolate, MvPolynomial.eval_toMvPolynomial]

/-- The polynomial has degree at most `d` separately in each coordinate. -/
theorem degreeOf_interpolate_le {a : Fin (d + 1) → F} (ha : Function.Injective a)
    (C : Fin (d + 1) → Polynomial F) (hC : ∀ i, (C i).natDegree ≤ d) (j : Fin 2) :
    (interpolate a C).degreeOf j ≤ d := by
  classical
  rw [interpolate]
  apply (MvPolynomial.degreeOf_sum_le j _ _).trans
  apply Finset.sup_le
  intro i _
  apply (MvPolynomial.degreeOf_mul_le j _ _).trans
  have hL := GridInterpolation.degreeOf_toMvPolynomial_le (Lagrange.basis univ a i) 0 j
  have hCi := GridInterpolation.degreeOf_toMvPolynomial_le (C i) 1 j
  have hdeg : (Lagrange.basis univ a i).natDegree = d := by
    simpa using Lagrange.natDegree_basis ha.injOn (mem_univ i)
  fin_cases j <;> simp only [Fin.isValue, hdeg] at hL hCi ⊢
  · simpa using (add_le_add hL hCi)
  · exact (add_le_add hL hCi).trans (by simpa using hC i)

/-- Restricting to any fixed `X` gives a formal linear combination of the input polynomials. -/
theorem rowPolynomial_interpolate (a : Fin (d + 1) → F)
    (C : Fin (d + 1) → Polynomial F) (x : F) :
    rowPolynomial (interpolate a C) x =
      ∑ i, Polynomial.C ((Lagrange.basis univ a i).eval x) * C i := by
  simp only [rowPolynomial, interpolate, map_sum, map_mul]
  apply sum_congr rfl
  intro i _
  rw [axisRestrict_toMvPolynomial_of_ne _ 0 1 (by decide),
    axisRestrict_toMvPolynomial_self]
  rfl

/-- Every selected `Y`-polynomial is recovered formally, without a field-size premise. -/
theorem rowPolynomial_interpolate_node {a : Fin (d + 1) → F}
    (ha : Function.Injective a) (C : Fin (d + 1) → Polynomial F) (i : Fin (d + 1)) :
    rowPolynomial (interpolate a C) (a i) = C i := by
  classical
  rw [rowPolynomial_interpolate]
  rw [sum_eq_single i]
  · rw [Lagrange.eval_basis_self ha.injOn (mem_univ i), Polynomial.C_1, one_mul]
  · intro j _ hji
    rw [Lagrange.eval_basis_of_ne hji (mem_univ i), Polynomial.C_0, zero_mul]
  · exact fun hi => (hi (mem_univ i)).elim

/-- Evaluation recovery at every selected `X` coordinate. -/
theorem eval_interpolate_node {a : Fin (d + 1) → F} (ha : Function.Injective a)
    (C : Fin (d + 1) → Polynomial F) (i : Fin (d + 1)) (y : F) :
    MvPolynomial.eval ![a i, y] (interpolate a C) = (C i).eval y := by
  rw [← eval_rowPolynomial, rowPolynomial_interpolate_node ha]

/-- A degree-bounded `X`-polynomial agreeing at all selected coordinates is the entire
fixed-`Y` restriction, as a formal polynomial. -/
theorem columnPolynomial_interpolate_eq {a : Fin (d + 1) → F}
    (ha : Function.Injective a) (C : Fin (d + 1) → Polynomial F)
    (hC : ∀ i, (C i).natDegree ≤ d) (y : F) (R : Polynomial F)
    (hR : R.natDegree ≤ d) (hagree : ∀ i, R.eval (a i) = (C i).eval y) :
    columnPolynomial (interpolate a C) y = R := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ ha
  · intro i
    rw [eval_columnPolynomial, eval_interpolate_node ha]
    exact (hagree i).symm
  · have hslice : (columnPolynomial (interpolate a C) y).natDegree ≤ d :=
      (natDegree_axisRestrict_le _ _ _).trans (degreeOf_interpolate_le ha C hC 0)
    simpa only [Fintype.card_fin] using
      (max_le hslice hR).trans_lt (Nat.lt_succ_self d)

/-- A compatible degree-bounded `X`-row is recovered at every coordinate. -/
theorem eval_interpolate_eq_of_node_agreement {a : Fin (d + 1) → F}
    (ha : Function.Injective a) (C : Fin (d + 1) → Polynomial F)
    (hC : ∀ i, (C i).natDegree ≤ d) (y : F) (R : Polynomial F)
    (hR : R.natDegree ≤ d) (hagree : ∀ i, R.eval (a i) = (C i).eval y) (x : F) :
    MvPolynomial.eval ![x, y] (interpolate a C) = R.eval x := by
  rw [← eval_columnPolynomial, columnPolynomial_interpolate_eq ha C hC y R hR hagree]

/-- More than `d` agreeing clean rows determine any additional degree-bounded `Y`-column.
The clean rows need not occupy the whole field, and agreement with the new column
is required only on the explicitly counted subset. -/
theorem rowPolynomial_interpolate_eq_of_many_agreements [DecidableEq F]
    {a : Fin (d + 1) → F} (ha : Function.Injective a)
    (C : Fin (d + 1) → Polynomial F) (hC : ∀ i, (C i).natDegree ≤ d)
    (B : Finset F) (R : F → Polynomial F) (hR : ∀ y ∈ B, (R y).natDegree ≤ d)
    (hclean : ∀ y ∈ B, ∀ i, (R y).eval (a i) = (C i).eval y)
    (x : F) (Cx : Polynomial F) (hCx : Cx.natDegree ≤ d)
    (hagree : d < (B.filter (fun y => Cx.eval y = (R y).eval x)).card) :
    rowPolynomial (interpolate a C) x = Cx := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _
    (B.filter (fun y => Cx.eval y = (R y).eval x))
  · intro y hy
    obtain ⟨hyB, hy⟩ := mem_filter.mp hy
    rw [eval_rowPolynomial,
      eval_interpolate_eq_of_node_agreement ha C hC y (R y) (hR y hyB) (hclean y hyB)]
    exact hy.symm
  · have hslice : (rowPolynomial (interpolate a C) x).natDegree ≤ d :=
      (natDegree_axisRestrict_le _ _ _).trans (degreeOf_interpolate_le ha C hC 1)
    exact (max_le hslice hCx).trans_lt hagree

/-- A clean rectangle constructs one actual bivariate polynomial and extends any
additional column with more than `d` agreements among the clean rows. -/
theorem exists_extension_of_clean_rectangle [DecidableEq F]
    {a : Fin (d + 1) → F} (ha : Function.Injective a)
    (C : Fin (d + 1) → Polynomial F) (hC : ∀ i, (C i).natDegree ≤ d)
    (B : Finset F) (R : F → Polynomial F) (hR : ∀ y ∈ B, (R y).natDegree ≤ d)
    (hclean : ∀ y ∈ B, ∀ i, (R y).eval (a i) = (C i).eval y) :
    ∃ P : MvPolynomial (Fin 2) F,
      (∀ j, P.degreeOf j ≤ d) ∧
      (∀ i, rowPolynomial P (a i) = C i) ∧
      (∀ y ∈ B, columnPolynomial P y = R y) ∧
      ∀ (x : F) (Cx : Polynomial F), Cx.natDegree ≤ d →
        d < (B.filter (fun y => Cx.eval y = (R y).eval x)).card →
        rowPolynomial P x = Cx := by
  refine ⟨interpolate a C, degreeOf_interpolate_le ha C hC,
    rowPolynomial_interpolate_node ha C, ?_, ?_⟩
  · intro y hy
    exact columnPolynomial_interpolate_eq ha C hC y (R y) (hR y hy) (hclean y hy)
  · intro x Cx hCx hagree
    exact rowPolynomial_interpolate_eq_of_many_agreements ha C hC B R hR hclean x Cx hCx hagree

end PCP.Algebraic.BivariateInterpolation
