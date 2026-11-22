/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BivariateInterpolation
import PCP.Algebraic.PointedLineSampling

/-!
# Coarse bivariate agreement from an explicit clean rectangle

Selected columns are polynomials in `Y` at distinct `X` coordinates; every row
is a degree-bounded polynomial in `X`. If each selected column has error at most
`ε`, a clean set of more than `ε|F|+d` rows on `d+1` seed columns determines one
bivariate polynomial. Every supplied column is its restriction. A differing row
then contributes at least `n-d` errors among the `n` columns, yielding proximity
`nε/(n-d)` on the whole grid.

This is the bivariate counting conclusion of Arora--Safra Corollary 5.2.3.
The clean rectangle remains an explicit hypothesis; its existence is a separate
step. All distances and cardinal estimates use normalized rational arithmetic.
-/

namespace PCP.Algebraic.BivariateAgreementFromRectangle

open Finset PointLineCrossing BivariateInterpolation AffineLineSampling
open scoped BigOperators

section Counting

variable {I A : Type*} [Fintype I] [Nonempty I] [DecidableEq A]

/-- Removing all global errors from a large set leaves more than `d` agreements. -/
theorem card_agreements_gt (f g : I → A) (B : Finset I) {d : ℕ} {ε : ℚ}
    (hclose : relativeDistance f g ≤ ε)
    (hB : ε * Fintype.card I + d < B.card) :
    d < (B.filter (fun i => f i = g i)).card := by
  classical
  have hq : (0 : ℚ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have herr : (hammingDist f g : ℚ) ≤ ε * Fintype.card I :=
    (div_le_iff₀ hq).mp hclose
  have hpart := card_filter_add_card_filter_not (s := B) (fun i => f i = g i)
  have hbad : (B.filter (fun i => f i ≠ g i)).card ≤ hammingDist f g := by
    apply card_le_card
    exact filter_subset_filter _ (subset_univ B)
  have hbad' : ((B.filter (fun i => f i ≠ g i)).card : ℚ) ≤ ε * Fintype.card I :=
    (Nat.cast_le.mpr hbad).trans herr
  have hpart' : ((B.filter (fun i => f i = g i)).card : ℚ) +
      (B.filter (fun i => f i ≠ g i)).card = B.card := by exact_mod_cast hpart
  have hgood : (d : ℚ) < (B.filter (fun i => f i = g i)).card := by linarith
  exact_mod_cast hgood

end Counting

section PolynomialCounts

variable {F I : Type*} [Field F] [DecidableEq F] [Fintype I] {d : ℕ}

/-- Distinct degree-bounded polynomials disagree on at least `n-d` distinct sample points. -/
theorem sample_disagreementCount_ge (a : I → F) (ha : Function.Injective a)
    (p q : Polynomial F) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (hne : p ≠ q) :
    (Fintype.card I : ℚ) - d ≤
      (hammingDist (fun i => p.eval (a i)) (fun i => q.eval (a i)) : ℚ) := by
  classical
  let S := univ.filter (fun i => p.eval (a i) = q.eval (a i))
  have hgood : S.card ≤ d := by
    by_contra hbad
    have hlarge : d < S.card := Nat.lt_of_not_ge hbad
    apply hne
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q
      (f := fun i : S => a i) (ha.comp Subtype.val_injective)
    · intro i
      exact (mem_filter.mp i.property).2
    · simpa only [Fintype.card_coe] using (max_le hp hq).trans_lt hlarge
  have hpart := card_filter_add_card_filter_not (s := univ)
    (fun i => p.eval (a i) = q.eval (a i))
  have hpart' : (S.card : ℚ) +
      (hammingDist (fun i => p.eval (a i)) (fun i => q.eval (a i)) : ℚ) = Fintype.card I := by
    exact_mod_cast hpart
  have hgood' : (S.card : ℚ) ≤ d := by exact_mod_cast hgood
  linarith

end PolynomialCounts

section FiniteField

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] {d : ℕ}

/-- Column-wise proximity controls the mean number of errors across the supplied columns. -/
theorem expect_rowErrors_le (a : I → F) (C : I → Polynomial F) (R : F → Polynomial F)
    {ε : ℚ} (hcol : ∀ i, relativeDistance (fun y => (R y).eval (a i)) (C i).eval ≤ ε) :
    (𝔼 y, (hammingDist (fun i => (R y).eval (a i)) (fun i => (C i).eval y) : ℚ)) ≤
      Fintype.card I * ε := by
  classical
  have hrow (y : F) :
      (hammingDist (fun i => (R y).eval (a i)) (fun i => (C i).eval y) : ℚ) =
        ∑ i, if (R y).eval (a i) ≠ (C i).eval y then (1 : ℚ) else 0 := by
    simp only [hammingDist, natCast_card_filter]
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

omit [Fintype I] in
/-- Every supplied column is forced by the clean seed rectangle and its error bound. -/
theorem all_columns_recovered (a : I → F) (ha : Function.Injective a)
    (C : I → Polynomial F) (hC : ∀ i, (C i).natDegree ≤ d)
    (R : F → Polynomial F) (hR : ∀ y, (R y).natDegree ≤ d)
    (b : Fin (d + 1) → I) (hb : Function.Injective b) (B : Finset F)
    (hclean : ∀ y ∈ B, ∀ j, (R y).eval (a (b j)) = (C (b j)).eval y)
    {ε : ℚ} (hcol : ∀ i, relativeDistance (fun y => (R y).eval (a i)) (C i).eval ≤ ε)
    (hB : ε * Fintype.card F + d < B.card) (i : I) :
    rowPolynomial (interpolate (a ∘ b) (C ∘ b)) (a i) = C i := by
  apply rowPolynomial_interpolate_eq_of_many_agreements (ha.comp hb) (C ∘ b)
    (fun j => hC (b j)) B R (fun y _ => hR y) hclean (a i) (C i) (hC i)
  apply card_agreements_gt (C i).eval (fun y => (R y).eval (a i)) B
    (by simpa only [relativeDistance_comm] using hcol i) hB

/-- Once all columns are recovered, the fraction of differing formal rows is at most
the average number of column errors divided by the polynomial separation `n-d`. -/
theorem rowDistance_le (a : I → F) (ha : Function.Injective a)
    (C : I → Polynomial F) (R : F → Polynomial F) (hR : ∀ y, (R y).natDegree ≤ d)
    (P : MvPolynomial (Fin 2) F) (hP : ∀ j, P.degreeOf j ≤ d)
    (hcolumns : ∀ i, rowPolynomial P (a i) = C i) (hn : d < Fintype.card I)
    {ε : ℚ} (hcol : ∀ i, relativeDistance (fun y => (R y).eval (a i)) (C i).eval ≤ ε) :
    relativeDistance R (columnPolynomial P) ≤
      Fintype.card I * ε / ((Fintype.card I : ℚ) - d) := by
  classical
  have hslice (y : F) : (columnPolynomial P y).natDegree ≤ d :=
    (natDegree_axisRestrict_le _ _ _).trans (hP 0)
  have heval (y : F) (i : I) :
      (columnPolynomial P y).eval (a i) = (C i).eval y := by
    rw [eval_columnPolynomial, ← eval_rowPolynomial, hcolumns]
  have hpoint (y : F) :
      ((Fintype.card I : ℚ) - d) * (if R y ≠ columnPolynomial P y then (1 : ℚ) else 0) ≤
        (hammingDist (fun i => (R y).eval (a i)) (fun i => (C i).eval y) : ℚ) := by
    split_ifs with hy
    · simp only [mul_one]
      simpa only [heval] using
        sample_disagreementCount_ge a ha (R y) (columnPolynomial P y) (hR y) (hslice y) hy
    · simp only [mul_zero]
      exact Nat.cast_nonneg _
  have hmean := expect_le_expect (s := univ) (fun y _ => hpoint y)
  rw [← mul_expect, ← fraction_eq_expect, fraction_ne_eq_relativeDistance] at hmean
  have hgap : (0 : ℚ) < Fintype.card I - d := sub_pos.mpr (by exact_mod_cast hn)
  apply (le_div_iff₀ hgap).mpr
  simpa only [mul_comm] using hmean.trans (expect_rowErrors_le a C R hcol)

/-- A formal row mismatch bounds every evaluation-grid disagreement in that row. -/
theorem gridDistance_le_rowDistance (R : F → Polynomial F)
    (P : MvPolynomial (Fin 2) F) :
    relativeDistance (fun z : F × F => (R z.2).eval z.1)
      (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ relativeDistance R (columnPolynomial P) := by
  have he := relativeDistance_comp_equiv (Equiv.prodComm F F)
    (fun z : F × F => (R z.2).eval z.1)
    (fun z => MvPolynomial.eval ![z.1, z.2] P)
  rw [← he]
  apply (relativeDistance_le_of_disagreement
    (fun z : F × F => (R z.1).eval z.2)
    (fun z => MvPolynomial.eval ![z.2, z.1] P)
    (fun z => R z.1) (fun z => columnPolynomial P z.1) ?_).trans
  · exact (relativeDistance_comp_fst R (columnPolynomial P)).le
  · intro z hz heq
    apply hz
    rw [heq, eval_columnPolynomial]

/-- A clean seed rectangle and close columns give an actual nearby bivariate polynomial. -/
theorem exists_nearby_polynomial (a : I → F) (ha : Function.Injective a)
    (C : I → Polynomial F) (hC : ∀ i, (C i).natDegree ≤ d)
    (R : F → Polynomial F) (hR : ∀ y, (R y).natDegree ≤ d)
    (b : Fin (d + 1) → I) (hb : Function.Injective b) (B : Finset F)
    (hclean : ∀ y ∈ B, ∀ j, (R y).eval (a (b j)) = (C (b j)).eval y)
    {ε : ℚ} (hcol : ∀ i, relativeDistance (fun y => (R y).eval (a i)) (C i).eval ≤ ε)
    (hB : ε * Fintype.card F + d < B.card) :
    ∃ P : MvPolynomial (Fin 2) F, (∀ j, P.degreeOf j ≤ d) ∧
      (∀ i, rowPolynomial P (a i) = C i) ∧
      relativeDistance R (columnPolynomial P) ≤
        Fintype.card I * ε / ((Fintype.card I : ℚ) - d) ∧
      relativeDistance (fun z : F × F => (R z.2).eval z.1)
        (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤
        Fintype.card I * ε / ((Fintype.card I : ℚ) - d) := by
  let P := interpolate (a ∘ b) (C ∘ b)
  have hP : ∀ j, P.degreeOf j ≤ d := degreeOf_interpolate_le (ha.comp hb) (C ∘ b)
    (fun j => hC (b j))
  have hcolumns : ∀ i, rowPolynomial P (a i) = C i :=
    all_columns_recovered a ha C hC R hR b hb B hclean hcol hB
  have hn : d < Fintype.card I := by
    have h := Fintype.card_le_of_injective b hb
    simp only [Fintype.card_fin] at h
    exact (Nat.lt_succ_self d).trans_le h
  have hrows := rowDistance_le a ha C R hR P hP hcolumns hn hcol
  exact ⟨P, hP, hcolumns, hrows, (gridDistance_le_rowDistance R P).trans hrows⟩

/-- The source's numerical `1/9` proximity conclusion, conditional only on the
explicit clean rectangle and the `1/10` column errors at `10d` distinct nodes. -/
theorem exists_nearby_polynomial_one_ninth (a : I → F) (ha : Function.Injective a)
    (C : I → Polynomial F) (hC : ∀ i, (C i).natDegree ≤ d)
    (R : F → Polynomial F) (hR : ∀ y, (R y).natDegree ≤ d)
    (b : Fin (d + 1) → I) (hb : Function.Injective b) (B : Finset F)
    (hclean : ∀ y ∈ B, ∀ j, (R y).eval (a (b j)) = (C (b j)).eval y)
    (hcol : ∀ i, relativeDistance (fun y => (R y).eval (a i)) (C i).eval ≤ (1 : ℚ) / 10)
    (hB : (1 : ℚ) / 10 * Fintype.card F + d < B.card)
    (hn : Fintype.card I = 10 * d) :
    ∃ P : MvPolynomial (Fin 2) F, (∀ j, P.degreeOf j ≤ d) ∧
      (∀ i, rowPolynomial P (a i) = C i) ∧
      relativeDistance R (columnPolynomial P) ≤ (1 : ℚ) / 9 ∧
      relativeDistance (fun z : F × F => (R z.2).eval z.1)
        (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ (1 : ℚ) / 9 := by
  have hd : 0 < d := by
    have h := Fintype.card_le_of_injective b hb
    simp only [Fintype.card_fin, hn] at h
    omega
  have hratio : Fintype.card I * ((1 : ℚ) / 10) /
      ((Fintype.card I : ℚ) - d) = 1 / 9 := by
    rw [hn, Nat.cast_mul, Nat.cast_ofNat]
    have hd' : (0 : ℚ) < d := by exact_mod_cast hd
    have hden : (10 : ℚ) * d - d ≠ 0 := by linarith
    field_simp
    ring
  simpa only [hratio] using exists_nearby_polynomial a ha C hC R hR b hb B hclean hcol hB

end FiniteField

end PCP.Algebraic.BivariateAgreementFromRectangle
