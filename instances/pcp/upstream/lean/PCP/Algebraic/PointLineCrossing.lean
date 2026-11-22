/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.FiniteDistance
import PCP.Algebraic.PointLineDecoder
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Crossing consistency for low-degree rows and columns

The deterministic ingredient of ALMSS, *Proof Verification and the Hardness of
Approximation Problems*, Appendix A, Corollary 70. A global comparison between
separated row codewords bounds disagreement on every transverse slice. This
will identify optimal row and column approximants with the corresponding
restrictions of a nearby bivariate polynomial.

The existence of that nearby bivariate polynomial is the separate
Arora--Safra agreement theorem quoted as ALMSS Theorem 69. It is not proved or
assumed globally here.

The underlying Arora--Safra result is Lemma 5.2.1 of *Probabilistic Checking of
Proofs: A New Characterization of NP*, JACM 45(1), printed p. 107; its note
identifies dimension two as the ALMSS application. That lemma's formulation is
coarse proximity of a function with polynomial rows from many close columns,
rather than the literal `4ε` form of ALMSS Theorem 69.
-/

namespace PCP.Algebraic.PointLineCrossing

open Finset

section SeparatedRows

variable {I J A : Type*} [Fintype I] [Fintype J] [DecidableEq A]

/-- Expanding separated row words multiplies their relative distance by at least
their separation. The separation hypothesis is local to the two rows compared. -/
theorem row_mismatch_mul_le (R S : I → J → A) (δ : ℚ)
    (hsep : ∀ i, R i ≠ S i → δ ≤ relativeDistance (R i) (S i)) :
    δ * relativeDistance R S ≤
      relativeDistance (fun p : I × J => R p.1 p.2) (fun p => S p.1 p.2) := by
  classical
  have hs : (∑ i, if R i ≠ S i then δ else 0) ≤
      ∑ i, relativeDistance (R i) (S i) := by
    apply sum_le_sum
    intro i _
    split_ifs with hi
    · exact hsep i hi
    · exact relativeDistance_nonneg _ _
  have he : (∑ i, if R i ≠ S i then δ else 0) =
      (hammingDist R S : ℚ) * δ := by
    simp only [hammingDist, ← sum_filter, sum_const, nsmul_eq_mul]
  rw [he] at hs
  rw [relativeDistance_prod]
  change δ * ((hammingDist R S : ℚ) / Fintype.card I) ≤ _
  calc
    _ = ((hammingDist R S : ℚ) * δ) / Fintype.card I := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Fintype.card I))

/-- A row code of distance at least `1 - τ` loses at most `τ` when an entire
row is charged for any disagreement. No positivity of `1 - τ` is needed. -/
theorem row_mismatch_le (R S : I → J → A) {τ : ℚ} (hτ : 0 ≤ τ)
    (hsep : ∀ i, R i ≠ S i → 1 - τ ≤ relativeDistance (R i) (S i)) :
    relativeDistance R S ≤
      relativeDistance (fun p : I × J => R p.1 p.2) (fun p => S p.1 p.2) + τ := by
  have h := row_mismatch_mul_le R S (1 - τ) hsep
  have hle := relativeDistance_le_one R S
  nlinarith

/-- Every fixed column is controlled by the same global error plus the row
code's distance deficit. -/
theorem transverse_distance_le (R S : I → J → A) {τ : ℚ} (hτ : 0 ≤ τ)
    (hsep : ∀ i, R i ≠ S i → 1 - τ ≤ relativeDistance (R i) (S i)) (j : J) :
    relativeDistance (fun i => R i j) (fun i => S i j) ≤
      relativeDistance (fun p : I × J => R p.1 p.2) (fun p => S p.1 p.2) + τ := by
  classical
  apply (relativeDistance_le_of_disagreement
    (fun i => R i j) (fun i => S i j) R S ?_).trans
    (row_mismatch_le R S hτ hsep)
  intro i hi heq
  exact hi (congrFun heq j)

end SeparatedRows

section PolynomialRows

open PointLineTest

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] {d : ℕ}

/-- For polynomial rows, the deficit in the preceding estimate is `d / |F|`.
The chosen column is arbitrary, rather than a fresh random column. -/
theorem polynomial_transverse_distance_le (R S : I → Polynomial F)
    (hR : ∀ i, (R i).natDegree ≤ d) (hS : ∀ i, (S i).natDegree ≤ d) (y : F) :
    relativeDistance (fun i => (R i).eval y) (fun i => (S i).eval y) ≤
      relativeDistance (fun p : I × F => (R p.1).eval p.2)
        (fun p => (S p.1).eval p.2) + (d : ℚ) / Fintype.card F := by
  apply transverse_distance_le (fun i => (R i).eval) (fun i => (S i).eval)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ?_ y
  intro i hi
  exact univariate_distance_ge _ _ (hR i) (hS i) (fun heq => hi (by rw [heq]))

/-- A nearest polynomial on a transverse slice is forced to equal a comparison
polynomial once row errors put the comparison inside the unique decoding radius.
Only the one necessary comparison in the minimization property is assumed. -/
theorem eq_of_transverse_close (R S : F → Polynomial F)
    (hR : ∀ i, (R i).natDegree ≤ d) (hS : ∀ i, (S i).natDegree ≤ d)
    (w : F → F) (p q : Polynomial F) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (y : F) (hScol : ∀ x, (S x).eval y = p.eval x)
    {η ε : ℚ}
    (hglobal : relativeDistance (fun z : F × F => (R z.1).eval z.2)
      (fun z => (S z.1).eval z.2) ≤ η)
    (hlocal : relativeDistance w (fun x => (R x).eval y) ≤ ε)
    (hmin : relativeDistance w q.eval ≤ relativeDistance w p.eval)
    (hradius : 2 * (ε + η + (d : ℚ) / Fintype.card F) <
      1 - (d : ℚ) / Fintype.card F) : q = p := by
  have ht := polynomial_transverse_distance_le R S hR hS y
  have hs : (fun x => (S x).eval y) = p.eval := funext hScol
  rw [hs] at ht
  have hw : relativeDistance w p.eval ≤ ε + η + (d : ℚ) / Fintype.card F := by
    have htriangle := relativeDistance_triangle w (fun x => (R x).eval y) p.eval
    linarith
  exact eq_of_univariate_close q p hq hp hradius (hmin.trans hw) hw

/-- The deterministic crossing argument. `GR` and `GC` are the row and column
polynomials of one comparison grid; their compatibility is explicit. Both actual
approximants at the crossing are nearest to the received slices. -/
theorem crossing_eq_of_nearby_rows (f : F × F → F)
    (R C GR GC : F → Polynomial F)
    (hR : ∀ x, (R x).natDegree ≤ d) (hC : ∀ y, (C y).natDegree ≤ d)
    (hGR : ∀ x, (GR x).natDegree ≤ d) (hGC : ∀ y, (GC y).natDegree ≤ d)
    (hG : ∀ x y, (GR x).eval y = (GC y).eval x)
    (x₀ y₀ : F) {η ε : ℚ}
    (hrows : relativeDistance (fun z : F × F => (R z.1).eval z.2)
      (fun z => (GR z.1).eval z.2) ≤ η)
    (hcols : relativeDistance (fun z : F × F => (C z.1).eval z.2)
      (fun z => (GC z.1).eval z.2) ≤ η)
    (hlrow : relativeDistance (fun y => f (x₀, y)) (fun y => (C y).eval x₀) ≤ ε)
    (hlcol : relativeDistance (fun x => f (x, y₀)) (fun x => (R x).eval y₀) ≤ ε)
    (hminR : relativeDistance (fun y => f (x₀, y)) (R x₀).eval ≤
      relativeDistance (fun y => f (x₀, y)) (GR x₀).eval)
    (hminC : relativeDistance (fun x => f (x, y₀)) (C y₀).eval ≤
      relativeDistance (fun x => f (x, y₀)) (GC y₀).eval)
    (hradius : 2 * (ε + η + (d : ℚ) / Fintype.card F) <
      1 - (d : ℚ) / Fintype.card F) : (R x₀).eval y₀ = (C y₀).eval x₀ := by
  have hc : C y₀ = GC y₀ := eq_of_transverse_close R GR hR hGR
    (fun x => f (x, y₀)) (GC y₀) (C y₀) (hGC y₀) (hC y₀) y₀
    (fun x => hG x y₀) hrows hlcol hminC hradius
  have hr : R x₀ = GR x₀ := eq_of_transverse_close C GC hC hGC
    (fun y => f (x₀, y)) (GR x₀) (R x₀) (hGR x₀) (hR x₀) x₀
    (fun y => (hG x₀ y).symm) hcols hlrow hminR hradius
  rw [hr, hc]
  exact hG x₀ y₀

end PolynomialRows

section AxisRestriction

variable {F σ : Type*} [Field F] [DecidableEq σ]

/-- Keep every coordinate fixed except one, whose value is the univariate
parameter. This is a coordinate slice, so individual degree controls it. -/
noncomputable def axisRestrict (u : σ → F) (i : σ) :
    MvPolynomial σ F →+* Polynomial F :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun j => if j = i then Polynomial.X else Polynomial.C (u j))

/-- Taking a coordinate slice does not increase its individual degree. -/
theorem natDegree_axisRestrict_le (u : σ → F) (i : σ) (P : MvPolynomial σ F) :
    (axisRestrict u i P).natDegree ≤ P.degreeOf i := by
  classical
  have hq (j : σ) :
      (if j = i then Polynomial.X else Polynomial.C (u j)).natDegree ≤
        if j = i then 1 else 0 := by
    split_ifs <;> simp
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  simp only [axisRestrict, MvPolynomial.eval₂Hom_monomial, Finsupp.prod]
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  calc
    _ ≤ ∑ j ∈ s.support,
        ((if j = i then Polynomial.X else Polynomial.C (u j)) ^ s j).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ j ∈ s.support, s j * (if j = i then 1 else 0) := by
      apply sum_le_sum
      intro j _
      exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hq j))
    _ ≤ s i := by
      simp only [mul_ite, mul_one, mul_zero, sum_ite_eq']
      split_ifs <;> omega
    _ ≤ P.degreeOf i := MvPolynomial.monomial_le_degreeOf i hs

/-- Evaluation of a coordinate slice updates precisely the selected coordinate. -/
@[simp] theorem eval_axisRestrict (u : σ → F) (i : σ) (P : MvPolynomial σ F) (t : F) :
    (axisRestrict u i P).eval t = MvPolynomial.eval (Function.update u i t) P := by
  have h : (Polynomial.evalRingHom t).comp (axisRestrict u i) =
      MvPolynomial.eval (Function.update u i t) := by
    ext j
    · simp [axisRestrict]
    · by_cases hj : j = i <;> simp [axisRestrict, hj]
  exact congrArg (fun f : MvPolynomial σ F →+* F => f P) h

end AxisRestriction

section BivariatePolynomial

variable {F : Type*} [Field F] {d : ℕ}

/-- The row through `x`, viewed as a polynomial in the second coordinate. -/
noncomputable def rowPolynomial (P : MvPolynomial (Fin 2) F) (x : F) : Polynomial F :=
  axisRestrict ![x, 0] 1 P

/-- The column through `y`, viewed as a polynomial in the first coordinate. -/
noncomputable def columnPolynomial (P : MvPolynomial (Fin 2) F) (y : F) : Polynomial F :=
  axisRestrict ![0, y] 0 P

@[simp] theorem eval_rowPolynomial (P : MvPolynomial (Fin 2) F) (x y : F) :
    (rowPolynomial P x).eval y = MvPolynomial.eval ![x, y] P := by
  rw [rowPolynomial, eval_axisRestrict]
  apply congrArg (fun u => MvPolynomial.eval u P)
  ext i
  fin_cases i <;> simp

@[simp] theorem eval_columnPolynomial (P : MvPolynomial (Fin 2) F) (x y : F) :
    (columnPolynomial P y).eval x = MvPolynomial.eval ![x, y] P := by
  rw [columnPolynomial, eval_axisRestrict]
  apply congrArg (fun u => MvPolynomial.eval u P)
  ext i
  fin_cases i <;> simp

variable [Fintype F] [DecidableEq F]

/-- The Corollary 70 argument with an explicit nearby bivariate polynomial.

The comparison polynomial has degree at most `d` in each variable. Its existence
is an explicit hypothesis; `BivariateCrossingSoundness` supplies it using the
separately proved bivariate agreement theorem.
The two line approximants at the crossing need only satisfy their usual minimum
distance property. Global errors `ε`, polynomial error `ρ`, and slice error `ε'`
are kept separate so this lemma can be reused with other agreement bounds. -/
theorem crossing_eq_of_nearby_polynomial (f : F × F → F)
    (R C : F → Polynomial F)
    (hR : ∀ x, (R x).natDegree ≤ d) (hC : ∀ y, (C y).natDegree ≤ d)
    (P : MvPolynomial (Fin 2) F) (hP : ∀ i, P.degreeOf i ≤ d)
    (x₀ y₀ : F) {ε ρ ε' : ℚ}
    (hrows : relativeDistance f (fun z => (R z.1).eval z.2) ≤ ε)
    (hcols : relativeDistance f (fun z => (C z.2).eval z.1) ≤ ε)
    (hnear : relativeDistance f (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ ρ)
    (hlrow : relativeDistance (fun y => f (x₀, y)) (fun y => (C y).eval x₀) ≤ ε')
    (hlcol : relativeDistance (fun x => f (x, y₀)) (fun x => (R x).eval y₀) ≤ ε')
    (hminR : ∀ p : Polynomial F, p.natDegree ≤ d →
      relativeDistance (fun y => f (x₀, y)) (R x₀).eval ≤
        relativeDistance (fun y => f (x₀, y)) p.eval)
    (hminC : ∀ p : Polynomial F, p.natDegree ≤ d →
      relativeDistance (fun x => f (x, y₀)) (C y₀).eval ≤
        relativeDistance (fun x => f (x, y₀)) p.eval)
    (hradius : 2 * (ε' + ε + ρ + (d : ℚ) / Fintype.card F) <
      1 - (d : ℚ) / Fintype.card F) : (R x₀).eval y₀ = (C y₀).eval x₀ := by
  have hGR (x : F) : (rowPolynomial P x).natDegree ≤ d :=
    (natDegree_axisRestrict_le ![x, 0] 1 P).trans (hP 1)
  have hGC (y : F) : (columnPolynomial P y).natDegree ≤ d :=
    (natDegree_axisRestrict_le ![0, y] 0 P).trans (hP 0)
  have hrows' : relativeDistance (fun z : F × F => (R z.1).eval z.2)
      (fun z => (rowPolynomial P z.1).eval z.2) ≤ ε + ρ := by
    simp only [eval_rowPolynomial]
    have h := relativeDistance_triangle (fun z : F × F => (R z.1).eval z.2) f
      (fun z => MvPolynomial.eval ![z.1, z.2] P)
    rw [relativeDistance_comm (fun z : F × F => (R z.1).eval z.2) f] at h
    linarith
  have hcols' : relativeDistance (fun z : F × F => (C z.1).eval z.2)
      (fun z => (columnPolynomial P z.1).eval z.2) ≤ ε + ρ := by
    have h := relativeDistance_triangle (fun z : F × F => (C z.2).eval z.1) f
      (fun z => MvPolynomial.eval ![z.1, z.2] P)
    rw [relativeDistance_comm (fun z : F × F => (C z.2).eval z.1) f] at h
    have ht : relativeDistance (fun z : F × F => (C z.2).eval z.1)
        (fun z => (columnPolynomial P z.2).eval z.1) ≤ ε + ρ := by
      simp only [eval_columnPolynomial]
      linarith
    have he := relativeDistance_comp_equiv (Equiv.prodComm F F)
      (fun z : F × F => (C z.2).eval z.1)
      (fun z => (columnPolynomial P z.2).eval z.1)
    rw [← he] at ht
    exact ht
  apply crossing_eq_of_nearby_rows f R C (rowPolynomial P) (columnPolynomial P)
    hR hC hGR hGC (fun x y => by simp) x₀ y₀ hrows' hcols' hlrow hlcol
    (hminR _ (hGR x₀)) (hminC _ (hGC y₀))
  linarith

/-- The numerical form of ALMSS Corollary 70 for chosen nearest rows and columns.
The nearby bivariate polynomial, whose existence is the substantive preceding
agreement theorem, remains an explicit argument. -/
theorem crossing_bestApproximation_eq_of_nearby_polynomial (f : F × F → F)
    (P : MvPolynomial (Fin 2) F) (hP : ∀ i, P.degreeOf i ≤ d)
    (x₀ y₀ : F) {ε ε' : ℚ}
    (hrows : relativeDistance f (fun z =>
      (PointLineTest.bestApproximation d (fun y => f (z.1, y))).val.eval z.2) ≤ ε)
    (hcols : relativeDistance f (fun z =>
      (PointLineTest.bestApproximation d (fun x => f (x, z.2))).val.eval z.1) ≤ ε)
    (hnear : relativeDistance f (fun z => MvPolynomial.eval ![z.1, z.2] P) ≤ 4 * ε)
    (hlrow : relativeDistance (fun y => f (x₀, y)) (fun y =>
      (PointLineTest.bestApproximation d (fun x => f (x, y))).val.eval x₀) ≤ ε')
    (hlcol : relativeDistance (fun x => f (x, y₀)) (fun x =>
      (PointLineTest.bestApproximation d (fun y => f (x, y))).val.eval y₀) ≤ ε')
    (hsmall : 5 * ε + ε' + 2 * ((d : ℚ) / Fintype.card F) < 1 / 2) :
    (PointLineTest.bestApproximation d (fun y => f (x₀, y))).val.eval y₀ =
      (PointLineTest.bestApproximation d (fun x => f (x, y₀))).val.eval x₀ := by
  apply crossing_eq_of_nearby_polynomial f
    (fun x => (PointLineTest.bestApproximation d (fun y => f (x, y))).val)
    (fun y => (PointLineTest.bestApproximation d (fun x => f (x, y))).val)
    (fun x => (PointLineTest.bestApproximation d (fun y => f (x, y))).property)
    (fun y => (PointLineTest.bestApproximation d (fun x => f (x, y))).property)
    P hP x₀ y₀ hrows hcols hnear hlrow hlcol
    (PointLineTest.bestApproximation_min d _) (PointLineTest.bestApproximation_min d _)
  have hratio : (0 : ℚ) ≤ (d : ℚ) / Fintype.card F :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  linarith

end BivariatePolynomial

end PCP.Algebraic.PointLineCrossing
