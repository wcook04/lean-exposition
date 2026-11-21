/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BerlekampWelchMatrix
import PCP.Algebraic.PointLineCrossing

/-!
# Constructing bivariate Berlekamp–Welch certificates

Polynomial kernel coordinates are assembled into actual bivariate polynomials.
The first variable indexes numerator and locator powers, while the second
variable carries their polynomial coefficients. All coefficient and degree
claims are formal polynomial identities, independent of the field's cardinality.

The final theorem constructs the bounded kernel from sufficiently many genuine
close rows, then assembles a numerator and a nonzero locator. It assumes neither
a polynomial kernel nor a bivariate certificate. This supplies the bivariate
case of the polynomial linear-system lifting in Arora–Safra Lemma 5.2.7.
-/

namespace PCP.Algebraic.BerlekampWelchCertificate

open Finset Polynomial Matrix PointLineCrossing BerlekampWelchMatrix

section Series

variable {R : Type*} [CommRing R] {k : ℕ}

/-- A polynomial with a specified finite list of coefficients. -/
noncomputable def series (v : Fin (k + 1) → R) : Polynomial R :=
  ∑ j : Fin (k + 1), monomial (j : ℕ) (v j)

@[simp] theorem coeff_series (v : Fin (k + 1) → R) (j : Fin (k + 1)) :
    (series v).coeff j = v j := by
  classical
  simp [series, coeff_monomial, Fin.val_inj]

theorem series_injective : Function.Injective (series (R := R) (k := k)) := by
  intro v w h
  funext j
  simpa only [coeff_series] using congrArg (fun p : Polynomial R => p.coeff j) h

theorem natDegree_series_le (v : Fin (k + 1) → R) : (series v).natDegree ≤ k := by
  unfold series
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ j.isLt)

theorem eval_series (v : Fin (k + 1) → R) (x : R) :
    (series v).eval x = ∑ j, v j * x ^ (j : ℕ) := by
  simp only [series, eval_finsetSum, eval_monomial]

end Series

variable {F I : Type*} [Field F] {k d e D K : ℕ}

/-- Include a univariate polynomial as a polynomial in the second variable alone. -/
noncomputable def inY : Polynomial F →+* MvPolynomial (Fin 2) F :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X 1)

@[simp] theorem inY_C (a : F) : inY (C a) = MvPolynomial.C a := by simp [inY]

@[simp] theorem inY_X : inY (X : Polynomial F) = MvPolynomial.X 1 := by simp [inY]

/-- Assemble polynomial coefficients into a bivariate polynomial. -/
noncomputable def assemble (v : Fin (k + 1) → Polynomial F) : MvPolynomial (Fin 2) F :=
  ∑ j, inY (v j) * MvPolynomial.X 0 ^ (j : ℕ)

/-- A symbolic change of representation to polynomials in `X` with coefficients in `F[Y]`. -/
noncomputable def symbolicX : MvPolynomial (Fin 2) F →+* Polynomial (Polynomial F) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    ![Polynomial.X, Polynomial.C Polynomial.X]

@[simp] theorem symbolicX_inY (p : Polynomial F) : symbolicX (inY p) = C p := by
  have h : symbolicX.comp inY = (Polynomial.C : Polynomial F →+* Polynomial (Polynomial F)) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [symbolicX]
    · simp [symbolicX]
  exact congrArg (fun f : Polynomial F →+* Polynomial (Polynomial F) => f p) h

@[simp] theorem symbolicX_assemble (v : Fin (k + 1) → Polynomial F) :
    symbolicX (assemble v) = series v := by
  simp only [assemble, map_sum, map_mul, map_pow, symbolicX_inY]
  simp only [symbolicX, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
    C_mul_X_pow_eq_monomial, series]

theorem assemble_injective : Function.Injective (assemble (F := F) (k := k)) := by
  intro v w h
  apply series_injective
  simpa only [symbolicX_assemble] using congrArg symbolicX h

@[simp] theorem rowPolynomial_inY (p : Polynomial F) (x : F) :
    rowPolynomial (inY p) x = p := by
  have h : (axisRestrict ![x, 0] 1).comp inY = RingHom.id (Polynomial F) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [axisRestrict]
    · simp [axisRestrict]
  exact congrArg (fun f : Polynomial F →+* Polynomial F => f p) h

/-- Restriction at a fixed first coordinate evaluates the outer coefficient series. -/
theorem rowPolynomial_assemble (v : Fin (k + 1) → Polynomial F) (x : F) :
    rowPolynomial (assemble v) x = ∑ j, v j * C (x ^ (j : ℕ)) := by
  change axisRestrict ![x, 0] 1 (∑ j, inY (v j) * MvPolynomial.X 0 ^ (j : ℕ)) = _
  simp only [map_sum, map_mul, map_pow]
  have hy (j : Fin (k + 1)) : axisRestrict ![x, 0] 1 (inY (v j)) = v j :=
    rowPolynomial_inY (v j) x
  simp only [hy]
  simp only [axisRestrict, MvPolynomial.eval₂Hom_X', show (0 : Fin 2) ≠ 1 by decide,
    ↓reduceIte, Matrix.cons_val_zero, ← map_pow]

theorem degreeOf_inY_zero (p : Polynomial F) : (inY p).degreeOf 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, inY_C, inY_X]
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro j _
  apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
  simp only [MvPolynomial.degreeOf_C,
    MvPolynomial.degreeOf_X_pow_of_ne _ (by decide : (0 : Fin 2) ≠ 1), zero_add, le_refl]

theorem degreeOf_inY_one_le (p : Polynomial F) : (inY p).degreeOf 1 ≤ p.natDegree := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, inY_C, inY_X]
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro j hj
  apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
  simpa only [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self_pow, zero_add] using
    Nat.le_of_lt_succ (mem_range.mp hj)

theorem degreeOf_assemble_zero_le (v : Fin (k + 1) → Polynomial F) :
    (assemble v).degreeOf 0 ≤ k := by
  unfold assemble
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro j _
  apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
  simpa only [degreeOf_inY_zero, MvPolynomial.degreeOf_X_self_pow, zero_add] using
    Nat.le_of_lt_succ j.isLt

theorem degreeOf_assemble_one_le (v : Fin (k + 1) → Polynomial F)
    (hv : ∀ j, (v j).natDegree ≤ K) : (assemble v).degreeOf 1 ≤ K := by
  unfold assemble
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro j _
  apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
  simpa only [MvPolynomial.degreeOf_X_pow_of_ne _ (by decide : (1 : Fin 2) ≠ 0), add_zero]
    using (degreeOf_inY_one_le (v j)).trans (hv j)

@[simp] theorem assemble_zero : assemble (0 : Fin (k + 1) → Polynomial F) = 0 := by
  simp [assemble]

theorem rowPolynomial_assemble_eq_eval_series (v : Fin (k + 1) → Polynomial F) (x : F) :
    rowPolynomial (assemble v) x = (series v).eval (C x) := by
  rw [rowPolynomial_assemble, eval_series]
  simp only [map_pow]

/-- The formal matrix product is the bivariate certificate equation at the selected column. -/
theorem matrix_mulVec_assemble (a : I → F) (columns : I → Polynomial F)
    (v : Unknowns d e → Polynomial F) (i : I) :
    (matrix d e a columns *ᵥ v) i =
      rowPolynomial (assemble (fun j => v (Sum.inl j))) (a i) -
        columns i * rowPolynomial (assemble (fun j => v (Sum.inr j))) (a i) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, matrix_inl, matrix_inr]
  have hN : (∑ j : Fin (d + e + 1), C (a i ^ (j : ℕ)) * v (Sum.inl j)) =
      rowPolynomial (assemble (fun j => v (Sum.inl j))) (a i) := by
    rw [rowPolynomial_assemble]
    apply sum_congr rfl
    intro j _
    ring
  have hE : (∑ j : Fin (e + 1), (-columns i * C (a i ^ (j : ℕ))) * v (Sum.inr j)) =
      -columns i * rowPolynomial (assemble (fun j => v (Sum.inr j))) (a i) := by
    rw [rowPolynomial_assemble, mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [hN, hE]
  ring

theorem equations_of_kernel (a : I → F) (columns : I → Polynomial F)
    (v : Unknowns d e → Polynomial F) (hv : matrix d e a columns *ᵥ v = 0) (i : I) :
    rowPolynomial (assemble (fun j => v (Sum.inl j))) (a i) =
      columns i * rowPolynomial (assemble (fun j => v (Sum.inr j))) (a i) := by
  have h := congrFun hv i
  rw [matrix_mulVec_assemble] at h
  exact sub_eq_zero.mp h

variable [Fintype I]

/-- A nonzero polynomial kernel yields a nonzero assembled locator when distinct
nodes outnumber the numerator's degree. The argument is over the integral domain `F[Y]`. -/
theorem assembled_locator_ne_zero (a : I → F) (ha : Function.Injective a)
    (columns : I → Polynomial F) (v : Unknowns d e → Polynomial F)
    (hv0 : v ≠ 0) (hv : matrix d e a columns *ᵥ v = 0)
    (hnodes : d + e < Fintype.card I) : assemble (fun j => v (Sum.inr j)) ≠ 0 := by
  intro hE
  have hEcoef : (fun j : Fin (e + 1) => v (Sum.inr j)) = 0 :=
    assemble_injective (hE.trans assemble_zero.symm)
  have hN : series (fun j : Fin (d + e + 1) => v (Sum.inl j)) = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (Polynomial.C_injective.comp ha)
    · intro i
      change (series (fun j : Fin (d + e + 1) => v (Sum.inl j))).eval (C (a i)) = 0
      rw [← rowPolynomial_assemble_eq_eval_series, equations_of_kernel a columns v hv i, hE]
      simp only [rowPolynomial, map_zero, mul_zero]
    · exact (natDegree_series_le _).trans_lt hnodes
  apply hv0
  funext j
  cases j with
  | inl j =>
    have h := congrArg (fun p : Polynomial (Polynomial F) => p.coeff j) hN
    simpa only [coeff_series, coeff_zero, Pi.zero_apply] using h
  | inr j => exact congrFun hEcoef j

/-- Assemble an actual bounded polynomial kernel into a nonzero bivariate certificate. -/
theorem certificate_of_kernel (a : I → F) (ha : Function.Injective a)
    (columns : I → Polynomial F) (v : Unknowns d e → Polynomial F)
    (hv0 : v ≠ 0) (hv : matrix d e a columns *ᵥ v = 0)
    (hdegree : ∀ j, (v j).natDegree ≤ K) (hnodes : d + e < Fintype.card I) :
    ∃ E N : MvPolynomial (Fin 2) F, E ≠ 0 ∧ E.degreeOf 0 ≤ e ∧
      N.degreeOf 0 ≤ d + e ∧ E.degreeOf 1 ≤ K ∧ N.degreeOf 1 ≤ K ∧
      ∀ i, rowPolynomial N (a i) = columns i * rowPolynomial E (a i) := by
  refine ⟨assemble (fun j => v (Sum.inr j)), assemble (fun j => v (Sum.inl j)),
    assembled_locator_ne_zero a ha columns v hv0 hv hnodes,
    degreeOf_assemble_zero_le _, degreeOf_assemble_zero_le _,
    degreeOf_assemble_one_le _ (fun j => hdegree (Sum.inr j)),
    degreeOf_assemble_one_le _ (fun j => hdegree (Sum.inl j)), ?_⟩
  exact equations_of_kernel a columns v hv

/-- Many genuine close rows construct a bivariate numerator and nonzero locator
with explicit bounds in both variables; no polynomial certificate is assumed. -/
theorem exists_certificate_of_good_specializations
    (a : I → F) (ha : Function.Injective a) (columns : I → Polynomial F)
    (hcolumns : ∀ i, (columns i).natDegree ≤ D)
    (S : Finset F) (hcard : (d + 2 * e + 2) * D < S.card)
    (hgood : ∀ y ∈ S, ∃ s : Polynomial F, s.natDegree ≤ d ∧
      (BerlekampWelch.errors a (fun i => (columns i).eval y) s).card ≤ e)
    (hnodes : d + e < Fintype.card I) :
    ∃ E N : MvPolynomial (Fin 2) F, E ≠ 0 ∧ E.degreeOf 0 ≤ e ∧
      N.degreeOf 0 ≤ d + e ∧ E.degreeOf 1 ≤ (d + 2 * e + 1) * D ∧
      N.degreeOf 1 ≤ (d + 2 * e + 1) * D ∧
      ∀ i, rowPolynomial N (a i) = columns i * rowPolynomial E (a i) := by
  obtain ⟨v, hv0, hv, hdegree⟩ :=
    PolynomialMatrixKernel.exists_bounded_kernel_of_maximal_minors_fintype
      (matrix d e a columns) (natDegree_matrix_le a columns hcolumns)
      (maximal_minor_eq_zero_of_good_specializations a columns hcolumns S hcard hgood)
  apply certificate_of_kernel a ha columns v hv0 hv _ hnodes
  intro j
  have hc : Fintype.card (Unknowns d e) - 1 = d + 2 * e + 1 := by
    rw [card_unknowns]
    omega
  simpa only [hc] using hdegree j

end PCP.Algebraic.BerlekampWelchCertificate
