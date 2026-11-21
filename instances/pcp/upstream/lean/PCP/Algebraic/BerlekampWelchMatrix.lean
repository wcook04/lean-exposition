/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BerlekampWelch
import PCP.Algebraic.PolynomialMatrixKernel
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# Polynomial Berlekamp–Welch matrices

The unknowns are the coefficients of a numerator of degree at most `d+e` and a
locator of degree at most `e`. The matrix equations at node `a i` express
`N(a i) - columns i * E(a i) = 0`, with the received column values polynomial in
the transverse variable. This is the specialization input to Arora–Safra
Lemma 5.2.7.

Each good specialization has a genuine nonzero kernel vector, constructed from
the explicit Berlekamp–Welch error locator. No solution or kernel certificate is
assumed in that construction. No algorithmic running-time bound is claimed.
-/

namespace PCP.Algebraic.BerlekampWelchMatrix

open Finset Polynomial Matrix

variable {F I : Type*} [Field F] {d e D : ℕ}

/-- Numerator coefficients followed by locator coefficients. -/
abbrev Unknowns (d e : ℕ) := Fin (d + e + 1) ⊕ Fin (e + 1)

@[simp] theorem card_unknowns (d e : ℕ) :
    Fintype.card (Unknowns d e) = d + 2 * e + 2 := by
  simp only [Unknowns, Fintype.card_sum, Fintype.card_fin]
  omega

/-- The polynomial matrix of received-word equations, with rows indexed by evaluation nodes. -/
noncomputable def matrix (d e : ℕ) (a : I → F) (columns : I → Polynomial F) :
    Matrix I (Unknowns d e) (Polynomial F) :=
  fun i j => Sum.elim (fun k : Fin (d + e + 1) => C (a i ^ (k : ℕ)))
    (fun k : Fin (e + 1) => -columns i * C (a i ^ (k : ℕ))) j

@[simp] theorem matrix_inl (a : I → F) (columns : I → Polynomial F)
    (i : I) (j : Fin (d + e + 1)) :
    matrix d e a columns i (Sum.inl j) = C (a i ^ (j : ℕ)) := rfl

@[simp] theorem matrix_inr (a : I → F) (columns : I → Polynomial F)
    (i : I) (j : Fin (e + 1)) :
    matrix d e a columns i (Sum.inr j) = -columns i * C (a i ^ (j : ℕ)) := rfl

/-- The transverse degree of each entry is at most the column-word degree. -/
theorem natDegree_matrix_le (a : I → F) (columns : I → Polynomial F)
    (hcolumns : ∀ i, (columns i).natDegree ≤ D) (i : I) (j : Unknowns d e) :
    (matrix d e a columns i j).natDegree ≤ D := by
  cases j with
  | inl j => simp only [matrix_inl, natDegree_C]; exact Nat.zero_le _
  | inr j =>
    apply natDegree_mul_le.trans
    simpa only [natDegree_neg, natDegree_C, add_zero] using hcolumns i

/-- Encode a pair of bounded-degree polynomials into the matrix's unknown coordinates. -/
def coefficientVector (d e : ℕ) (E N : Polynomial F) : Unknowns d e → F :=
  Sum.elim (fun j => N.coeff j) (fun j => E.coeff j)

/-- A nonzero locator yields a nonzero coefficient vector, even if the numerator vanishes. -/
theorem coefficientVector_ne_zero (E N : Polynomial F) (hE : E.natDegree ≤ e)
    (hE0 : E ≠ 0) : coefficientVector d e E N ≠ 0 := by
  intro hv
  have h := congrFun hv (Sum.inr ⟨E.natDegree, Nat.lt_succ_of_le hE⟩)
  change E.coeff E.natDegree = 0 at h
  exact hE0 (leadingCoeff_eq_zero.mp h)

private theorem sum_pow_mul_coeff (p : Polynomial F) {k : ℕ} (hp : p.natDegree ≤ k)
    (x : F) : (∑ j : Fin (k + 1), x ^ (j : ℕ) * p.coeff j) = p.eval x := by
  rw [show (∑ j : Fin (k + 1), x ^ (j : ℕ) * p.coeff j) =
      ∑ j ∈ range (k + 1), x ^ j * p.coeff j from
    Fin.sum_univ_eq_sum_range (fun j => x ^ j * p.coeff j) (k + 1)]
  simpa only [mul_comm] using (eval_eq_sum_range' (Nat.lt_succ_of_le hp) x).symm

/-- The evaluated matrix product is exactly the residual of each received-word equation. -/
theorem evaluated_matrix_mulVec (a : I → F) (columns : I → Polynomial F)
    (y : F) (E N : Polynomial F) (hE : E.natDegree ≤ e) (hN : N.natDegree ≤ d + e)
    (i : I) :
    ((matrix d e a columns).map (fun p => p.eval y) *ᵥ coefficientVector d e E N) i =
      N.eval (a i) - (columns i).eval y * E.eval (a i) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply,
    matrix_inl, matrix_inr, coefficientVector, Sum.elim_inl, Sum.elim_inr,
    eval_C, eval_mul, eval_neg, mul_assoc]
  rw [← mul_sum, sum_pow_mul_coeff N hN, sum_pow_mul_coeff E hE]
  ring

variable [Fintype I]

/-- Every genuine close row supplies a nonzero kernel vector of the specialized matrix. -/
theorem exists_specialized_kernel (a : I → F) (columns : I → Polynomial F)
    (y : F) (s : Polynomial F) (hs : s.natDegree ≤ d)
    (herr : (BerlekampWelch.errors a (fun i => (columns i).eval y) s).card ≤ e) :
    ∃ v : Unknowns d e → F, v ≠ 0 ∧
      (matrix d e a columns).map (fun p => p.eval y) *ᵥ v = 0 := by
  obtain ⟨E, N, hE0, hE, hN, heq⟩ :=
    BerlekampWelch.exists_solution a (fun i => (columns i).eval y) s hs herr
  refine ⟨coefficientVector d e E N, coefficientVector_ne_zero E N hE hE0, ?_⟩
  funext i
  rw [evaluated_matrix_mulVec a columns y E N hE hN i, heq i, sub_self]
  rfl

/-- Enough good specializations force every maximal minor to vanish formally.
The local kernel witnesses are constructed from the supplied genuine close rows. -/
theorem maximal_minor_eq_zero_of_good_specializations
    (a : I → F) (columns : I → Polynomial F)
    (hcolumns : ∀ i, (columns i).natDegree ≤ D)
    (S : Finset F) (hcard : (d + 2 * e + 2) * D < S.card)
    (hgood : ∀ y ∈ S, ∃ s : Polynomial F, s.natDegree ≤ d ∧
      (BerlekampWelch.errors a (fun i => (columns i).eval y) s).card ≤ e)
    (rows : Unknowns d e → I) :
    ((matrix d e a columns).submatrix rows id).det = 0 := by
  apply PolynomialMatrixKernel.maximal_minor_eq_zero_of_many_singular_specializations
    (matrix d e a columns) (natDegree_matrix_le a columns hcolumns) S
    (by simpa only [card_unknowns] using hcard) _ rows
  intro y hy
  obtain ⟨s, hs, herr⟩ := hgood y hy
  exact exists_specialized_kernel a columns y s hs herr

end PCP.Algebraic.BerlekampWelchMatrix
