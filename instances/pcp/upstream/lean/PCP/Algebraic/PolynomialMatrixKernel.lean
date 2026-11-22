/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Nat.Find

/-!
# Lifting singular polynomial matrices from specializations

The determinant step in Arora--Safra, *Probabilistic Checking of Proofs: A New
Characterization of NP*, Lemma 5.2.7. A square matrix with polynomial entries of
degree at most `d` has determinant of degree at most its size times `d`. If its
specializations have nonzero kernel at more distinct field points than that,
the determinant is the zero polynomial. The same argument applies to every
maximal square minor of a rectangular matrix. A largest nonzero minor then
provides a cofactor kernel vector with coordinate degrees at most
`(number of columns - 1) * d`. The maximal minor and the kernel vector are
constructed in the proof, rather than assumed.

The field need not be finite: the set of witnessing specializations is a finite
set supplied explicitly. No polynomial kernel or determinant vanishing is
assumed in the specialization theorem.
-/

namespace PCP.Algebraic.PolynomialMatrixKernel

open Finset Matrix Polynomial

section DeterminantDegree

variable {R N : Type*} [CommRing R] [Fintype N] [DecidableEq N] {d : ℕ}

/-- Entrywise degree bounds give the usual determinant degree bound. -/
theorem natDegree_det_le (A : Matrix N N (Polynomial R))
    (hA : ∀ i j, (A i j).natDegree ≤ d) :
    A.det.natDegree ≤ Fintype.card N * d := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro p _
  calc
    (Equiv.Perm.sign p • ∏ i, A (p i) i).natDegree ≤ (∏ i, A (p i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp
      · rw [hp, one_smul]
      · rw [hp, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i, (A (p i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : N, d := sum_le_sum (fun i _ => hA (p i) i)
    _ = Fintype.card N * d := by simp

/-- Evaluation commutes with the determinant, including size zero. -/
theorem eval_det (A : Matrix N N (Polynomial R)) (x : R) :
    A.det.eval x = (A.map (fun p => p.eval x)).det :=
  (Polynomial.evalRingHom x).map_det A

end DeterminantDegree

section Specialization

variable {F I N : Type*} [Field F] [Fintype N] [DecidableEq N] {d : ℕ}

/-- More singular specializations than the determinant's degree force formal singularity. -/
theorem det_eq_zero_of_many_singular_specializations
    (A : Matrix N N (Polynomial F)) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (S : Finset F) (hcard : Fintype.card N * d < S.card)
    (hker : ∀ x ∈ S, ∃ v : N → F, v ≠ 0 ∧ (A.map (fun p => p.eval x)) *ᵥ v = 0) :
    A.det = 0 := by
  classical
  by_contra hdet
  have hroots : S.card ≤ A.det.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    apply (Polynomial.mem_roots hdet).mpr
    change A.det.eval x = 0
    rw [eval_det]
    exact Matrix.exists_mulVec_eq_zero_iff.mp (hker x hx)
  exact (not_lt_of_ge (hroots.trans (natDegree_det_le A hA))) hcard

/-- A common nonzero kernel at each specialization forces every maximal minor
to vanish as a formal polynomial. The row selection need not be injective. -/
theorem maximal_minor_eq_zero_of_many_singular_specializations
    (A : Matrix I N (Polynomial F)) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (S : Finset F) (hcard : Fintype.card N * d < S.card)
    (hker : ∀ x ∈ S, ∃ v : N → F, v ≠ 0 ∧ (A.map (fun p => p.eval x)) *ᵥ v = 0)
    (rows : N → I) : (A.submatrix rows id).det = 0 := by
  apply det_eq_zero_of_many_singular_specializations (A.submatrix rows id)
    (fun i j => hA (rows i) j) S hcard
  intro x hx
  obtain ⟨v, hv, hAv⟩ := hker x hx
  refine ⟨v, hv, ?_⟩
  funext i
  exact congrFun hAv (rows i)

omit [DecidableEq N] in
/-- For square matrices, formal singularity already produces an actual nonzero
polynomial kernel vector. This statement does not bound its degree; see
`exists_bounded_polynomial_kernel_of_many_singular_specializations`. -/
theorem exists_polynomial_kernel_of_many_singular_specializations
    (A : Matrix N N (Polynomial F)) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (S : Finset F) (hcard : Fintype.card N * d < S.card)
    (hker : ∀ x ∈ S, ∃ v : N → F, v ≠ 0 ∧ (A.map (fun p => p.eval x)) *ᵥ v = 0) :
    ∃ v : N → Polynomial F, v ≠ 0 ∧ A *ᵥ v = 0 := by
  classical
  exact Matrix.exists_mulVec_eq_zero_iff.mpr
    (det_eq_zero_of_many_singular_specializations A hA S hcard hker)

end Specialization

section CofactorKernel

variable {F I N : Type*} [Field F] [Fintype N] {d k : ℕ}

/-- Cofactors of `k` selected rows and `k+1` columns give a bounded polynomial
kernel when appending any row makes the corresponding determinant vanish.
The first cofactor is explicitly nonzero, and its column occurs nowhere else. -/
theorem exists_bounded_kernel_of_minor
    (A : Matrix I N (Polynomial F)) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (rows : Fin k → I) (cols : Fin (k + 1) → N)
    (hfirst : ∀ j : Fin k, cols j.succ ≠ cols 0)
    (hbase : (A.submatrix rows (fun j => cols j.succ)).det ≠ 0)
    (hext : ∀ i, (A.submatrix (Fin.cons i rows) cols).det = 0) :
    ∃ v : N → Polynomial F, v ≠ 0 ∧ A *ᵥ v = 0 ∧
      ∀ j, (v j).natDegree ≤ k * d := by
  classical
  let w : Fin (k + 1) → Polynomial F := fun j =>
    (-1) ^ (j : ℕ) * (A.submatrix rows (fun l => cols (j.succAbove l))).det
  let v : N → Polynomial F := ∑ j, Pi.single (cols j) (w j)
  have hwdegree (j : Fin (k + 1)) : (w j).natDegree ≤ k * d := by
    dsimp only [w]
    apply Polynomial.natDegree_mul_le.trans
    have hb := natDegree_det_le (A.submatrix rows (fun l => cols (j.succAbove l)))
      (fun i l => hA (rows i) (cols (j.succAbove l)))
    simpa using hb
  have hvfirst : v (cols 0) = w 0 := by
    have hz (j : Fin k) : (Pi.single (cols j.succ) (w j.succ) : N → Polynomial F) (cols 0) = 0 := by
      exact Pi.single_eq_of_ne (hfirst j).symm _
    change (∑ j, Pi.single (cols j) (w j) : N → Polynomial F) (cols 0) = w 0
    rw [Finset.sum_apply, Fin.sum_univ_succ]
    simp only [Pi.single_eq_same, hz, sum_const_zero, add_zero]
  have hwfirst : w 0 ≠ 0 := by
    simpa [w] using hbase
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv
    exact hwfirst (hvfirst.symm.trans (congrFun hv (cols 0)))
  · dsimp only [v]
    rw [Matrix.mulVec_sum]
    funext i
    simp only [Finset.sum_apply, Matrix.mulVec_single, Pi.zero_apply, Pi.smul_apply,
      Matrix.col_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    have h := Matrix.det_succ_row_zero (A.submatrix (Fin.cons i rows) cols)
    rw [hext i] at h
    convert h.symm using 1
    apply sum_congr rfl
    intro j _
    simp only [w, Matrix.submatrix_apply, Fin.cons_zero,
      Matrix.submatrix_submatrix, Function.comp_def, Fin.cons_succ]
    ring
  · intro j
    dsimp only [v]
    rw [Finset.sum_apply]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro l _
    by_cases hl : cols l = j
    · subst j
      simpa only [Pi.single_eq_same] using hwdegree l
    · rw [Pi.single_eq_of_ne (Ne.symm hl), Polynomial.natDegree_zero]
      exact Nat.zero_le _

end CofactorKernel

section MaximalMinor

variable {F I : Type*} [Field F] {d n : ℕ}

/-- Vanishing maximal minors of a rectangular polynomial matrix produce an
actual nonzero polynomial kernel, with the Cramer/cofactor degree bound.
The proof chooses a largest nonzero minor, rather than assuming one. -/
theorem exists_bounded_kernel_of_maximal_minors
    (A : Matrix I (Fin n) (Polynomial F)) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (hfull : ∀ rows : Fin n → I, (A.submatrix rows id).det = 0) :
    ∃ v : Fin n → Polynomial F, v ≠ 0 ∧ A *ᵥ v = 0 ∧
      ∀ j, (v j).natDegree ≤ (n - 1) * d := by
  classical
  let P : ℕ → Prop := fun k => ∃ rows : Fin k → I, ∃ cols : Fin k → Fin n,
    (A.submatrix rows cols).det ≠ 0
  have hP0 : P 0 := by
    refine ⟨Fin.elim0, Fin.elim0, ?_⟩
    simp
  have hPn : ¬ P n := by
    rintro ⟨rows, cols, hminor⟩
    have hinj : Function.Injective cols := by
      intro i j hij
      by_contra hne
      exact hminor (Matrix.det_zero_of_column_eq hne (fun k => by simp [hij]))
    let e : Fin n ≃ Fin n :=
      Equiv.ofBijective cols ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩
    have he := Matrix.det_permute' e (A.submatrix rows id)
    have hz : (A.submatrix rows cols).det = 0 := by
      rw [hfull rows, mul_zero] at he
      exact he
    exact hminor hz
  let k := Nat.findGreatest P n
  have hkP : P k := Nat.findGreatest_spec (Nat.zero_le n) hP0
  have hkle : k ≤ n := Nat.findGreatest_le n
  have hklt : k < n := by
    by_contra hnot
    have heq : k = n := by omega
    exact hPn (heq ▸ hkP)
  obtain ⟨rows, cols, hbase⟩ := hkP
  have hnotSurj : ¬ Function.Surjective cols := by
    intro hs
    have hc := Fintype.card_le_of_surjective cols hs
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin n, ∀ l, cols l ≠ j := by
    simpa only [Function.Surjective, not_forall, not_exists] using hnotSurj
  have hext (i : I) : (A.submatrix (Fin.cons i rows) (Fin.cons j cols)).det = 0 := by
    by_contra hne
    have hPlarger : P (k + 1) := ⟨Fin.cons i rows, Fin.cons j cols, hne⟩
    have hb : k + 1 ≤ k := Nat.le_findGreatest (by omega) hPlarger
    omega
  obtain ⟨v, hv, hAv, hdeg⟩ := exists_bounded_kernel_of_minor A hA rows (Fin.cons j cols)
    (fun l => by simpa only [Fin.cons_succ, Fin.cons_zero] using hj l)
    (by simpa only [Fin.cons_succ] using hbase) hext
  refine ⟨v, hv, hAv, fun l => (hdeg l).trans ?_⟩
  exact Nat.mul_le_mul_right d (by omega)

end MaximalMinor

section FiniteColumnIndex

variable {F I N : Type*} [Field F] [Fintype N] [DecidableEq N] {d : ℕ}

/-- The bounded polynomial kernel construction for an arbitrary finite column index. -/
theorem exists_bounded_kernel_of_maximal_minors_fintype
    (A : Matrix I N (Polynomial F)) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (hfull : ∀ rows : N → I, (A.submatrix rows id).det = 0) :
    ∃ v : N → Polynomial F, v ≠ 0 ∧ A *ᵥ v = 0 ∧
      ∀ j, (v j).natDegree ≤ (Fintype.card N - 1) * d := by
  classical
  let e : Fin (Fintype.card N) ≃ N := (Fintype.equivFin N).symm
  have hfull' (rows : Fin (Fintype.card N) → I) :
      ((A.submatrix id e).submatrix rows id).det = 0 := by
    have h := (Matrix.det_submatrix_equiv_self e
      (A.submatrix (rows ∘ e.symm) id)).trans (hfull (rows ∘ e.symm))
    simpa only [Matrix.submatrix_submatrix, Function.comp_def,
      Equiv.symm_apply_apply, id_eq] using h
  obtain ⟨v, hv, hAv, hdeg⟩ := exists_bounded_kernel_of_maximal_minors
    (A.submatrix id e) (fun i j => hA i (e j)) hfull'
  refine ⟨v ∘ e.symm, ?_, ?_, fun j => hdeg (e.symm j)⟩
  · intro hz
    apply hv
    funext j
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] using
      congrFun hz (e j)
  · simpa only [Function.comp_id] using
      (Matrix.submatrix_mulVec_equiv A v id e).symm.trans hAv

omit [DecidableEq N] in
/-- Polynomial linear-system lifting: sufficiently many singular specializations
produce a nonzero formal kernel whose coordinate degrees are at most
`(number of columns - 1) * entry degree`. No finite-field assumption is needed. -/
theorem exists_bounded_polynomial_kernel_of_many_singular_specializations
    (A : Matrix I N (Polynomial F)) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (S : Finset F) (hcard : Fintype.card N * d < S.card)
    (hker : ∀ x ∈ S, ∃ v : N → F, v ≠ 0 ∧ (A.map (fun p => p.eval x)) *ᵥ v = 0) :
    ∃ v : N → Polynomial F, v ≠ 0 ∧ A *ᵥ v = 0 ∧
      ∀ j, (v j).natDegree ≤ (Fintype.card N - 1) * d := by
  classical
  exact exists_bounded_kernel_of_maximal_minors_fintype A hA
    (maximal_minor_eq_zero_of_many_singular_specializations A hA S hcard hker)

end FiniteColumnIndex

end PCP.Algebraic.PolynomialMatrixKernel
