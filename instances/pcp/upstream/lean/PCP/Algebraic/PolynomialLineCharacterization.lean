/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.PolynomialLineDegree
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact characterization by affine-line restrictions

If every affine-line restriction has ordinary univariate degree at most `d`,
and the field has more than `2*d` elements, the function is represented by an
actual multivariate polynomial of ordinary total degree at most `d`.

Dimension induction interpolates `d+1` slices into a polynomial of total degree
at most `2*d`. Origin-line restrictions then remove its higher homogeneous pieces.
No low-degree decoding or soundness premise is assumed.
-/

namespace PCP.Algebraic.PolynomialLine

open Finset MvPolynomial

variable {F : Type*} [Field F]

/-- A genuine bounded-degree polynomial represents the function on every affine line. -/
def HasLowDegreeLines {σ : Type*} (d : ℕ) (f : (σ → F) → F) : Prop :=
  ∀ u v, ∃ p : Polynomial F, p.natDegree ≤ d ∧ ∀ t, p.eval t = f (point u v t)

/-- Evaluation of an ordinary total-degree-bounded polynomial has low-degree lines. -/
theorem hasLowDegreeLines_eval {σ : Type*} {d : ℕ} (P : MvPolynomial σ F)
    (hP : P.totalDegree ≤ d) : HasLowDegreeLines d (fun x => eval x P) := by
  intro u v
  exact ⟨restrict u v P, natDegree_restrict_le_of_totalDegree_le u v P hP,
    eval_restrict u v P⟩

/-- Embedding a univariate polynomial in one variable does not increase total degree. -/
theorem totalDegree_toMvPolynomial_le {σ : Type*} (p : Polynomial F) (i : σ) :
    (p.toMvPolynomial i).totalDegree ≤ p.natDegree := by
  classical
  conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
    Polynomial.toMvPolynomial_X]
  apply totalDegree_finsetSum_le
  intro k hk
  apply (totalDegree_mul _ _).trans
  simpa using Polynomial.le_natDegree_of_mem_supp k hk

/-- Interpolate polynomials in the remaining variables at selected first coordinates. -/
noncomputable def interpolateSlices {n d : ℕ} (a : Fin (d + 1) → F)
    (P : Fin (d + 1) → MvPolynomial (Fin n) F) : MvPolynomial (Fin (n + 1)) F :=
  ∑ i, (Lagrange.basis univ a i).toMvPolynomial 0 * rename Fin.succ (P i)

theorem totalDegree_interpolateSlices_le {n d : ℕ} {a : Fin (d + 1) → F}
    (ha : Function.Injective a) (P : Fin (d + 1) → MvPolynomial (Fin n) F)
    (hP : ∀ i, (P i).totalDegree ≤ d) :
    (interpolateSlices a P).totalDegree ≤ 2 * d := by
  classical
  apply totalDegree_finsetSum_le
  intro i _
  have hL : (Lagrange.basis univ a i).natDegree = d := by
    simpa using Lagrange.natDegree_basis ha.injOn (mem_univ i)
  apply (totalDegree_mul _ _).trans
  have hleft := totalDegree_toMvPolynomial_le (Lagrange.basis univ a i) (0 : Fin (n + 1))
  have hright := (totalDegree_rename_le Fin.succ (P i)).trans (hP i)
  omega

theorem eval_interpolateSlices {n d : ℕ} (a : Fin (d + 1) → F)
    (P : Fin (d + 1) → MvPolynomial (Fin n) F) (x : F) (y : Fin n → F) :
    eval (Fin.cons x y) (interpolateSlices a P) =
      ∑ i, (Lagrange.basis univ a i).eval x * eval y (P i) := by
  simp [interpolateSlices, eval_toMvPolynomial, eval_rename, Function.comp_def]

/-- Slice interpolation recovers all first-coordinate lines, not only the selected slices. -/
theorem eval_interpolateSlices_eq {n d : ℕ} {a : Fin (d + 1) → F}
    (ha : Function.Injective a) (P : Fin (d + 1) → MvPolynomial (Fin n) F)
    (f : (Fin (n + 1) → F) → F)
    (hP : ∀ i y, eval y (P i) = f (Fin.cons (a i) y))
    (haxis : ∀ y : Fin n → F, ∃ p : Polynomial F,
      p.natDegree ≤ d ∧ ∀ t, p.eval t = f (Fin.cons t y))
    (z : Fin (n + 1) → F) : eval z (interpolateSlices a P) = f z := by
  obtain ⟨p, hp, heval⟩ := haxis (Fin.tail z)
  have hdegree : p.degree < (univ : Finset (Fin (d + 1))).card := by
    apply Polynomial.degree_le_natDegree.trans_lt
    simpa only [card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
      (show (p.natDegree : WithBot ℕ) < ↑(d + 1) by
        exact_mod_cast hp.trans_lt (Nat.lt_succ_self d))
  have hid := Lagrange.eq_interpolate (f := p) ha.injOn hdegree
  have hvalue := congrArg (fun q : Polynomial F => q.eval (z 0)) hid
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at hvalue
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hvalue
  rw [← Fin.cons_self_tail z, eval_interpolateSlices]
  rw [← heval]
  rw [hvalue]
  apply sum_congr rfl
  intro i _
  rw [heval, ← hP]
  ring

variable [Fintype F]

/-- Exact line-to-polynomial characterization, using ordinary total degree. -/
theorem exists_polynomial_of_hasLowDegreeLines {n d : ℕ}
    (f : (Fin n → F) → F) (hcard : 2 * d < Fintype.card F)
    (hf : HasLowDegreeLines d f) :
    ∃ P : MvPolynomial (Fin n) F, P.totalDegree ≤ d ∧ ∀ x, eval x P = f x := by
  classical
  induction n with
  | zero =>
      refine ⟨C (f 0), by simp, ?_⟩
      intro x
      simpa using congrArg f (Subsingleton.elim (0 : Fin 0 → F) x)
  | succ n ih =>
      obtain ⟨a⟩ := Function.Embedding.nonempty_of_card_le
        (show Fintype.card (Fin (d + 1)) ≤ Fintype.card F by
          simp only [Fintype.card_fin]
          omega)
      have hslice (x : F) : HasLowDegreeLines d (fun y : Fin n → F => f (Fin.cons x y)) := by
        intro u v
        obtain ⟨p, hp, heval⟩ := hf (Fin.cons x u) (Fin.cons 0 v)
        refine ⟨p, hp, fun t => ?_⟩
        rw [heval]
        congr 1
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [point_apply]
      choose P hP using fun i : Fin (d + 1) => ih (fun y => f (Fin.cons (a i) y)) (hslice (a i))
      have haxis (y : Fin n → F) : ∃ p : Polynomial F,
          p.natDegree ≤ d ∧ ∀ t, p.eval t = f (Fin.cons t y) := by
        obtain ⟨p, hp, heval⟩ := hf (Fin.cons 0 y) (Fin.cons 1 0)
        refine ⟨p, hp, fun t => ?_⟩
        rw [heval]
        congr 1
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [point_apply]
      let Q := interpolateSlices a P
      have hQ : Q.totalDegree ≤ 2 * d :=
        totalDegree_interpolateSlices_le a.injective P (fun i => (hP i).1)
      have heval : ∀ x, eval x Q = f x :=
        eval_interpolateSlices_eq a.injective P f (fun i => (hP i).2) haxis
      refine ⟨Q, totalDegree_le_of_origin_restrictions Q (hQ.trans_lt hcard) ?_, heval⟩
      intro v
      obtain ⟨p, hp, hpval⟩ := hf 0 v
      have hid : restrict 0 v Q = p := by
        apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ Function.injective_id
        · intro t
          rw [eval_restrict, heval, hpval]
        · exact (max_le ((natDegree_restrict_le _ _ _).trans hQ)
            (hp.trans (by omega))).trans_lt hcard
      rw [hid]
      exact hp

/-- The exact affine-line characterization, with both directions proved. -/
theorem hasLowDegreeLines_iff_exists_polynomial {n d : ℕ}
    (f : (Fin n → F) → F) (hcard : 2 * d < Fintype.card F) :
    HasLowDegreeLines d f ↔
      ∃ P : MvPolynomial (Fin n) F, P.totalDegree ≤ d ∧ ∀ x, eval x P = f x := by
  refine ⟨exists_polynomial_of_hasLowDegreeLines f hcard, ?_⟩
  rintro ⟨P, hP, heval⟩
  simpa only [heval] using hasLowDegreeLines_eval P hP

/-- The exact characterization is independent of the chosen finite coordinate type. -/
theorem exists_polynomial_of_hasLowDegreeLines_finite {σ : Type*} [Finite σ] {d : ℕ}
    (f : (σ → F) → F) (hcard : 2 * d < Fintype.card F)
    (hf : HasLowDegreeLines d f) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ d ∧ ∀ x, eval x P = f x := by
  classical
  let _ := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  have hg : HasLowDegreeLines d (fun x : Fin (Fintype.card σ) → F => f (x ∘ e)) := by
    intro u v
    obtain ⟨p, hp, heval⟩ := hf (u ∘ e) (v ∘ e)
    refine ⟨p, hp, fun t => ?_⟩
    exact heval t
  obtain ⟨Q, hQ, heval⟩ := exists_polynomial_of_hasLowDegreeLines _ hcard hg
  refine ⟨rename e.symm Q, (totalDegree_rename_le _ _).trans hQ, ?_⟩
  intro x
  rw [eval_rename, heval]
  congr 1
  ext i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- Both directions of the affine-line characterization for arbitrary finite coordinates. -/
theorem hasLowDegreeLines_iff_exists_polynomial_finite {σ : Type*} [Finite σ] {d : ℕ}
    (f : (σ → F) → F) (hcard : 2 * d < Fintype.card F) :
    HasLowDegreeLines d f ↔
      ∃ P : MvPolynomial σ F, P.totalDegree ≤ d ∧ ∀ x, eval x P = f x := by
  refine ⟨exists_polynomial_of_hasLowDegreeLines_finite f hcard, ?_⟩
  rintro ⟨P, hP, heval⟩
  simpa only [heval] using hasLowDegreeLines_eval P hP

end PCP.Algebraic.PolynomialLine
