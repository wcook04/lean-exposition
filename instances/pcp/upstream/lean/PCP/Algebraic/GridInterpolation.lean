/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Lagrange

/-!
# Interpolation on a finite Cartesian grid

The mathematical low-degree extension in Fact 2.4. The interpolation basis is the
product, over coordinates, of mathlib's univariate Lagrange basis polynomials.
Uniqueness uses individual degree bounds and a nonempty grid alphabet. No claim about
the running time of constructing the extension is made here.
-/

namespace PCP.Algebraic.GridInterpolation

open Finset MvPolynomial

variable {𝔽 σ : Type*} [Field 𝔽] [DecidableEq 𝔽] [Fintype σ] [DecidableEq σ]

omit [DecidableEq 𝔽] [Fintype σ] in
/-- Embedding a univariate polynomial affects only its chosen variable. -/
theorem degreeOf_toMvPolynomial_le (p : Polynomial 𝔽) (i j : σ) :
    (p.toMvPolynomial i).degreeOf j ≤ if i = j then p.natDegree else 0 := by
  conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
    Polynomial.toMvPolynomial_X]
  apply (degreeOf_sum_le j _ _).trans
  apply Finset.sup_le
  intro k hk
  apply (degreeOf_mul_le j _ _).trans
  by_cases hij : i = j
  · subst i
    simpa using Polynomial.le_natDegree_of_mem_supp k hk
  · simp [degreeOf_X_pow_of_ne k (Ne.symm hij), hij]

/-- The grid basis polynomial which is one at `a` and zero at the other grid points. -/
noncomputable def basis (H : Finset 𝔽) (a : σ → H) : MvPolynomial σ 𝔽 :=
  ∏ i, (Lagrange.basis H id (a i : 𝔽)).toMvPolynomial i

omit [DecidableEq σ] in
theorem eval_basis (H : Finset 𝔽) (a b : σ → H) :
    eval (fun i => (b i : 𝔽)) (basis H a) = if a = b then 1 else 0 := by
  classical
  rw [basis, map_prod]
  simp only [eval_toMvPolynomial]
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    apply prod_eq_one
    intro i _
    exact Lagrange.eval_basis_self (fun _ _ _ _ h => h) (a i).property
  · rw [ite_eq_right hab]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    apply prod_eq_zero (mem_univ i)
    exact Lagrange.eval_basis_of_ne (v := id) (fun h => hi (Subtype.ext h)) (b i).property

omit [DecidableEq σ] in
theorem degreeOf_basis_le (H : Finset 𝔽) (a : σ → H) (j : σ) :
    (basis H a).degreeOf j ≤ H.card - 1 := by
  classical
  calc
    _ ≤ ∑ i : σ, ((Lagrange.basis H id (a i : 𝔽)).toMvPolynomial i).degreeOf j :=
      degreeOf_prod_le j _ _
    _ ≤ ∑ i : σ, if i = j then H.card - 1 else 0 := by
      apply sum_le_sum
      intro i _
      simpa only [Lagrange.natDegree_basis (v := id) (fun _ _ _ _ h => h) (a i).property]
        using degreeOf_toMvPolynomial_le (Lagrange.basis H id (a i : 𝔽)) i j
    _ = H.card - 1 := by simp

/-- Linear interpolation from a table on the grid to a formal multivariate polynomial. -/
noncomputable def interpolate (H : Finset 𝔽) : ((σ → H) → 𝔽) →ₗ[𝔽] MvPolynomial σ 𝔽 :=
  ∑ a : σ → H, (LinearMap.proj a).smulRight (basis H a)

theorem interpolate_apply (H : Finset 𝔽) (f : (σ → H) → 𝔽) :
    interpolate H f = ∑ a : σ → H, f a • basis H a := by
  simp [interpolate]

@[simp] theorem eval_interpolate (H : Finset 𝔽) (f : (σ → H) → 𝔽) (a : σ → H) :
    eval (fun i => (a i : 𝔽)) (interpolate H f) = f a := by
  classical
  rw [interpolate_apply, map_sum]
  simp [MvPolynomial.smul_eq_C_mul, eval_basis]

theorem degreeOf_interpolate_le (H : Finset 𝔽) (f : (σ → H) → 𝔽) (i : σ) :
    (interpolate H f).degreeOf i ≤ H.card - 1 := by
  rw [interpolate_apply]
  apply (degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro a _
  rw [MvPolynomial.smul_eq_C_mul]
  exact (degreeOf_mul_le i _ _).trans (by simpa using degreeOf_basis_le H a i)

/-- The total-degree estimate in Fact 2.4. -/
theorem totalDegree_interpolate_le (H : Finset 𝔽) (f : (σ → H) → 𝔽) :
    (interpolate H f).totalDegree ≤ (H.card - 1) * Fintype.card σ := by
  classical
  rw [totalDegree, Finset.sup_le_iff]
  intro s hs
  calc
    s.sum (fun _ n => n) = ∑ i : σ, s i := by rw [Finsupp.sum_fintype]; simp
    _ ≤ ∑ _i : σ, (H.card - 1) := sum_le_sum fun i _ =>
      (monomial_le_degreeOf i hs).trans (degreeOf_interpolate_le H f i)
    _ = (H.card - 1) * Fintype.card σ := by simp [mul_comm]

omit [DecidableEq 𝔽] in
/-- A polynomial of individual degree below the grid size is determined on that grid. -/
theorem eq_zero_of_eval_grid_eq_zero {m : ℕ} (H : Finset 𝔽) (p : MvPolynomial (Fin m) 𝔽)
    (hdeg : ∀ i, p.degreeOf i < H.card)
    (heval : ∀ a : Fin m → H, eval (fun i => (a i : 𝔽)) p = 0) : p = 0 := by
  induction m with
  | zero =>
      rw [p.eq_C_of_isEmpty] at *
      simpa using heval (fun i => Fin.elim0 i)
  | succ m ih =>
      apply (finSuccEquiv 𝔽 m).injective
      rw [map_zero]
      apply Polynomial.ext
      intro k
      rw [Polynomial.coeff_zero]
      apply ih ((finSuccEquiv 𝔽 m p).coeff k)
        (fun i => (degreeOf_coeff_finSuccEquiv p i k).trans_lt (hdeg i.succ))
      intro a
      let P := (finSuccEquiv 𝔽 m p).map (eval (fun i => (a i : 𝔽)))
      have hP : P = 0 := by
        apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero H
        · have hnat : P.natDegree < H.card :=
            Polynomial.natDegree_map_le.trans_lt ((natDegree_finSuccEquiv p).trans_lt (hdeg 0))
          exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hnat)
        · intro x hx
          have h := heval (Fin.cons ⟨x, hx⟩ a)
          rw [← eval_eq_eval_mv_eval']
          convert h using 1
          apply congrArg (fun y : Fin (m + 1) → 𝔽 => eval y p)
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
      have hcoeff := congrArg (fun q : Polynomial 𝔽 => q.coeff k) hP
      simpa [P] using hcoeff

omit [DecidableEq 𝔽] in
theorem eq_of_eval_grid_eq {m : ℕ} (H : Finset 𝔽) (p q : MvPolynomial (Fin m) 𝔽)
    (hp : ∀ i, p.degreeOf i < H.card) (hq : ∀ i, q.degreeOf i < H.card)
    (heval : ∀ a : Fin m → H, eval (fun i => (a i : 𝔽)) p = eval (fun i => (a i : 𝔽)) q) :
    p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_grid_eq_zero H (p - q)
    (fun i => (degreeOf_sub_le i p q).trans_lt (max_lt (hp i) (hq i)))
  intro a
  simp [eval_sub, heval a]

/-- Interpolation recovers a formal polynomial under the individual-degree bound. -/
theorem interpolate_eval {m : ℕ} (H : Finset 𝔽) (hH : H.Nonempty)
    (p : MvPolynomial (Fin m) 𝔽) (hp : ∀ i, p.degreeOf i ≤ H.card - 1) :
    interpolate H (fun a => eval (fun i => (a i : 𝔽)) p) = p := by
  apply eq_of_eval_grid_eq H
  · intro i
    exact (degreeOf_interpolate_le H _ i).trans_lt (Nat.sub_lt (card_pos.mpr hH) (by decide))
  · intro i
    exact (hp i).trans_lt (Nat.sub_lt (card_pos.mpr hH) (by decide))
  · intro a
    exact eval_interpolate H _ a

omit [DecidableEq 𝔽] in
/-- The existence and uniqueness part of Fact 2.4, for a nonempty grid alphabet. -/
theorem existsUnique_extension {m : ℕ} (H : Finset 𝔽) (hH : H.Nonempty)
    (f : (Fin m → H) → 𝔽) :
    ∃! p : MvPolynomial (Fin m) 𝔽, (∀ i, p.degreeOf i ≤ H.card - 1) ∧
      ∀ a : Fin m → H, eval (fun i => (a i : 𝔽)) p = f a := by
  classical
  refine ⟨interpolate H f, ⟨degreeOf_interpolate_le H f, eval_interpolate H f⟩, ?_⟩
  intro p hp
  apply eq_of_eval_grid_eq H
  · intro i
    exact (hp.1 i).trans_lt (Nat.sub_lt (card_pos.mpr hH) (by decide))
  · intro i
    exact (degreeOf_interpolate_le H f i).trans_lt (Nat.sub_lt (card_pos.mpr hH) (by decide))
  · intro a
    rw [hp.2 a, eval_interpolate]

end PCP.Algebraic.GridInterpolation
