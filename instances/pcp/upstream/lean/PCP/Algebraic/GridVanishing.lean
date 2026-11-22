/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Combinatorics.Nullstellensatz

/-!
# Degree-bounded certificates for vanishing on a grid

Lemma 2.9 of A, *A Simple Algebraic Proof of the PCP Theorem*. We adapt mathlib's
Combinatorial Nullstellensatz to an ordinary finite family of coefficient polynomials,
and expose the degree bound on each nonzero coefficient. The latter avoids losing
information to natural-number subtraction when the input degree is below the grid size.

All identities are identities of formal polynomials. No algorithmic cost is asserted.
-/

namespace PCP.Algebraic.GridVanishing

open Finset MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- The coordinate polynomial `∏ a ∈ H, (X i - a)`. -/
noncomputable def coordinate (H : Finset R) (i : σ) : MvPolynomial σ R :=
  ∏ a ∈ H, (X i - C a)

/-- Vanishing at every point of the Cartesian grid, including zero-dimensional grids. -/
def VanishesOn (H : Finset R) (p : MvPolynomial σ R) : Prop :=
  ∀ x : σ → R, (∀ i, x i ∈ H) → eval x p = 0

@[simp] theorem coordinate_empty (i : σ) : coordinate (∅ : Finset R) i = 1 := by
  simp [coordinate]

@[simp] theorem coordinate_singleton (a : R) (i : σ) :
    coordinate {a} i = X i - C a := by
  simp [coordinate]

theorem eval_coordinate (H : Finset R) (i : σ) (x : σ → R) :
    eval x (coordinate H i) = ∏ a ∈ H, (x i - a) := by
  simp [coordinate]

theorem eval_coordinate_eq_zero (H : Finset R) (i : σ) (x : σ → R) (hx : x i ∈ H) :
    eval x (coordinate H i) = 0 := by
  classical
  rw [eval_coordinate]
  exact prod_eq_zero hx (sub_self _)

theorem coordinate_vanishesOn (H : Finset R) (i : σ) : VanishesOn H (coordinate H i) :=
  fun x hx => eval_coordinate_eq_zero H i x (hx i)

section Domain

variable [IsDomain R]

theorem coordinate_ne_zero (H : Finset R) (i : σ) : coordinate H i ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro a _ h
  have := congrArg (fun p => p.coeff (Finsupp.single i 1)) h
  simp [eq_comm] at this

variable [Finite σ]

/-- Total degree is additive on nonzero factors over a domain. -/
theorem totalDegree_mul_eq {p q : MvPolynomial σ R} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).totalDegree = p.totalDegree + q.totalDegree := by
  let : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  rw [← degree_degLexDegree, MonomialOrder.degLex.degree_mul hp hq, map_add,
    degree_degLexDegree, degree_degLexDegree]

theorem totalDegree_coordinate (H : Finset R) (i : σ) :
    (coordinate H i).totalDegree = H.card := by
  classical
  let : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  rw [← degree_degLexDegree, coordinate, MonomialOrder.degLex.degree_prod]
  · simp [MonomialOrder.degree_X_sub_C]
  · intro a _
    exact (MonomialOrder.lex.monic_X_sub_C i a).ne_zero

/-- Below the grid size, the only polynomial vanishing on the grid is zero. -/
theorem eq_zero_of_totalDegree_lt (H : Finset R)
    (p : MvPolynomial σ R) (hp : VanishesOn H p) (hdeg : p.totalDegree < H.card) : p = 0 := by
  exact eq_zero_of_eval_zero_at_prod_finset p (fun _ => H)
    (fun i => (degreeOf_le_totalDegree p i).trans_lt hdeg) hp

variable [Fintype σ]

omit [IsDomain R] [Finite σ] in
theorem vanishesOn_of_eq_sum (H : Finset R) (p : MvPolynomial σ R)
    (Q : σ → MvPolynomial σ R) (hp : p = ∑ i, Q i * coordinate H i) : VanishesOn H p := by
  intro x hx
  rw [hp, map_sum]
  apply sum_eq_zero
  intro i _
  rw [map_mul, eval_coordinate_eq_zero H i x (hx i), mul_zero]

/-- A degree-sensitive form of Lemma 2.9, retaining the bound before subtraction. -/
theorem exists_decomposition (H : Finset R)
    (p : MvPolynomial σ R) (hp : VanishesOn H p) :
    ∃ Q : σ → MvPolynomial σ R,
      (∀ i, Q i ≠ 0 → (Q i).totalDegree + H.card ≤ p.totalDegree) ∧
      p = ∑ i, Q i * coordinate H i := by
  classical
  rcases H.eq_empty_or_nonempty with rfl | hH
  · cases isEmpty_or_nonempty σ with
    | inl h =>
        have hz : p = 0 := by
          have he := hp (fun i => isEmptyElim i) (fun i => isEmptyElim i)
          rw [p.eq_C_of_isEmpty] at he ⊢
          simpa using congrArg (C (σ := σ)) he
        exact ⟨fun _ => 0, by simp, by simp [hz]⟩
    | inr h =>
        obtain ⟨i⟩ := h
        refine ⟨fun j => if j = i then p else 0, ?_, ?_⟩
        · intro j hj
          by_cases hji : j = i <;> simp_all
        · simp
  · obtain ⟨Q, hQ, hsum⟩ := combinatorial_nullstellensatz_exists_linearCombination
      (fun _ : σ => H) (fun _ => hH) p hp
    refine ⟨Q, ?_, ?_⟩
    · intro i hi
      have h := hQ i
      change (coordinate H i * Q i).totalDegree ≤ p.totalDegree at h
      rw [totalDegree_mul_eq (coordinate_ne_zero H i) hi, totalDegree_coordinate] at h
      simpa [add_comm] using h
    · rw [hsum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · simp only [smul_eq_mul, coordinate]
      · intro i
        simp

/-- Lemma 2.9: a bounded family of multiples of the coordinate vanishing polynomials. -/
theorem vanishesOn_iff_exists_decomposition (H : Finset R)
    (p : MvPolynomial σ R) :
    VanishesOn H p ↔ ∃ Q : σ → MvPolynomial σ R,
      (∀ i, (Q i).totalDegree ≤ p.totalDegree - H.card) ∧
      p = ∑ i, Q i * coordinate H i := by
  classical
  constructor
  · intro hp
    obtain ⟨Q, hQ, hsum⟩ := exists_decomposition H p hp
    refine ⟨Q, fun i => ?_, hsum⟩
    by_cases hi : Q i = 0
    · simp [hi]
    · exact Nat.le_sub_of_add_le (hQ i hi)
  · rintro ⟨Q, _, hsum⟩
    exact vanishesOn_of_eq_sum H p Q hsum

end Domain

end PCP.Algebraic.GridVanishing
