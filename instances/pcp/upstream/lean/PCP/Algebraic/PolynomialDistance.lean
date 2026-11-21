/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.Distance
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Distance of low-degree polynomial functions

The large-field branch of Theorem 2.5 in Amireddy–Behera–Srinivasan–Sudan–Willumsgaard,
*A Simple Algebraic Proof of the PCP Theorem*. Mathlib's Schwartz–Zippel theorem gives
the agreement bound `d / |𝔽|`, hence distance at least `1 - d / |𝔽|`.

The inequalities remain valid (but uninformative) when `d ≥ |𝔽|`. Recovering a formal
polynomial from its evaluation function requires the strict bound `d < |𝔽|`.
The binary multilinear bound `2⁻ᵈ` is proved in `PCP.Algebraic.BinaryDistance`.
-/

namespace PCP.Algebraic

open Finset MvPolynomial

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {m d : ℕ}

/-- The probability that a nonzero polynomial vanishes, in rational normalization. -/
theorem eval_zero_agreement_le (p : MvPolynomial (Fin m) 𝔽) (hp : p ≠ 0) :
    relativeAgreement (fun x => eval x p) 0 ≤ (p.totalDegree : ℚ) / Fintype.card 𝔽 := by
  have h := NNRat.coe_le_coe.mpr (schwartz_zippel_totalDegree hp (univ : Finset 𝔽))
  simpa [relativeAgreement, Fintype.card_pi_const] using h

/-- Two distinct polynomials of degree at most `d` agree on at most a `d / |𝔽|` fraction. -/
theorem eval_agreement_le (p q : MvPolynomial (Fin m) 𝔽)
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) (hne : p ≠ q) :
    relativeAgreement (fun x => eval x p) (fun x => eval x q) ≤
      (d : ℚ) / Fintype.card 𝔽 := by
  calc
    _ = relativeAgreement (fun x => eval x (p - q)) 0 := by
      simp [relativeAgreement, eval_sub, sub_eq_zero]
    _ ≤ ((p - q).totalDegree : ℚ) / Fintype.card 𝔽 :=
      eval_zero_agreement_le _ (sub_ne_zero.mpr hne)
    _ ≤ (d : ℚ) / Fintype.card 𝔽 := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (totalDegree_sub p q).trans (max_le hp hq)

/-- Theorem 2.5 (large-field branch), in the pairwise distance form used for decoding. -/
theorem eval_distance_ge (p q : MvPolynomial (Fin m) 𝔽)
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) (hne : p ≠ q) :
    1 - (d : ℚ) / Fintype.card 𝔽 ≤
      relativeDistance (fun x => eval x p) (fun x => eval x q) := by
  have h := eval_agreement_le p q hp hq hne
  rw [relativeAgreement_eq_one_sub_relativeDistance] at h
  linarith

/-- In particular, a nonzero polynomial is nonzero on at least a `1 - d / |𝔽|` fraction. -/
theorem eval_distance_zero_ge (p : MvPolynomial (Fin m) 𝔽)
    (hp : p.totalDegree ≤ d) (hne : p ≠ 0) :
    1 - (d : ℚ) / Fintype.card 𝔽 ≤ relativeDistance (fun x => eval x p) 0 := by
  simpa only [map_zero, Pi.zero_def] using eval_distance_ge p 0 hp (by simp) hne

/-- The agreement threshold for equality is strict. -/
theorem eq_of_eval_agreement_gt (p q : MvPolynomial (Fin m) 𝔽)
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d)
    (h : (d : ℚ) / Fintype.card 𝔽 <
      relativeAgreement (fun x => eval x p) (fun x => eval x q)) : p = q := by
  by_contra hne
  exact (not_lt_of_ge (eval_agreement_le p q hp hq hne)) h

omit [DecidableEq 𝔽] in
/-- Evaluation determines a formal polynomial when its total degree is below the field size. -/
theorem eval_injective_of_totalDegree_lt_card :
    Set.InjOn (fun p : MvPolynomial (Fin m) 𝔽 => fun x => eval x p)
      {p | p.totalDegree < Fintype.card 𝔽} := by
  classical
  intro p hp q hq heval
  dsimp only at heval
  apply eq_of_eval_agreement_gt p q (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  rw [heval, relativeAgreement_self]
  apply (div_lt_one (by exact_mod_cast Fintype.card_pos (α := 𝔽))).mpr
  exact_mod_cast max_lt hp hq

/-- At radius strictly below half the distance bound, the nearby formal polynomial is unique. -/
theorem eq_of_eval_close (p q : MvPolynomial (Fin m) 𝔽)
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d)
    {w : (Fin m → 𝔽) → 𝔽} {ε : ℚ}
    (hradius : 2 * ε < 1 - (d : ℚ) / Fintype.card 𝔽)
    (hwp : relativeDistance w (fun x => eval x p) ≤ ε)
    (hwq : relativeDistance w (fun x => eval x q) ≤ ε) : p = q := by
  by_contra hne
  have hlow := eval_distance_ge p q hp hq hne
  have htriangle := relativeDistance_triangle (fun x => eval x p) w (fun x => eval x q)
  rw [relativeDistance_comm (fun x => eval x p) w] at htriangle
  linarith

/-- A §2's `𝒫_d(m, 𝔽)`: functions represented by a polynomial of total degree at most `d`.

This predicate concerns functions, and does not assert that the representing polynomial
is unique over a finite field.
-/
def IsLowDegree (d : ℕ) (f : (Fin m → 𝔽) → 𝔽) : Prop :=
  ∃ p : MvPolynomial (Fin m) 𝔽, p.totalDegree ≤ d ∧ (fun x => eval x p) = f

omit [Fintype 𝔽] [DecidableEq 𝔽] in
theorem isLowDegree_eval (p : MvPolynomial (Fin m) 𝔽) (hp : p.totalDegree ≤ d) :
    IsLowDegree d (fun x => eval x p) := ⟨p, hp, rfl⟩

theorem IsLowDegree.relativeDistance_ge {f g : (Fin m → 𝔽) → 𝔽}
    (hf : IsLowDegree d f) (hg : IsLowDegree d g) (hne : f ≠ g) :
    1 - (d : ℚ) / Fintype.card 𝔽 ≤ relativeDistance f g := by
  obtain ⟨p, hp, rfl⟩ := hf
  obtain ⟨q, hq, rfl⟩ := hg
  exact eval_distance_ge p q hp hq (fun h => hne (h ▸ rfl))

/-- Uniqueness of a nearby low-degree function, independent of its chosen representation. -/
theorem IsLowDegree.eq_of_close {f g w : (Fin m → 𝔽) → 𝔽} {ε : ℚ}
    (hf : IsLowDegree d f) (hg : IsLowDegree d g)
    (hradius : 2 * ε < 1 - (d : ℚ) / Fintype.card 𝔽)
    (hwf : relativeDistance w f ≤ ε) (hwg : relativeDistance w g ≤ ε) : f = g :=
  eq_of_relativeDistance_le_of_separated
    (C := {f | IsLowDegree d f})
    (fun _ hf _ hg hne => hf.relativeDistance_ge hg hne) hradius hf hg hwf hwg

end PCP.Algebraic
