/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.GeneratorLowDegreeTest
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.IntervalCases

/-!
# Statement and boundary checks for the generator low-degree proof

The independent signatures lock the linear field bound, full multiplicative
generator, ordinary total degree, strict rejection threshold and factor two.
The degree-two example lies far below the paper's cubic field bound `q > C*c^3`.
-/

namespace PCP.Audit.GeneratorLowDegree

open PCP.Algebraic GeneratorLowDegreeTest

universe u_1 u_2

def IntendedSoundnessType : Prop :=
  ∀ {F : Type u_1} {σ : Type u_2} [Field F] {c : ℕ} [Fintype F] {ζ : F}
    [DecidableEq F] [Fintype σ] [DecidableEq σ],
    2 * c < Fintype.card F → IsPrimitiveRoot ζ (Fintype.card F - 1) →
    ∀ (f : (σ → F) → F) {δ : ℚ}, rejectionRate c ζ f ≤ δ →
      δ < 1 / (2 * (c + 2 : ℚ) ^ 2) →
      ∃ P : MvPolynomial σ F, P.totalDegree ≤ c ∧
        relativeDistance f (fun x => MvPolynomial.eval x P) ≤ 2 * δ

def IntendedCharacterizationType : Prop :=
  ∀ {F : Type u_1} {σ : Type u_2} [Field F] {c : ℕ} [Fintype F] {ζ : F} [Finite σ],
    2 * c < Fintype.card F → IsPrimitiveRoot ζ (Fintype.card F - 1) →
    ∀ f : (σ → F) → F, (∀ u v, check c ζ f u v = 0) ↔
      ∃ P : MvPolynomial σ F, P.totalDegree ≤ c ∧ ∀ x, MvPolynomial.eval x P = f x

example : IntendedSoundnessType.{u_1, u_2} := @exists_close
example : IntendedCharacterizationType.{u_1, u_2} := @check_eq_zero_iff_exists_polynomial

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem generator_five : IsPrimitiveRoot (2 : ZMod 5) 4 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by decide) (by decide)
  intro n hn hlt
  interval_cases n <;> decide

/-- Degree two at `q=5=2c+1`: no large-field hypothesis can enter unnoticed. -/
example (f : (Fin 3 → ZMod 5) → ZMod 5) {δ : ℚ}
    (hrej : rejectionRate 2 2 f ≤ δ) (hδ : δ < 1 / 32) :
    ∃ P : MvPolynomial (Fin 3) (ZMod 5), P.totalDegree ≤ 2 ∧
      relativeDistance f (fun x => MvPolynomial.eval x P) ≤ 2 * δ := by
  apply exists_close (by decide) (by simpa using generator_five) f hrej
  norm_num
  exact hδ

/-- The constant-monomial weights add to one. -/
example : ∑ i : Fin 3, weights 2 (2 : ZMod 5) i = 1 :=
  sum_weights (by decide) (by simpa using generator_five)

/-- Degree zero includes the smallest field and empty coordinate types. -/
example {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : (σ → ZMod 2) → ZMod 2) {δ : ℚ}
    (hrej : rejectionRate 0 1 f ≤ δ) (hδ : δ < 1 / 8) :
    ∃ P : MvPolynomial σ (ZMod 2), P.totalDegree ≤ 0 ∧
      relativeDistance f (fun x => MvPolynomial.eval x P) ≤ 2 * δ := by
  apply exists_close (by decide) (by simp) f hrej
  norm_num
  exact hδ

end PCP.Audit.GeneratorLowDegree
