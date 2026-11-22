/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BooleanCoefficientArithmetic
import PCP.Algebraic.HadamardDerivedOracle
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Recovering Boolean coefficients from evaluations

In characteristic two, summing the values on all subsets of a squarefree support
recovers its coefficient. A degree-three query thus needs at most eight field
evaluations per coefficient. This computes the existing cubic query translation
without constructing or reducing a formal polynomial.
-/

namespace PCP.Algebraic.BooleanCoefficientRecovery

open Finset BinaryPolynomialSpace

variable {t r : ℕ}

/-- The Boolean point with precisely the specified nonzero coordinates. -/
def indicator (s : Finset (Fin t)) : Fin t → ZMod 2 := fun i => if i ∈ s then 1 else 0

/-- The subset transform, restricted to the permitted coefficient supports. -/
def recover (f : (Fin t → ZMod 2) → ZMod 2) : Coefficients t r :=
  fun s => ∑ u ∈ s.val.powerset, f (indicator u)

theorem subset_parity (s v : Finset (Fin t)) :
    (∑ u ∈ s.powerset, if v ⊆ u then (1 : ZMod 2) else 0) =
      if v = s then 1 else 0 := by
  induction s using Finset.induction_on generalizing v with
  | empty => simp only [powerset_empty, sum_singleton, subset_empty]
  | @insert a s ha ih =>
    rw [sum_powerset_insert ha]
    by_cases hav : a ∈ v
    · have hz : (∑ u ∈ s.powerset, if v ⊆ u then (1 : ZMod 2) else 0) = 0 := by
        apply sum_eq_zero
        intro u hu
        have hn : ¬ v ⊆ u := fun h => ha ((mem_powerset.mp hu) (h hav))
        simp only [ite_eq_right hn]
      rw [hz, zero_add]
      simp_rw [subset_insert_iff]
      rw [ih]
      have he : v.erase a = s ↔ v = insert a s := by
        constructor
        · intro h
          rw [← h, insert_erase hav]
        · intro h
          simp [h, ha]
      simp only [he]
    · simp_rw [subset_insert_iff_of_notMem hav]
      have he : v ≠ insert a s := fun h => hav (h ▸ mem_insert_self a s)
      rw [ite_eq_right he]
      exact CharTwo.add_self_eq_zero _

theorem prod_indicator (u v : Finset (Fin t)) :
    (∏ i ∈ v, indicator u i) = if v ⊆ u then (1 : ZMod 2) else 0 := by
  by_cases h : v ⊆ u
  · rw [ite_eq_left h]
    exact prod_eq_one fun i hi => ite_eq_left (h hi)
  · rw [ite_eq_right h]
    obtain ⟨i, hiv, hiu⟩ := Finset.not_subset.mp h
    exact prod_eq_zero hiv (ite_eq_right hiu)

/-- The transform recovers every stored coefficient, including the empty support. -/
@[simp] theorem recover_evaluate (p : Coefficients t r) :
    recover (fun x => BooleanCoefficientArithmetic.evaluate x p) = p := by
  funext s
  simp only [recover, BooleanCoefficientArithmetic.evaluate]
  rw [sum_comm]
  simp_rw [prod_indicator, ← mul_sum, subset_parity, mul_ite, mul_one, mul_zero]
  simpa only [Subtype.ext_iff, mem_univ, ite_true] using
    (Finset.sum_ite_eq' (Finset.univ : Finset (Monomials t r)) s p)

/-- Equality to a bounded polynomial function certifies the computed coefficients. -/
theorem recover_eq (f : (Fin t → ZMod 2) → ZMod 2) (p : Coefficients t r)
    (h : ∀ x, f x = BinaryPolynomialSpace.evaluate x p) : recover f = p := by
  have hf : f = fun x => BooleanCoefficientArithmetic.evaluate x p := by
    funext x
    rw [BooleanCoefficientArithmetic.evaluate_eq, h]
  rw [hf, recover_evaluate]

/-- One coefficient reads precisely the subsets of its support. -/
theorem evaluations_per_coefficient_le (s : Monomials t r) :
    s.val.powerset.card ≤ 2 ^ r := by
  rw [card_powerset]
  exact Nat.pow_le_pow_right (by decide) s.property

section Composition

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F]

/-- Translate an affine observation of an executable field function into coefficients. -/
def compose (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (f : F → F)
    (L : Coefficients t 1) : Coefficients t r :=
  recover (fun x => BooleanCoefficientArithmetic.evaluate (ρ (f (ρ.symm x))) L)

/-- A polynomial semantics of bounded degree justifies the finite subset algorithm. -/
theorem compose_eq_query (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (f : F → F)
    (P : Polynomial F) (hf : ∀ u, f u = P.eval u) (L : Coefficients t 1)
    (hP : P.natDegree ≤ r) : compose ρ f L = HadamardComposition.query ρ P L hP := by
  apply recover_eq
  intro x
  rw [BooleanCoefficientArithmetic.evaluate_eq, hf]
  simpa only [LinearEquiv.apply_symm_apply] using
    (HadamardComposition.evaluate_query ρ P L hP (ρ.symm x)).symm

/-- The verifier's unweighted cubic translation is an executable coefficient vector. -/
def cubicQuery (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (L : Coefficients t 1) : Coefficients t 3 := compose ρ (fun u => u ^ 3 - 1) L

/-- Multiplying the cubic by any field weight does not change the coefficient bound. -/
def weightedCubicQuery (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : F)
    (L : Coefficients t 1) : Coefficients t 3 := compose ρ (fun u => a * (u ^ 3 - 1)) L

variable [Nontrivial F]

@[simp] theorem cubicQuery_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2))
    (L : Coefficients t 1) : cubicQuery ρ L =
      HadamardComposition.query ρ HadamardDerivedOracle.cubic L
        HadamardDerivedOracle.natDegree_cubic_le :=
  compose_eq_query ρ _ _ (fun u => (HadamardDerivedOracle.eval_cubic u).symm) L _

@[simp] theorem weightedCubicQuery_eq (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (a : F)
    (L : Coefficients t 1) : weightedCubicQuery ρ a L =
      HadamardComposition.query ρ (HadamardDerivedOracle.weightedCubic a) L
        (HadamardDerivedOracle.natDegree_weightedCubic_le a) :=
  compose_eq_query ρ _ _ (fun u => (HadamardDerivedOracle.eval_weightedCubic a u).symm) L _

end Composition

end PCP.Algebraic.BooleanCoefficientRecovery
