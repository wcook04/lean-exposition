/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientEvaluationCost

/-!
# The numeric subset transform is exact Boolean coefficient recovery

A truth table is stored in increasing numeric point order. Evaluating this table
with all masks gives the subset sum used by Boolean coefficient recovery.
-/

namespace PCP.Lang.BooleanCoefficientList

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientIndex BooleanLoops

/-- Every Boolean point, in its production numeric order. -/
def fullMasks (t : ℕ) : List ℕ := List.ofFn fun i : Fin (2 ^ t) => i.val

/-- The binary truth table of a Boolean function. -/
def table (t : ℕ) (f : (Fin t → ZMod 2) → ZMod 2) : List ℕ :=
  List.ofFn fun i : Fin (2 ^ t) => (f (point t i)).val

/-- An arbitrary requested mask list is recovered by the same stored evaluation kernel. -/
def recoverBits (t : ℕ) (ms values : List ℕ) : List ℕ :=
  ms.map fun m => terms t m (fullMasks t) values % 2

theorem terms_recover (t : ℕ) (f : (Fin t → ZMod 2) → ZMod 2) (s : Finset (Fin t)) :
    (terms t (subsetCodeEquiv t s).val (fullMasks t) (table t f) : ZMod 2) =
      ∑ u ∈ s.powerset, f (BooleanCoefficientRecovery.indicator u) := by
  rw [fullMasks, table, terms_ofFn]
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [← (subsetCodeEquiv t).sum_comp]
  simp only [truth, BooleanMaskSubset.contains_iff, Equiv.symm_apply_apply,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero]
  have hfilter : Finset.univ.filter (fun u : Finset (Fin t) => u ⊆ s) = s.powerset := by
    ext u
    simp
  rw [← Finset.sum_filter, hfilter]
  apply Finset.sum_congr rfl
  intro u _
  simp [point]

/-- The stored transform returns the precise dense coefficient word. -/
theorem recoverBits_eq {t r : ℕ} (f : (Fin t → ZMod 2) → ZMod 2) :
    recoverBits t (BooleanMask.masks t r) (table t f) =
      encode (BooleanCoefficientRecovery.recover f : Coefficients t r) := by
  rw [recoverBits, BooleanMask.masks_eq_canonicalMasks]
  simp only [BooleanMask.canonicalMasks, List.map_ofFn, encode]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  rw [BooleanMask.monomial_code]
  have h := congrArg ZMod.val (terms_recover t f ((monomialEquiv t r).symm i).val)
  simpa only [ZMod.val_natCast, wordEquiv_apply, BooleanCoefficientRecovery.recover] using h

end PCP.Lang.BooleanCoefficientList
