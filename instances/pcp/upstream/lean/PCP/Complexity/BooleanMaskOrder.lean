/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanMaskLang
import Mathlib.Data.List.Sort

/-!
# Increasing numeric enumeration of bounded Boolean monomials

Filtering consecutive integer masks by population count gives exactly the order
of the production coefficient codec, without a run-time finite-type enumeration
or sorting operation.
-/

namespace PCP.Lang.BooleanMask

open PCP.Algebraic BinaryPolynomialSelector
open BooleanCoefficientIndex

/-- Concrete stored masks, in increasing numeric order. -/
def masks (t r : ℕ) : List ℕ :=
  (List.range (2 ^ t)).filter fun n => decide ((digits t n).sum ≤ r)

@[simp] theorem mem_masks (t r n : ℕ) :
    n ∈ masks t r ↔ n < 2 ^ t ∧ (digits t n).sum ≤ r := by
  simp [masks]

/-- The semantic increasing enumeration of the bounded-code subtype. -/
def canonicalMasks (t r : ℕ) : List ℕ :=
  List.ofFn fun j : Fin (dimension t r) =>
    (monoEquivOfFin (BoundedCode t r) (card_boundedCode t r) j).val.val

theorem canonicalMasks_pairwise (t r : ℕ) : (canonicalMasks t r).Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact (monoEquivOfFin (BoundedCode t r) (card_boundedCode t r)).strictMono hij

theorem mem_canonicalMasks (t r n : ℕ) :
    n ∈ canonicalMasks t r ↔ n < 2 ^ t ∧ (digits t n).sum ≤ r := by
  constructor
  · intro h
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
    let i := monoEquivOfFin (BoundedCode t r) (card_boundedCode t r) j
    refine ⟨i.val.isLt, ?_⟩
    change (digits t i.val.val).sum ≤ r
    rw [digits_sum_card]
    exact i.property
  · rintro ⟨hn, hw⟩
    let i : BoundedCode t r := ⟨⟨n, hn⟩, by simpa only [← digits_sum_card] using hw⟩
    let j := (monoEquivOfFin (BoundedCode t r) (card_boundedCode t r)).symm i
    apply List.mem_ofFn.mpr
    refine ⟨j, ?_⟩
    simp [j, i]

/-- Equality pins down the exact production ordering, rather than just the set of masks. -/
theorem masks_eq_canonicalMasks (t r : ℕ) : masks t r = canonicalMasks t r := by
  have hp : (masks t r).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hq := canonicalMasks_pairwise t r
  have hperm : (masks t r).Perm (canonicalMasks t r) :=
    (List.perm_ext_iff_of_nodup hp.nodup hq.nodup).mpr fun n =>
      (mem_masks t r n).trans (mem_canonicalMasks t r n).symm
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => False.elim (Nat.lt_asymm hab hba)) hp hq hperm

@[simp] theorem masks_length (t r : ℕ) : (masks t r).length = dimension t r := by
  rw [masks_eq_canonicalMasks]
  simp [canonicalMasks]

theorem monomial_code (t r : ℕ) (j : Fin (dimension t r)) :
    (monoEquivOfFin (BoundedCode t r) (card_boundedCode t r) j).val.val =
      (subsetCodeEquiv t ((monomialEquiv t r).symm j).val).val := by
  simp [monomialEquiv, boundedCodeEquiv]

/-- Stored list lookup produces the code of the exact semantic coefficient position. -/
theorem masks_getD (t r : ℕ) (j : Fin (dimension t r)) :
    (masks t r).getD j.val 0 = (subsetCodeEquiv t ((monomialEquiv t r).symm j).val).val := by
  rw [masks_eq_canonicalMasks]
  simp only [canonicalMasks, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, j.isLt, dite_eq_left, Option.getD_some]
  exact monomial_code t r j

end PCP.Lang.BooleanMask
