/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.BinaryPolynomialSpace
import Mathlib.Data.Fintype.Sort
import Mathlib.Algebra.BigOperators.Fin

/-!
# Computable indexing of bounded Boolean coefficient vectors

A squarefree monomial is first encoded by its characteristic bit mask. The
numeric masks of weight at most `r` are sorted in increasing order to obtain a
dense index. Coefficient vectors then become explicit binary words and integer
indices by base-two expansion.

All indexing definitions are computable, uniformly in `t` and `r`; none uses
`Fintype.equivFin`, `equivOfCardEq`, or a choice of enumeration. This file proves
the codec identities. The production verifier's affine and cubic codecs use this
same order, and their concrete implementation is covered by
`PCP.Lang.ThreeColorRuntime.polyTimeAlg`.
-/

namespace PCP.Algebraic.BooleanCoefficientIndex

open Finset BinaryPolynomialSpace

/-- The characteristic bit vector of a subset. -/
def mask {t : ℕ} (s : Finset (Fin t)) : Fin t → Fin 2 :=
  fun i => if i ∈ s then 1 else 0

/-- Read a subset from exactly the positions carrying a one bit. -/
def unmask {t : ℕ} (v : Fin t → Fin 2) : Finset (Fin t) :=
  univ.filter (fun i => v i = 1)

@[simp] theorem unmask_mask {t : ℕ} (s : Finset (Fin t)) : unmask (mask s) = s := by
  ext i
  simp [unmask, mask]

@[simp] theorem mask_unmask {t : ℕ} (v : Fin t → Fin 2) : mask (unmask v) = v := by
  funext i
  simp only [mask, unmask, mem_filter, mem_univ, true_and]
  generalize v i = b
  fin_cases b <;> rfl

/-- A computable characteristic-mask equivalence, including the empty coordinate set. -/
def maskEquiv (t : ℕ) : Finset (Fin t) ≃ (Fin t → Fin 2) where
  toFun := mask
  invFun := unmask
  left_inv := unmask_mask
  right_inv := mask_unmask

/-- Numeric subset codes use the explicit base-two finite-function equivalence. -/
def subsetCodeEquiv (t : ℕ) : Finset (Fin t) ≃ Fin (2 ^ t) :=
  (maskEquiv t).trans (@finFunctionFinEquiv 2 t)

/-- Valid numeric masks retain precisely the original total-degree restriction. -/
abbrev BoundedCode (t r : ℕ) :=
  {i : Fin (2 ^ t) // ((subsetCodeEquiv t).symm i).card ≤ r}

/-- Converting a bounded monomial to its mask preserves its exact degree condition. -/
def boundedCodeEquiv (t r : ℕ) : Monomials t r ≃ BoundedCode t r where
  toFun s := ⟨subsetCodeEquiv t s.1, by simpa using s.2⟩
  invFun i := ⟨(subsetCodeEquiv t).symm i.1, i.2⟩
  left_inv s := Subtype.ext ((subsetCodeEquiv t).symm_apply_apply s.1)
  right_inv i := Subtype.ext ((subsetCodeEquiv t).apply_symm_apply i.1)

/-- The exact number of stored squarefree coefficients. -/
def dimension (t r : ℕ) : ℕ := ∑ k ∈ range (r + 1), t.choose k

theorem card_boundedCode (t r : ℕ) : Fintype.card (BoundedCode t r) = dimension t r := by
  rw [← Fintype.card_congr (boundedCodeEquiv t r), card_monomials]
  rfl

/-- Rank valid masks by increasing numeric value; this fixes their enumeration canonically. -/
def monomialEquiv (t r : ℕ) : Monomials t r ≃ Fin (dimension t r) :=
  (boundedCodeEquiv t r).trans
    (monoEquivOfFin (BoundedCode t r) (card_boundedCode t r)).toEquiv.symm

/-- The dense coefficient word reads monomials in their increasing-mask order. -/
def wordEquiv (t r : ℕ) : Coefficients t r ≃ (Fin (dimension t r) → ZMod 2) :=
  Equiv.arrowCongr (monomialEquiv t r) (Equiv.refl (ZMod 2))

@[simp] theorem wordEquiv_apply {t r : ℕ} (c : Coefficients t r) (i : Fin (dimension t r)) :
    wordEquiv t r c i = c ((monomialEquiv t r).symm i) := rfl

/-- A complete coefficient vector has a computable dense integer index. -/
def coefficientEquiv (t r : ℕ) : Coefficients t r ≃ Fin (2 ^ dimension t r) :=
  (wordEquiv t r).trans
    ((Equiv.arrowCongr (Equiv.refl (Fin (dimension t r))) (ZMod.finEquiv 2).toEquiv.symm).trans
      (@finFunctionFinEquiv 2 (dimension t r)))

/-- Encode the actual coefficient function, not an arbitrary enumeration of its finite type. -/
def encode {t r : ℕ} (c : Coefficients t r) : Fin (2 ^ dimension t r) :=
  coefficientEquiv t r c

/-- Decode the integer's bits into exactly the bounded monomial coordinates. -/
def decode {t r : ℕ} (i : Fin (2 ^ dimension t r)) : Coefficients t r :=
  (coefficientEquiv t r).symm i

@[simp] theorem decode_encode {t r : ℕ} (c : Coefficients t r) : decode (encode c) = c :=
  (coefficientEquiv t r).symm_apply_apply c

@[simp] theorem encode_decode {t r : ℕ} (i : Fin (2 ^ dimension t r)) : encode (decode i) = i :=
  (coefficientEquiv t r).apply_symm_apply i

/-- The computable indexing has exactly the original coefficient-space cardinality. -/
theorem card_coefficients (t r : ℕ) :
    Fintype.card (Coefficients t r) = 2 ^ dimension t r := by
  rw [Fintype.card_congr (coefficientEquiv t r), Fintype.card_fin]

@[simp] theorem dimension_zero (t : ℕ) : dimension t 0 = 1 := by
  simp [dimension]

@[simp] theorem dimension_one (t : ℕ) : dimension t 1 = 1 + t := by
  simp [dimension, sum_range_succ]

@[simp] theorem dimension_three (t : ℕ) :
    dimension t 3 = 1 + t + t.choose 2 + t.choose 3 := by
  simp [dimension, sum_range_succ]

/-- The affine coefficient index has the exact expected bit dimension. -/
def affineEquiv (t : ℕ) : Coefficients t 1 ≃ Fin (2 ^ (1 + t)) :=
  (coefficientEquiv t 1).trans (finCongr (congrArg (2 ^ ·) (dimension_one t)))

/-- The cubic coefficient index includes the constant, linear, quadratic and cubic terms. -/
def cubicEquiv (t : ℕ) :
    Coefficients t 3 ≃ Fin (2 ^ (1 + t + t.choose 2 + t.choose 3)) :=
  (coefficientEquiv t 3).trans (finCongr (congrArg (2 ^ ·) (dimension_three t)))

end PCP.Algebraic.BooleanCoefficientIndex
