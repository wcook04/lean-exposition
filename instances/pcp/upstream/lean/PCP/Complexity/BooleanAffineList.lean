/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanLabelAddition

/-!
# Stored affine labels

Increasing numeric mask order puts the constant first, followed by the coordinate
singletons. Homogeneous labels are therefore a zero followed by their stored bits.
-/

namespace PCP.Lang.BooleanAffineList

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientIndex
open BooleanCoefficientArithmetic

variable {t : ℕ}

theorem subsetCode_empty (t : ℕ) : (subsetCodeEquiv t ∅).val = 0 := by
  simp [subsetCodeEquiv, maskEquiv, mask]

theorem subsetCode_singleton (i : Fin t) : (subsetCodeEquiv t {i}).val = 2 ^ i.val := by
  have hm : mask {i} = Pi.single i (1 : Fin 2) := by
    funext j
    simp [mask, Pi.single_apply, eq_comm]
  change (finFunctionFinEquiv (mask {i})).val = _
  rw [hm, finFunctionFinEquiv_single]
  simp

def affineMasks (t : ℕ) : List ℕ := 0 :: List.ofFn fun i : Fin t => 2 ^ i.val

theorem affineMasks_pairwise (t : ℕ) : (affineMasks t).Pairwise (· < ·) := by
  refine List.pairwise_cons.mpr ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
    positivity
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    exact Nat.pow_lt_pow_right (by decide) hij

theorem mem_affineMasks (t n : ℕ) :
    n ∈ affineMasks t ↔ n ∈ BooleanMask.masks t 1 := by
  rw [BooleanMask.mem_masks]
  constructor
  · intro hn
    simp only [affineMasks, List.mem_cons, List.mem_ofFn] at hn
    rcases hn with rfl | ⟨i, rfl⟩
    · refine ⟨by positivity, ?_⟩
      have h := BooleanMask.digits_sum_card t (subsetCodeEquiv t ∅)
      rw [subsetCode_empty, Equiv.symm_apply_apply] at h
      simp [h]
    · refine ⟨Nat.pow_lt_pow_right (by decide) i.isLt, ?_⟩
      have h := BooleanMask.digits_sum_card t (subsetCodeEquiv t {i})
      rw [subsetCode_singleton, Equiv.symm_apply_apply] at h
      simp [h]
  · rintro ⟨hn, hc⟩
    let s := (subsetCodeEquiv t).symm ⟨n, hn⟩
    have hs : s.card ≤ 1 := by
      change ((subsetCodeEquiv t).symm (⟨n, hn⟩ : Fin (2 ^ t))).card ≤ 1
      rw [← BooleanMask.digits_sum_card]
      exact hc
    have he : (subsetCodeEquiv t s).val = n := by simp [s]
    by_cases hz : s.card = 0
    · rw [Finset.card_eq_zero.mp hz, subsetCode_empty] at he
      simp [affineMasks, ← he]
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by omega : s.card = 1)
      rw [hi, subsetCode_singleton] at he
      simp only [affineMasks, List.mem_cons, List.mem_ofFn]
      exact Or.inr ⟨i, he⟩

theorem masks_one (t : ℕ) : BooleanMask.masks t 1 = affineMasks t := by
  have hp := BooleanMask.canonicalMasks_pairwise t 1
  rw [← BooleanMask.masks_eq_canonicalMasks] at hp
  have hq := affineMasks_pairwise t
  have he : (BooleanMask.masks t 1).Perm (affineMasks t) :=
    (List.perm_ext_iff_of_nodup hp.nodup hq.nodup).mpr fun n => (mem_affineMasks t n).symm
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => False.elim (Nat.lt_asymm hab hba)) hp hq he

theorem monomial_zero (j : Fin (dimension t 1)) (hj : j.val = 0) :
    ((monomialEquiv t 1).symm j).val = ∅ := by
  apply (subsetCodeEquiv t).injective
  apply Fin.ext
  rw [subsetCode_empty, ← BooleanMask.masks_getD, masks_one, hj]
  rfl

theorem monomial_succ (j : Fin (dimension t 1)) (i : Fin t) (hj : j.val = i.val + 1) :
    ((monomialEquiv t 1).symm j).val = {i} := by
  apply (subsetCodeEquiv t).injective
  apply Fin.ext
  rw [subsetCode_singleton, ← BooleanMask.masks_getD, masks_one, hj]
  simp [affineMasks, List.getD_eq_getElem?_getD]

theorem homogeneous_empty (w : Fin t → ZMod 2) (s : Monomials t 1) (hs : s.val = ∅) :
    homogeneousIndex (by decide : 1 ≤ 1) w s = 0 := by
  unfold homogeneousIndex
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, w i * (if s.val = {i} then 1 else 0)) = 0
  simp [hs]

theorem homogeneous_singleton (w : Fin t → ZMod 2) (s : Monomials t 1)
    (i : Fin t) (hs : s.val = {i}) :
    homogeneousIndex (by decide : 1 ≤ 1) w s = w i := by
  unfold homogeneousIndex
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ j, w j * (if s.val = {j} then 1 else 0)) = w i
  simp [hs]

/-- The semantic affine label has a directly materializable coefficient list. -/
theorem encode_homogeneous (w : Fin t → ZMod 2) :
    BooleanCoefficientList.encode (homogeneousIndex (by decide : 1 ≤ 1) w) =
      0 :: List.ofFn (fun i => (w i).val) := by
  apply List.ext_getElem
  · simp [dimension_one, Nat.add_comm]
  · intro n hn hn'
    simp only [BooleanCoefficientList.encode, List.getElem_ofFn, wordEquiv_apply]
    cases n with
    | zero =>
      rw [homogeneous_empty w _ (monomial_zero _ rfl)]
      rfl
    | succ n =>
      have hnt : n < t := by simpa using hn'
      rw [homogeneous_singleton w _ ⟨n, hnt⟩ (monomial_succ _ _ rfl)]
      simp

/-- Prefix a zero coefficient to a stored homogeneous binary label. -/
def homogeneous : Stmt 1 2 :=
  .seq (.copy 0 1) (.seq (.assign 0 (.const 0)) (.push 1 0))

theorem homogeneous_run (w : Fin t → ZMod 2) (st : State 1 2)
    (hw : st.lists 0 = List.ofFn (fun i => (w i).val)) :
    (homogeneous.run st).1.lists 1 =
      BooleanCoefficientList.encode (homogeneousIndex (by decide : 1 ≤ 1) w) := by
  rw [encode_homogeneous]
  simp [homogeneous, Stmt.run, Expr.eval, Function.update, hw]

theorem homogeneous_source (st : State 1 2) :
    (homogeneous.run st).1.lists 0 = st.lists 0 :=
  run_lists_frame homogeneous 0 (by decide) st

theorem homogeneous_cost (w : Fin t → ZMod 2) (st : State 1 2)
    (hw : st.lists 0 = List.ofFn (fun i => (w i).val)) :
    (homogeneous.run st).2 ≤ 2 * t + 5 := by
  have hb : BinaryField.Bits (List.ofFn (fun i => (w i).val)) := by
    intro n hn
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
    exact ZMod.val_lt _
  have hs := BinaryField.listSize_bits hb
  simp only [List.length_ofFn] at hs
  simpa [homogeneous, Stmt.run, Expr.cost, Expr.readSize, Expr.eval, Function.update, hw]
    using hs

end PCP.Lang.BooleanAffineList
