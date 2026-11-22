/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanMaskOrder

/-!
# A stored language enumeration of the coefficient masks

The program scans consecutive natural codes, computes their support sizes with
the proved population-count loop, and stores precisely the permitted masks.
-/

namespace PCP.Lang.BooleanMask

open PCP.Algebraic BinaryPolynomialSelector

def countRegs : Fin 6 → Fin 36 := Fin.castLE (by decide)
def countLists : Fin 1 → Fin 2 := Fin.castLE (by decide)
def count36 : Stmt 36 2 := popcount.rename countRegs countLists

theorem count36_run (st : State 36 2) :
    (count36.run st).1.regs 2 = (digits (st.regs 0) (st.regs 1)).sum := by
  have h := congrArg (fun z : State 6 1 × ℕ => z.1.regs 2)
    (popcount.run_rename countRegs countLists (Fin.castLE_injective _) (Fin.castLE_injective _) st)
  exact h.trans (popcount_run _)

def countMask : Stmt 36 2 :=
  .seq (.assign 0 (.var 20)) (.seq (.assign 1 (.var 32)) count36)

theorem countMask_run (st : State 36 2) :
    (countMask.run st).1.regs 2 = (digits (st.regs 20) (st.regs 32)).sum := by
  simp only [countMask, run_seq_fst, run_assign_fst, Expr.eval]
  rw [count36_run]
  simp [Function.update]

def appendTail : Stmt 36 2 :=
  .seq (.assign 2 (.lt 2 22))
    (.seq (.ite 2 (.push 1 32) .skip) (.assign 32 (.add 32 35)))

theorem appendTail_step (st : State 36 2) (h35 : st.regs 35 = 1) :
    (appendTail.run st).1.lists 1 =
      (if st.regs 2 < st.regs 22 then st.regs 32 :: st.lists 1 else st.lists 1) ∧
    (appendTail.run st).1.regs 32 = st.regs 32 + 1 := by
  by_cases h : st.regs 2 < st.regs 22 <;>
    simp [appendTail, Stmt.run, Expr.eval, Function.update, h35, h]

def enumerationBody : Stmt 36 2 := .seq countMask appendTail

def EnumContext (t r q : ℕ) (st : State 36 2) : Prop :=
  st.regs 20 = t ∧ st.regs 21 = r ∧ st.regs 22 = r + 1 ∧
    st.regs 28 = q ∧ st.regs 35 = 1

theorem enumerationBody_step (t r q : ℕ) (st : State 36 2) (hc : EnumContext t r q st) :
    (enumerationBody.run st).1.lists 1 =
      (if (digits t (st.regs 32)).sum ≤ r then st.regs 32 :: st.lists 1 else st.lists 1) ∧
    (enumerationBody.run st).1.regs 32 = st.regs 32 + 1 := by
  have hs2 := countMask_run st
  rw [hc.1] at hs2
  have hs22 := run_regs_frame countMask 22 (by decide) st
  have hs32 := run_regs_frame countMask 32 (by decide) st
  have hs35 := run_regs_frame countMask 35 (by decide) st
  have hsl := run_lists_frame countMask 1 (by decide) st
  simp only [enumerationBody, run_seq_fst]
  generalize hs : (countMask.run st).1 = s at *
  have h := appendTail_step s (hs35.trans hc.2.2.2.2)
  simpa only [hs2, hs22, hs32, hsl, hc.2.2.1, Nat.lt_succ_iff] using h

theorem enumerationBody_frame (st : State 36 2) (r : Fin 36)
    (hr : r ∈ ([20, 21, 22, 28, 35] : List (Fin 36))) :
    (enumerationBody.run st).1.regs r = st.regs r := by
  apply run_regs_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem enumerationBody_context (t r q : ℕ) (st : State 36 2) (hc : EnumContext t r q st) :
    EnumContext t r q (enumerationBody.run st).1 := by
  unfold EnumContext at hc ⊢
  rw [enumerationBody_frame st 20 (by decide), enumerationBody_frame st 21 (by decide),
    enumerationBody_frame st 22 (by decide), enumerationBody_frame st 28 (by decide),
    enumerationBody_frame st 35 (by decide)]
  exact hc

def masksBelow (t r n : ℕ) : List ℕ :=
  (List.range n).filter fun j => decide ((digits t j).sum ≤ r)

theorem enumerationBody_inv (t r q n : ℕ) (st : State 36 2)
    (hc : EnumContext t r q st) (hi : st.regs 32 = n)
    (hl : st.lists 1 = (masksBelow t r n).reverse) :
    EnumContext t r q (enumerationBody.run st).1 ∧
      (enumerationBody.run st).1.regs 32 = n + 1 ∧
      (enumerationBody.run st).1.lists 1 = (masksBelow t r (n + 1)).reverse := by
  have hs := enumerationBody_step t r q st hc
  refine ⟨enumerationBody_context t r q st hc, hs.2.trans (by rw [hi]), ?_⟩
  rw [hs.1, hi, hl]
  by_cases hp : (digits t n).sum ≤ r <;>
    simp [masksBelow, List.range_succ, List.filter_append, hp]

/-- The field-size bound `28` is supplied; list `0` is an empty reusable source. -/
def gatherMasks : Stmt 36 2 :=
  .seq (.copy 0 1) (.seq (.assign 35 (.const 1)) (.seq (.assign 22 (.add 21 35))
    (.seq (.assign 32 (.const 0)) (.seq (.loop 28 enumerationBody) (.rev 1)))))

theorem gatherMasks_run (t r : ℕ) (st : State 36 2)
    (h20 : st.regs 20 = t) (h21 : st.regs 21 = r) (h28 : st.regs 28 = 2 ^ t)
    (he : st.lists 0 = []) :
    (gatherMasks.run st).1.lists 1 = masks t r := by
  let q := 2 ^ t
  let s := setReg (setReg (setReg (setList st 1 []) 35 1) 22 (r + 1)) 32 0
  have hit := iterate_inv enumerationBody.run (Nat.size q + 1) q
    (fun n u => EnumContext t r q u ∧ u.regs 32 = n ∧
      u.lists 1 = (masksBelow t r n).reverse)
    (fun n u _ hu => enumerationBody_inv t r q n u hu.1 hu.2.1 hu.2.2) s
    (by simp [EnumContext, s, Function.update, h20, h21, h28, q, masksBelow])
  have hout := hit.2.2
  simp only [gatherMasks, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
    run_loop_fst, run_rev_fst, setReg_regs, setList_regs, setList_lists, Function.update,
    Fin.reduceEq, dite_true, dite_false, he, h21, h28]
  change ((iterate enumerationBody.run (Nat.size q + 1) q s).1.lists 1).reverse = _
  rw [hout, List.reverse_reverse]
  rfl

/-- Complete fixed-register enumeration, computing the mask-space size internally. -/
def enumerateMasks : Stmt 36 2 := .seq cardinality gatherMasks

theorem enumerateMasks_run (t r : ℕ) (st : State 36 2)
    (h20 : st.regs 20 = t) (h21 : st.regs 21 = r) (he : st.lists 0 = []) :
    (enumerateMasks.run st).1.lists 1 = masks t r := by
  have hs28 := cardinality_run st
  rw [h20] at hs28
  exact gatherMasks_run t r (cardinality.run st).1
    ((run_regs_frame cardinality 20 (by decide) st).trans h20)
    ((run_regs_frame cardinality 21 (by decide) st).trans h21) hs28
    ((run_lists_frame cardinality 0 (by decide) st).trans he)

end PCP.Lang.BooleanMask
