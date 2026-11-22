/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanLabelKernelCost

/-!
# Truth tables for Boolean label products and embeddings

A fixed counted-loop program enumerates numeric Boolean points and stores one
computed observation at each point. Both coefficient source arrays are preserved.
-/

namespace PCP.Lang.BooleanLabelTable

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList
open BooleanLabelKernel

variable {t a b : ℕ}

def value (product : Bool) (p : Coefficients t a) (q : Coefficients t b) (j : ℕ) : ℕ :=
  if hj : j < 2 ^ t then (function product p q (point t ⟨j, hj⟩)).val else 0

theorem value_lt_two (product : Bool) (p : Coefficients t a) (q : Coefficients t b) (j : ℕ) :
    value product p q j < 2 := by
  unfold value
  split_ifs
  · exact ZMod.val_lt _
  · decide

def Context (p : Coefficients t a) (q : Coefficients t b) (st : State 57 20) : Prop :=
  BooleanLabelKernel.Context p q st ∧ st.regs 52 = 2 ^ t ∧ st.regs 53 = 1 ∧ st.lists 7 = []

def body (product : Bool) : Stmt 57 20 :=
  .seq (kernel product) (.seq (.push 16 46) (.assign 24 (.add 24 53)))

theorem body_step (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (st : State 57 20) (hc : Context p q st) (hj : st.regs 24 < 2 ^ t) :
    ((body product).run st).1.regs 24 = st.regs 24 + 1 ∧
      ((body product).run st).1.lists 16 = value product p q (st.regs 24) :: st.lists 16 := by
  have hr := kernel_run product p q ⟨st.regs 24, hj⟩ st hc.1 rfl
  have hs24 := kernel_reg product st 24 (by decide)
  have hs53 := kernel_reg product st 53 (by decide)
  have hs16 := kernel_list product st 16 (by decide)
  simp only [body, run_seq_fst]
  generalize hs : ((kernel product).run st).1 = s at *
  simp [run_push_fst, run_assign_fst, Expr.eval, Function.update, hr,
    hs24, hs53, hc.2.2.1, hs16, value, hj]

theorem body_context (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (st : State 57 20) (hc : Context p q st) : Context p q ((body product).run st).1 := by
  have h20 := run_regs_frame (body product) 20 (by cases product <;> decide) st
  have h52 := run_regs_frame (body product) 52 (by cases product <;> decide) st
  have h53 := run_regs_frame (body product) 53 (by cases product <;> decide) st
  have h7 := run_lists_frame (body product) 7 (by cases product <;> decide) st
  have h12 := run_lists_frame (body product) 12 (by cases product <;> decide) st
  have h13 := run_lists_frame (body product) 13 (by cases product <;> decide) st
  have h19 := run_lists_frame (body product) 19 (by cases product <;> decide) st
  have h18 := run_lists_frame (body product) 18 (by cases product <;> decide) st
  unfold Context BooleanLabelKernel.Context at hc ⊢
  rw [h20, h52, h53, h7, h12, h13, h19, h18]
  exact hc

def tabulate (product : Bool) : Stmt 57 20 :=
  .seq (.copy 7 16) (.seq (.assign 24 (.const 0))
    (.seq (.loop 52 (body product)) (.rev 16)))

theorem tabulate_run (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (st : State 57 20) (hc : Context p q st) :
    ((tabulate product).run st).1.lists 16 = (List.range (2 ^ t)).map (value product p q) := by
  let N := 2 ^ t
  let s := setReg (setList st 16 []) 24 0
  have hinit : Context p q s ∧ s.regs 24 = 0 ∧
      s.lists 16 = ((List.range 0).map (value product p q)).reverse := by
    simp [Context, BooleanLabelKernel.Context, s, Function.update,
      hc.1.1, hc.1.2.1, hc.1.2.2.1, hc.1.2.2.2.1, hc.1.2.2.2.2,
      hc.2.1, hc.2.2.1, hc.2.2.2]
  have hout := iterate_inv (body product).run (Nat.size N + 1) N
    (fun j u => Context p q u ∧ u.regs 24 = j ∧
      u.lists 16 = ((List.range j).map (value product p q)).reverse)
    (by
      intro j u hj hu
      have hh := body_step product p q u hu.1 (by rw [hu.2.1]; exact hj)
      refine ⟨body_context product p q u hu.1, hh.1.trans (by rw [hu.2.1]), ?_⟩
      rw [hh.2, hu.2.1, hu.2.2]
      simp [List.range_succ]) s hinit
  simp only [tabulate, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
    run_loop_fst, run_rev_fst, setReg_regs, setList_regs, Function.update,
    Fin.reduceEq, dite_false, hc.2.1, hc.2.2.2]
  change ((iterate (body product).run (Nat.size N + 1) N s).1.lists 16).reverse = _
  rw [hout.2.2, List.reverse_reverse]

theorem range_values (product : Bool) (p : Coefficients t a) (q : Coefficients t b) :
    (List.range (2 ^ t)).map (value product p q) = table t (function product p q) := by
  rw [← BooleanCoefficientTransform.fullMasks_range]
  simp only [fullMasks, List.map_ofFn, table]
  apply congrArg List.ofFn
  funext i
  simp [value, i.isLt]

theorem tabulate_table (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (st : State 57 20) (hc : Context p q st) :
    ((tabulate product).run st).1.lists 16 = table t (function product p q) :=
  (tabulate_run product p q st hc).trans (range_values product p q)

end PCP.Lang.BooleanLabelTable
