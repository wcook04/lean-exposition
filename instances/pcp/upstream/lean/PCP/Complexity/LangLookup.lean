/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.LangRenaming
import PCP.Complexity.LangCost

/-!
# Bounded lookup in a stored list

The index is in register zero, the source in list zero, and the answer is returned
in register one. An out-of-range index returns zero immediately. Thus a huge
binary index cannot cause a loop of exponentially many iterations. The source
list and index are preserved; the routine has a quadratic charged-cost bound.
-/

namespace PCP.Lang.Lookup

def pop : Stmt 4 2 := .pop 1 1 2

def body : Stmt 4 2 :=
  .seq (.copy 0 1) (.seq (.loop 0 pop) pop)

def lookup : Stmt 4 2 :=
  .seq (.len 0 3) (.seq (.assign 2 (.lt 0 3)) (.ite 2 body (.assign 1 (.const 0))))

theorem pop_tail (st : State 4 2) : (pop.run st).1.lists 1 = (st.lists 1).tail := by
  cases hl : st.lists 1 <;> simp [pop, Stmt.run, hl, Function.update]

theorem pop_head (st : State 4 2) : (pop.run st).1.regs 1 = (st.lists 1).headD 0 := by
  cases hl : st.lists 1 <;> simp [pop, Stmt.run, hl, Function.update]

theorem pop_iterate (c n : ℕ) (st : State 4 2) :
    (iterate pop.run c n st).1.lists 1 = (st.lists 1).drop n := by
  induction n generalizing st with
  | zero => simp [iterate]
  | succ n ih =>
    rw [iterate_succ_fst, ih, pop_tail]
    rw [← List.drop_one, List.drop_drop]
    simp [Nat.add_comm]

theorem body_run (st : State 4 2) :
    (body.run st).1.regs 1 = (st.lists 0).getD (st.regs 0) 0 := by
  simp only [body, run_seq_fst, pop_head, run_loop_fst, pop_iterate,
    run_copy_fst, setList_regs, setList_lists, Function.update_self]
  simp [List.getD_eq_getElem?_getD]

/-- The stored lookup is total and returns precisely `List.getD` with zero padding. -/
theorem lookup_run (st : State 4 2) :
    (lookup.run st).1.regs 1 = (st.lists 0).getD (st.regs 0) 0 := by
  simp only [lookup, run_seq_fst, run_len_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_self]
  rw [run_ite_fst]
  by_cases hi : st.regs 0 < (st.lists 0).length
  · simp [Function.update, hi, body_run]
  · simp [Function.update, hi, Stmt.run, Expr.eval, List.getD_eq_getElem?_getD]

theorem lookup_preserves_source (st : State 4 2) : (lookup.run st).1.lists 0 = st.lists 0 :=
  run_lists_frame lookup 0 (by decide) st

theorem lookup_preserves_index (st : State 4 2) : (lookup.run st).1.regs 0 = st.regs 0 :=
  run_regs_frame lookup 0 (by decide) st

theorem pop_size (st : State 4 2) : listSize ((pop.run st).1.lists 1) ≤ listSize (st.lists 1) := by
  rw [pop_tail]
  cases st.lists 1 <;> simp [listSize]

theorem pop_cost (st : State 4 2) : (pop.run st).2 ≤ listSize (st.lists 1) + 1 := by
  cases hl : st.lists 1 with
  | nil => simp [pop, Stmt.run, hl]
  | cons v l =>
    simp only [pop, Stmt.run, hl, listSize, List.map_cons, List.sum_cons]
    omega

theorem body_cost (st : State 4 2) (hi : st.regs 0 ≤ (st.lists 0).length) :
    (body.run st).2 ≤ 6 * (listSize (st.lists 0) + 1) ^ 2 := by
  let S := listSize (st.lists 0)
  let next := setList st 1 (st.lists 0)
  have hsize : listSize (next.lists 1) ≤ S := by simp [next, S]
  have hiter := iterate_cost_le pop.run (Nat.size (st.regs 0) + 1) (S + 1)
    (fun s => listSize (s.lists 1) ≤ S)
    (fun s hs => (pop_size s).trans hs)
    (fun s hs => (pop_cost s).trans (Nat.add_le_add_right hs 1)) (st.regs 0) next hsize
  have hframe := iterate_frame pop.run (Nat.size (st.regs 0) + 1)
    (fun s => listSize (s.lists 1) ≤ S) (fun s hs => (pop_size s).trans hs)
    (st.regs 0) next hsize
  have hfinal := pop_cost (iterate pop.run (Nat.size (st.regs 0) + 1) (st.regs 0) next).1
  have hidx : st.regs 0 ≤ S := hi.trans (length_le_listSize _)
  have hidxSize : Nat.size (st.regs 0) ≤ S := (size_le_self _).trans hidx
  have hm := Nat.mul_le_mul hidx (show Nat.size (st.regs 0) + 1 + (S + 1) ≤ 2 * S + 2 by omega)
  simp only [body, run_seq_snd, run_copy_snd, run_copy_fst, run_loop_snd, run_loop_fst,
    setList_regs]
  change S + 1 + ((iterate pop.run (Nat.size (st.regs 0) + 1) (st.regs 0) next).2 +
    Nat.size (st.regs 0) + 1 +
    (pop.run (iterate pop.run (Nat.size (st.regs 0) + 1) (st.regs 0) next).1).2 + 1) + 1 ≤ _
  nlinarith

/-- The cost depends polynomially on stored data size and the binary length of the index. -/
theorem lookup_cost (st : State 4 2) :
    (lookup.run st).2 ≤ 20 * (listSize (st.lists 0) + Nat.size (st.regs 0) + 1) ^ 2 := by
  let S := listSize (st.lists 0)
  have hlen : Nat.size (st.lists 0).length ≤ S :=
    (size_le_self _).trans (length_le_listSize _)
  let next := setReg (setReg st 3 (st.lists 0).length) 2
    (if st.regs 0 < (st.lists 0).length then 1 else 0)
  by_cases hi : st.regs 0 < (st.lists 0).length
  · have hb := body_cost next (by simpa [next, Function.update] using hi.le)
    simp only [next, setReg_lists, ite_eq_left hi] at hb
    simp [lookup, Stmt.run, Expr.eval, Expr.cost, Expr.readSize, Function.update, hi]
    nlinarith
  · simp [lookup, Stmt.run, Expr.eval, Expr.cost, Expr.readSize, Function.update, hi]
    nlinarith

end PCP.Lang.Lookup
