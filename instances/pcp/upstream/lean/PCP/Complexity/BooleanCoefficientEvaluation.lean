/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientList

/-!
# A stored language kernel for Boolean polynomial evaluation

The kernel traverses coefficient and mask lists together, tests support
containment, and accumulates coefficients in a natural register before taking
parity. The two source lists are preserved.
-/

namespace PCP.Lang.BooleanCoefficientEvaluation

open BooleanLoops BooleanCoefficientList

def subsetRegs : Fin 10 → Fin 15 := Fin.castLE (by decide)
def subsetLists : Fin 1 → Fin 4 := Fin.castLE (by decide)
def subset15 : Stmt 15 4 := BooleanMaskSubset.subset.rename subsetRegs subsetLists

theorem subset15_run (st : State 15 4) :
    (subset15.run st).1.regs 3 =
      truth (BooleanMaskSubset.Contains (st.regs 0) (st.regs 1) (st.regs 2)) := by
  have h := congrArg (fun z : State 10 1 × ℕ => z.1.regs 3)
    (BooleanMaskSubset.subset.run_rename subsetRegs subsetLists
      (Fin.castLE_injective _) (Fin.castLE_injective _) st)
  exact h.trans (BooleanMaskSubset.subset_run _)

def popInputs : Stmt 15 4 := .seq (.pop 2 1 12) (.pop 3 11 12)

theorem popInputs_step (st : State 15 4) :
    (popInputs.run st).1.regs 1 = (st.lists 2).headD 0 ∧
      (popInputs.run st).1.regs 11 = (st.lists 3).headD 0 ∧
      (popInputs.run st).1.lists 2 = (st.lists 2).tail ∧
      (popInputs.run st).1.lists 3 = (st.lists 3).tail := by
  cases hm : st.lists 2 <;> cases hc : st.lists 3 <;>
    simp [popInputs, Stmt.run, hm, hc, Function.update]

def addTerm : Stmt 15 4 := .seq (.assign 11 (.mul 11 3)) (.assign 10 (.add 10 11))

theorem addTerm_run (st : State 15 4) :
    (addTerm.run st).1.regs 10 = st.regs 10 + st.regs 11 * st.regs 3 := by
  simp [addTerm, Stmt.run, Expr.eval, Function.update]

def body : Stmt 15 4 := .seq popInputs (.seq subset15 addTerm)

theorem body_step (st : State 15 4) :
    (body.run st).1.regs 10 = st.regs 10 + (st.lists 3).headD 0 *
      truth (BooleanMaskSubset.Contains (st.regs 0) ((st.lists 2).headD 0) (st.regs 2)) ∧
      (body.run st).1.lists 2 = (st.lists 2).tail ∧
      (body.run st).1.lists 3 = (st.lists 3).tail := by
  have hp := popInputs_step st
  have hp0 := run_regs_frame popInputs 0 (by decide) st
  have hp2 := run_regs_frame popInputs 2 (by decide) st
  have hp10 := run_regs_frame popInputs 10 (by decide) st
  simp only [body, run_seq_fst]
  generalize hps : (popInputs.run st).1 = s at *
  have hs3 := subset15_run s
  have hs10 := run_regs_frame subset15 10 (by decide) s
  have hs11 := run_regs_frame subset15 11 (by decide) s
  have hs2 := run_lists_frame subset15 2 (by decide) s
  have hs4 := run_lists_frame subset15 3 (by decide) s
  generalize hss : (subset15.run s).1 = u at *
  refine ⟨?_, ?_, ?_⟩
  · rw [addTerm_run, hs10, hs11, hs3, hp10, hp.1, hp.2.1, hp0, hp2]
  · exact (run_lists_frame addTerm 2 (by decide) u).trans (hs2.trans hp.2.2.1)
  · exact (run_lists_frame addTerm 3 (by decide) u).trans (hs4.trans hp.2.2.2)

theorem body_width (st : State 15 4) : (body.run st).1.regs 0 = st.regs 0 :=
  run_regs_frame body 0 (by decide) st

theorem body_point (st : State 15 4) : (body.run st).1.regs 2 = st.regs 2 :=
  run_regs_frame body 2 (by decide) st

theorem iterate_result (c : ℕ) (ms cs : List ℕ) (st : State 15 4)
    (hm : st.lists 2 = ms) (hc : st.lists 3 = cs) :
    (iterate body.run c ms.length st).1.regs 10 =
      st.regs 10 + terms (st.regs 0) (st.regs 2) ms cs := by
  induction ms generalizing cs st with
  | nil => simp [iterate, terms]
  | cons m ms ih =>
    have hs := body_step st
    rw [hm, hc] at hs
    simp only [List.length_cons, iterate_succ_fst]
    rw [ih cs.tail (body.run st).1 (by simpa using hs.2.1) hs.2.2,
      hs.1, body_width, body_point]
    simp only [List.headD_cons, terms, Nat.add_assoc]
    rfl

/-- Inputs: width `0`, point code `2`, masks list `0`, coefficient bits list `1`.
The result bit is in register `10`; the two source lists are preserved. -/
def evaluate : Stmt 15 4 :=
  .seq (.copy 0 2) (.seq (.copy 1 3) (.seq (.len 2 14)
    (.seq (.assign 10 (.const 0)) (.seq (.assign 13 (.const 2))
      (.seq (.loop 14 body) (.assign 10 (.mod 10 13)))))))

theorem evaluate_run (st : State 15 4) :
    (evaluate.run st).1.regs 10 =
      terms (st.regs 0) (st.regs 2) (st.lists 0) (st.lists 1) % 2 := by
  let s := setReg (setReg (setReg (setList (setList st 2 (st.lists 0)) 3 (st.lists 1))
    14 (st.lists 0).length) 10 0) 13 2
  have hi := iterate_result (Nat.size (st.lists 0).length + 1) (st.lists 0) (st.lists 1)
    s (by simp [s, Function.update]) (by simp [s])
  have h13 := iterate_inv body.run (Nat.size (st.lists 0).length + 1) (st.lists 0).length
    (fun _ u => u.regs 13 = 2)
    (fun _ u _ hu => (run_regs_frame body 13 (by decide) u).trans hu) s (by simp [s])
  simp only [evaluate, run_seq_fst, run_copy_fst, run_len_fst, run_assign_fst,
    Expr.eval, run_loop_fst, setReg_regs, setList_regs, setList_lists, Function.update,
    Fin.reduceEq, dite_true, dite_false]
  change (iterate body.run (Nat.size (st.lists 0).length + 1) (st.lists 0).length s).1.regs 10 %
    (iterate body.run (Nat.size (st.lists 0).length + 1) (st.lists 0).length s).1.regs 13 = _
  rw [hi, h13]
  simp [s, Function.update]

/-- The actual kernel evaluates the actual production coefficient word. -/
theorem evaluate_coefficients {t r : ℕ}
    (p : PCP.Algebraic.BinaryPolynomialSpace.Coefficients t r) (x : Fin (2 ^ t))
    (st : State 15 4) (ht : st.regs 0 = t) (hx : st.regs 2 = x.val)
    (hm : st.lists 0 = BooleanMask.masks t r) (hp : st.lists 1 = encode p) :
    (evaluate.run st).1.regs 10 =
      (PCP.Algebraic.BooleanCoefficientArithmetic.evaluate (point t x) p).val := by
  rw [evaluate_run, ht, hx, hm, hp, terms_mod_eq]

end PCP.Lang.BooleanCoefficientEvaluation
