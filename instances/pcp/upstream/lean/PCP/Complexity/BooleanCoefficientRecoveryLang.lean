/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientRecoveryList

/-!
# A stored language subset transform

The program traverses the requested coefficient masks, evaluates the stored
truth table on each support, and materializes the resulting coefficient bits.
-/

namespace PCP.Lang.BooleanCoefficientRecoveryLang

open BooleanCoefficientList

def evalRegs : Fin 15 → Fin 16 := Fin.castLE (by decide)
def evalLists : Fin 4 → Fin 8 := Fin.castLE (by decide)
def eval16 : Stmt 16 8 := BooleanCoefficientEvaluation.evaluate.rename evalRegs evalLists

theorem eval16_run (st : State 16 8) :
    (eval16.run st).1.regs 10 =
      terms (st.regs 0) (st.regs 2) (st.lists 0) (st.lists 1) % 2 := by
  have h := congrArg (fun z : State 15 4 × ℕ => z.1.regs 10)
    (BooleanCoefficientEvaluation.evaluate.run_rename evalRegs evalLists
      (Fin.castLE_injective _) (Fin.castLE_injective _) st)
  exact h.trans (BooleanCoefficientEvaluation.evaluate_run _)

def popMask : Stmt 16 8 := .pop 6 2 12

theorem popMask_step (st : State 16 8) :
    (popMask.run st).1.regs 2 = (st.lists 6).headD 0 ∧
      (popMask.run st).1.lists 6 = (st.lists 6).tail := by
  cases h : st.lists 6 <;> simp [popMask, Stmt.run, h, Function.update]

def body : Stmt 16 8 := .seq popMask (.seq eval16 (.push 5 10))

theorem body_step (st : State 16 8) :
    (body.run st).1.lists 5 =
      terms (st.regs 0) ((st.lists 6).headD 0) (st.lists 0) (st.lists 1) % 2 :: st.lists 5 ∧
      (body.run st).1.lists 6 = (st.lists 6).tail := by
  have hp := popMask_step st
  have hp0 := run_regs_frame popMask 0 (by decide) st
  have hpl0 := run_lists_frame popMask 0 (by decide) st
  have hpl1 := run_lists_frame popMask 1 (by decide) st
  have hpl5 := run_lists_frame popMask 5 (by decide) st
  simp only [body, run_seq_fst, run_push_fst]
  generalize hps : (popMask.run st).1 = s at *
  have hs10 := eval16_run s
  have hsl5 := run_lists_frame eval16 5 (by decide) s
  have hsl6 := run_lists_frame eval16 6 (by decide) s
  simp only [setList_lists, Function.update, Fin.reduceEq, dite_true, dite_false,
    hs10, hsl5, hsl6, hp0, hp.1, hpl0, hpl1, hpl5, hp.2, and_self]

theorem body_width (st : State 16 8) : (body.run st).1.regs 0 = st.regs 0 :=
  run_regs_frame body 0 (by decide) st

theorem body_source (st : State 16 8) (L : Fin 8) (hL : L = 0 ∨ L = 1) :
    (body.run st).1.lists L = st.lists L := by
  apply run_lists_frame
  rcases hL with rfl | rfl <;> decide

theorem iterate_result (c : ℕ) (ms : List ℕ) (st : State 16 8) (hm : st.lists 6 = ms) :
    (iterate body.run c ms.length st).1.lists 5 =
      (ms.map fun m => terms (st.regs 0) m (st.lists 0) (st.lists 1) % 2).reverse ++
        st.lists 5 := by
  induction ms generalizing st with
  | nil => simp [iterate]
  | cons m ms ih =>
    have hh := body_step st
    rw [hm] at hh
    simp only [List.length_cons, iterate_succ_fst]
    rw [ih _ (by simpa using hh.2), body_width,
      body_source _ 0 (Or.inl rfl), body_source _ 1 (Or.inr rfl), hh.1]
    simp [List.reverse_cons, List.append_assoc]

/-- Sources: all masks `0`, truth-table bits `1`, requested masks `4`, empty `7`.
The width is register `0` and the materialized output coefficient word is list `5`. -/
def recover : Stmt 16 8 :=
  .seq (.copy 4 6) (.seq (.copy 7 5) (.seq (.len 6 15)
    (.seq (.loop 15 body) (.rev 5))))

theorem recover_run (st : State 16 8) (he : st.lists 7 = []) :
    (recover.run st).1.lists 5 =
      (st.lists 4).map fun m => terms (st.regs 0) m (st.lists 0) (st.lists 1) % 2 := by
  let s := setReg (setList (setList st 6 (st.lists 4)) 5 []) 15 (st.lists 4).length
  have hi := iterate_result (Nat.size (st.lists 4).length + 1) (st.lists 4) s
    (by simp [s, Function.update])
  simp only [recover, run_seq_fst, run_copy_fst, run_len_fst, run_loop_fst, run_rev_fst,
    setReg_regs, setList_lists, setList_regs, Function.update, Fin.reduceEq,
    dite_true, dite_false, he]
  change ((iterate body.run (Nat.size (st.lists 4).length + 1)
    (st.lists 4).length s).1.lists 5).reverse = _
  rw [hi]
  simp [s, Function.update]

/-- Exactness for the actual bounded coefficient-recovery transform. -/
theorem recover_coefficients {t r : ℕ} (f : (Fin t → ZMod 2) → ZMod 2)
    (st : State 16 8) (ht : st.regs 0 = t) (hall : st.lists 0 = fullMasks t)
    (hv : st.lists 1 = table t f) (hm : st.lists 4 = BooleanMask.masks t r)
    (he : st.lists 7 = []) :
    (recover.run st).1.lists 5 =
      encode (PCP.Algebraic.BooleanCoefficientRecovery.recover f :
        PCP.Algebraic.BinaryPolynomialSpace.Coefficients t r) := by
  rw [recover_run st he, ht, hall, hv, hm]
  exact recoverBits_eq f

end PCP.Lang.BooleanCoefficientRecoveryLang
