/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanLabelTableCost

/-!
# Complete stored degree embeddings and mixed coefficient products

The program constructs both source-mask arrays, evaluates the requested Boolean
function at every numeric point, and recovers its bounded coefficient word.
The semantic equalities cover arbitrary source and target degree bounds.
-/

namespace PCP.Lang.BooleanLabelTransform

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList
open BooleanLabelKernel BooleanLabelTable

variable {t a b r : ℕ}

def enumRegs : Fin 36 → Fin 57 := Fin.castLE (by decide)
def enumLists (right : Bool) : Fin 2 → Fin 20 :=
  if right then ![7, 19] else ![7, 12]

theorem enumLists_injective (right : Bool) : Function.Injective (enumLists right) := by
  cases right <;> decide

def degreeReg (right : Bool) : Fin 57 := if right then 55 else 54

def masks (right : Bool) : Stmt 57 20 :=
  .seq (.assign 21 (.var (degreeReg right)))
    (BooleanMask.enumerateMasks.rename enumRegs (enumLists right))

theorem masks_run (right : Bool) (st : State 57 20) (ht : st.regs 20 = t)
    (hd : st.regs (degreeReg right) = a) (he : st.lists 7 = []) :
    ((masks right).run st).1.lists (enumLists right 1) = BooleanMask.masks t a := by
  let s := setReg st 21 a
  have h := congrArg (fun z : State 36 2 × ℕ => z.1.lists 1)
    (BooleanMask.enumerateMasks.run_rename enumRegs (enumLists right)
      (Fin.castLE_injective _) (enumLists_injective right) s)
  have hh := h.trans (BooleanMask.enumerateMasks_run t a
    (s.restrict enumRegs (enumLists right))
    (by simpa [s, State.restrict, enumRegs, Function.update] using ht)
    (by simp [s, State.restrict, enumRegs])
    (by cases right <;> simpa [s, State.restrict, enumLists] using he))
  simp only [masks, run_seq_fst, run_assign_fst, Expr.eval, hd]
  exact hh

theorem masks_cardinality (right : Bool) (st : State 57 20) (ht : st.regs 20 = t) :
    ((masks right).run st).1.regs 28 = 2 ^ t := by
  let s := setReg st 21 (st.regs (degreeReg right))
  have h := congrArg (fun z : State 36 2 × ℕ => z.1.regs 28)
    (BooleanMask.enumerateMasks.run_rename enumRegs (enumLists right)
      (Fin.castLE_injective _) (enumLists_injective right) s)
  have hg := run_regs_frame BooleanMask.gatherMasks 28 (by decide)
    (BinaryPolynomialSelector.cardinality.run (s.restrict enumRegs (enumLists right))).1
  have hc := BinaryPolynomialSelector.cardinality_run (s.restrict enumRegs (enumLists right))
  have hh := h.trans (hg.trans hc)
  simp only [masks, run_seq_fst, run_assign_fst, Expr.eval]
  simpa only [State.restrict_regs, show enumRegs 28 = (28 : Fin 57) from rfl,
    show enumRegs 20 = (20 : Fin 57) from rfl, s, setReg_regs,
    Function.update_of_ne (by decide : (20 : Fin 57) ≠ 21), ht] using hh

def prepare : Stmt 57 20 :=
  .seq (masks false) (.seq (masks true)
    (.seq (.assign 52 (.var 28)) (.assign 53 (.const 1))))

theorem prepare_context (p : Coefficients t a) (q : Coefficients t b) (st : State 57 20)
    (ht : st.regs 20 = t) (ha : st.regs 54 = a) (hb : st.regs 55 = b)
    (he : st.lists 7 = []) (hp : st.lists 13 = encode p) (hq : st.lists 18 = encode q) :
    BooleanLabelTable.Context p q (prepare.run st).1 := by
  have hl := masks_run false st ht ha he
  have hs20 := run_regs_frame (masks false) 20 (by decide) st
  have hs55 := run_regs_frame (masks false) 55 (by decide) st
  have hs7 := run_lists_frame (masks false) 7 (by decide) st
  have hs13 := run_lists_frame (masks false) 13 (by decide) st
  have hs18 := run_lists_frame (masks false) 18 (by decide) st
  simp only [prepare, run_seq_fst]
  generalize hs : ((masks false).run st).1 = s at *
  have hr := masks_run true s (hs20.trans ht) (hs55.trans hb) (hs7.trans he)
  have hN := masks_cardinality true s (hs20.trans ht)
  have hu20 := run_regs_frame (masks true) 20 (by decide) s
  have hu7 := run_lists_frame (masks true) 7 (by decide) s
  have hu12 := run_lists_frame (masks true) 12 (by decide) s
  have hu13 := run_lists_frame (masks true) 13 (by decide) s
  have hu18 := run_lists_frame (masks true) 18 (by decide) s
  generalize hu : ((masks true).run s).1 = u at *
  simp only [show enumLists false 1 = (12 : Fin 20) from rfl] at hl
  simp only [show enumLists true 1 = (19 : Fin 20) from rfl] at hr
  simp [BooleanLabelTable.Context, BooleanLabelKernel.Context, run_assign_fst,
    Expr.eval, Function.update, hu20, hs20, ht, hu7, hs7, he, hu12, hl,
    hu13, hs13, hp, hu18, hs18, hq, hr, hN]

def transformLists : Fin 8 → Fin 20 := ![0, 16, 1, 2, 4, 5, 6, 7]

theorem transformLists_injective : Function.Injective transformLists := by decide

def recover : Stmt 57 20 :=
  BooleanCoefficientTransform.transform.rename enumRegs transformLists

theorem recover_run (f : (Fin t → ZMod 2) → ZMod 2) (st : State 57 20)
    (ht : st.regs 20 = t) (hr : st.regs 23 = r) (hv : st.lists 16 = table t f)
    (he : st.lists 7 = []) :
    (recover.run st).1.lists 5 =
      encode (BooleanCoefficientRecovery.recover f : Coefficients t r) := by
  have h := congrArg (fun z : State 36 8 × ℕ => z.1.lists 5)
    (BooleanCoefficientTransform.transform.run_rename enumRegs transformLists
      (Fin.castLE_injective _) transformLists_injective st)
  have hh := h.trans (BooleanCoefficientTransform.transform_run f
    (st.restrict enumRegs transformLists) ht hr hv he)
  unfold recover
  simpa only [State.restrict_lists, show transformLists 5 = (5 : Fin 20) from rfl] using hh

/-- Inputs are width `20`, source degrees `54,55`, target degree `56`, source
coefficient lists `13,18`, and empty `7`; output coefficients occupy list `5`. -/
def query (product : Bool) : Stmt 57 20 :=
  .seq prepare (.seq (tabulate product) (.seq (.assign 23 (.var 56)) recover))

theorem query_run (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (st : State 57 20) (ht : st.regs 20 = t) (ha : st.regs 54 = a)
    (hb : st.regs 55 = b) (hr : st.regs 56 = r) (he : st.lists 7 = [])
    (hp : st.lists 13 = encode p) (hq : st.lists 18 = encode q) :
    ((query product).run st).1.lists 5 =
      encode (BooleanCoefficientRecovery.recover (function product p q) : Coefficients t r) := by
  have hc := prepare_context p q st ht ha hb he hp hq
  have hs56 := run_regs_frame prepare 56 (by decide) st
  simp only [query, run_seq_fst]
  generalize hs : (prepare.run st).1 = s at *
  have htable := tabulate_table product p q s hc
  have hu20 := run_regs_frame (tabulate product) 20 (by cases product <;> decide) s
  have hu56 := run_regs_frame (tabulate product) 56 (by cases product <;> decide) s
  have hu7 := run_lists_frame (tabulate product) 7 (by cases product <;> decide) s
  generalize hu : ((tabulate product).run s).1 = u at *
  simp only [run_assign_fst, Expr.eval]
  apply recover_run
  · simpa [Function.update] using hu20.trans hc.1.1
  · simpa using hu56.trans (hs56.trans hr)
  · exact htable
  · exact hu7.trans hc.2.2.2

theorem query_product (h : a + b ≤ r) (p : Coefficients t a) (q : Coefficients t b)
    (st : State 57 20) (ht : st.regs 20 = t) (ha : st.regs 54 = a)
    (hb : st.regs 55 = b) (hr : st.regs 56 = r) (he : st.lists 7 = [])
    (hp : st.lists 13 = encode p) (hq : st.lists 18 = encode q) :
    ((query true).run st).1.lists 5 =
      encode (BooleanCoefficientArithmetic.mixedProduct h p q) := by
  rw [query_run true p q st ht ha hb hr he hp hq]
  have hf : function true p q = fun x => BooleanCoefficientArithmetic.evaluate x
      (BooleanCoefficientArithmetic.mixedProduct h p q) := by
    funext x
    simp only [function, ite_true, BooleanCoefficientArithmetic.evaluate_mixedProduct]
  rw [hf, BooleanCoefficientRecovery.recover_evaluate]

/-- Degree embedding uses the same evaluated function, with a saved duplicate source. -/
def embed : Stmt 57 20 :=
  .seq (.copy 13 18) (.seq (.assign 55 (.var 54)) (query false))

theorem embed_run (h : a ≤ r) (p : Coefficients t a) (st : State 57 20)
    (ht : st.regs 20 = t) (ha : st.regs 54 = a) (hr : st.regs 56 = r)
    (he : st.lists 7 = []) (hp : st.lists 13 = encode p) :
    (embed.run st).1.lists 5 = encode (BooleanCoefficientArithmetic.embed h p) := by
  let s := setReg (setList st 18 (st.lists 13)) 55 (st.regs 54)
  have hh := query_run false p p s
    (by simpa [s, Function.update] using ht) (by simpa [s, Function.update] using ha)
    (by simpa [s] using ha) (by simpa [s, Function.update] using hr)
    (by simpa [s, Function.update] using he) (by simpa [s, Function.update] using hp)
    (by simpa [s] using hp)
  have hf : function false p p = fun x =>
      BooleanCoefficientArithmetic.evaluate x (BooleanCoefficientArithmetic.embed h p) := by
    funext x
    simp only [function, Bool.false_eq_true, ite_false, BooleanCoefficientArithmetic.evaluate_embed]
  rw [hf, BooleanCoefficientRecovery.recover_evaluate] at hh
  dsimp only [s] at hh
  simp only [embed, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval, setList_regs]
  generalize hu : ((query false).run
    (setReg (setList st 18 (st.lists 13)) 55 (st.regs 54))).1 = u at *
  exact hh

theorem query_frame (product : Bool) (st : State 57 20) :
    ((query product).run st).1.regs 20 = st.regs 20 ∧
    ((query product).run st).1.regs 54 = st.regs 54 ∧
    ((query product).run st).1.regs 55 = st.regs 55 ∧
    ((query product).run st).1.regs 56 = st.regs 56 ∧
    ((query product).run st).1.lists 7 = st.lists 7 ∧
    ((query product).run st).1.lists 13 = st.lists 13 ∧
    ((query product).run st).1.lists 18 = st.lists 18 := by
  refine ⟨run_regs_frame (query product) 20 ?_ st,
    run_regs_frame (query product) 54 ?_ st,
    run_regs_frame (query product) 55 ?_ st,
    run_regs_frame (query product) 56 ?_ st,
    run_lists_frame (query product) 7 ?_ st,
    run_lists_frame (query product) 13 ?_ st,
    run_lists_frame (query product) 18 ?_ st⟩
  all_goals cases product <;> decide

end PCP.Lang.BooleanLabelTransform
