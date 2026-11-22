/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryCubicTableCost

/-!
# Complete concrete cubic coefficient-query translation

The program prepares affine masks, builds the actual field-function truth table,
and recovers the requested degree-three coefficient word. Both weighted and
unweighted colour constraints use this same materialized pipeline.
-/

namespace PCP.Lang.BinaryCubicQueryLang

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BinaryFieldCode
open BinaryCubicTable

variable {t : ℕ} [NeZero t]

def enumRegs : Fin 36 → Fin 54 := Fin.castLE (by decide)
def affineLists (i : Fin 2) : Fin 17 := if i = 0 then 7 else 12

theorem affineLists_injective : Function.Injective affineLists := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [affineLists]

def affineMasks : Stmt 54 17 :=
  .seq (.assign 21 (.const 1)) (BooleanMask.enumerateMasks.rename enumRegs affineLists)

omit [NeZero t] in
theorem affineMasks_run (st : State 54 17) (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    (affineMasks.run st).1.lists 12 = BooleanMask.masks t 1 := by
  simp only [affineMasks, run_seq_fst, run_assign_fst, Expr.eval]
  have h := congrArg (fun z : State 36 2 × ℕ => z.1.lists 1)
    (BooleanMask.enumerateMasks.run_rename enumRegs affineLists
      (Fin.castLE_injective _) affineLists_injective (setReg st 21 1))
  have hh := h.trans (BooleanMask.enumerateMasks_run t 1
    ((setReg st 21 1).restrict enumRegs affineLists)
    (by simpa [State.restrict, enumRegs, Function.update] using ht)
    (by rfl) (by simpa [State.restrict, affineLists] using he))
  simpa only [State.restrict_lists, show affineLists 1 = (12 : Fin 17) from rfl] using hh

omit [NeZero t] in
theorem affineMasks_cardinality (st : State 54 17) (ht : st.regs 20 = t) :
    (affineMasks.run st).1.regs 28 = 2 ^ t := by
  have h := congrArg (fun z : State 36 2 × ℕ => z.1.regs 28)
    (BooleanMask.enumerateMasks.run_rename enumRegs affineLists
      (Fin.castLE_injective _) affineLists_injective (setReg st 21 1))
  have hg := run_regs_frame BooleanMask.gatherMasks 28 (by decide)
    (BinaryPolynomialSelector.cardinality.run ((setReg st 21 1).restrict enumRegs affineLists)).1
  have hc := BinaryPolynomialSelector.cardinality_run
    ((setReg st 21 1).restrict enumRegs affineLists)
  have hh := h.trans (hg.trans hc)
  simp only [affineMasks, run_seq_fst, run_assign_fst, Expr.eval]
  simpa only [State.restrict_regs, show enumRegs 28 = (28 : Fin 54) from rfl,
    show enumRegs 20 = (20 : Fin 54) from rfl, setReg_regs,
    Function.update_of_ne (by decide : (20 : Fin 54) ≠ 21), ht] using hh

def prepare : Stmt 54 17 :=
  .seq affineMasks (.seq (.assign 52 (.var 28)) (.assign 53 (.const 1)))

theorem prepare_context (w : BinaryMaterializedField.Element t) (L : Coefficients t 1)
    (st : State 54 17) (ht : st.regs 20 = t) (hw : st.regs 51 = (fieldEquiv t w).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hL : st.lists 13 = encode L) :
    Context w L (prepare.run st).1 := by
  have ha := affineMasks_run st ht he
  have hq := affineMasks_cardinality st ht
  have hs20 := run_regs_frame affineMasks 20 (by decide) st
  have hs51 := run_regs_frame affineMasks 51 (by decide) st
  have hs3 := run_lists_frame affineMasks 3 (by decide) st
  have hs7 := run_lists_frame affineMasks 7 (by decide) st
  have hs13 := run_lists_frame affineMasks 13 (by decide) st
  simp only [prepare, run_seq_fst]
  generalize hs : (affineMasks.run st).1 = s at *
  simp [Context, run_assign_fst, Expr.eval, Function.update,
    hs20, ht, hs51, hw, hs3, hm, hs7, he, hs13, hL, ha, hq]

def transformLists : Fin 8 → Fin 17 := ![0, 16, 1, 2, 4, 5, 6, 7]

theorem transformLists_injective : Function.Injective transformLists := by decide

def transform54 : Stmt 54 17 :=
  BooleanCoefficientTransform.transform.rename enumRegs transformLists

omit [NeZero t] in
theorem transform54_run (f : (Fin t → ZMod 2) → ZMod 2) (st : State 54 17)
    (ht : st.regs 20 = t) (hr : st.regs 23 = 3) (hv : st.lists 16 = table t f)
    (he : st.lists 7 = []) :
    (transform54.run st).1.lists 5 =
      encode (BooleanCoefficientRecovery.recover f : Coefficients t 3) := by
  have h := congrArg (fun z : State 36 8 × ℕ => z.1.lists 5)
    (BooleanCoefficientTransform.transform.run_rename enumRegs transformLists
      (Fin.castLE_injective _) transformLists_injective st)
  have hh := h.trans (BooleanCoefficientTransform.transform_run f
    (st.restrict enumRegs transformLists) ht hr hv he)
  unfold transform54
  simpa only [State.restrict_lists, show transformLists 5 = (5 : Fin 17) from rfl] using hh

def translated (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) : Coefficients t 3 :=
  if weighted then BooleanCoefficientRecovery.weightedCubicQuery
    (BinaryMaterializedField.coordinates t) w L
  else BooleanCoefficientRecovery.cubicQuery (BinaryMaterializedField.coordinates t) L

theorem recover_booleanFunction (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) :
    (BooleanCoefficientRecovery.recover (booleanFunction weighted w L) : Coefficients t 3) =
      translated weighted w L := by
  cases weighted <;> rfl

/-- Inputs: width `20`, weight code `51`, modulus `3`, empty `7`, affine label bits `13`.
The output in list `5` is the actual degree-three query word. -/
def query (weighted : Bool) : Stmt 54 17 :=
  .seq prepare (.seq (tabulate weighted) (.seq (.assign 23 (.const 3)) transform54))

theorem query_run (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 54 17) (ht : st.regs 20 = t)
    (hw : st.regs 51 = (fieldEquiv t w).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hL : st.lists 13 = encode L) :
    ((query weighted).run st).1.lists 5 = encode (translated weighted w L) := by
  have hc := prepare_context w L st ht hw hm he hL
  simp only [query, run_seq_fst]
  generalize hs : (prepare.run st).1 = s at *
  have htable := tabulate_table weighted w L s hc
  have hs20 := run_regs_frame (tabulate weighted) 20 (by cases weighted <;> decide) s
  have hs7 := run_lists_frame (tabulate weighted) 7 (by cases weighted <;> decide) s
  generalize hu : ((tabulate weighted).run s).1 = u at *
  simp only [run_assign_fst, Expr.eval]
  have hh := transform54_run (booleanFunction weighted w L) (setReg u 23 3)
    (by simpa [Function.update] using hs20.trans hc.1) (by simp)
    htable (hs7.trans hc.2.2.2.1)
  rw [recover_booleanFunction] at hh
  exact hh

end PCP.Lang.BinaryCubicQueryLang
