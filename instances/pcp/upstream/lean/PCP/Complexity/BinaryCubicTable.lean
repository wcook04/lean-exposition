/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryCubicObservationCost

/-!
# Stored truth tables of cubic affine observations

A counted loop visits numeric field codes in order. Each iteration performs the
actual materialized field operations and stored affine evaluation, then appends
one output bit. No function-space enumeration is executed.
-/

namespace PCP.Lang.BinaryCubicTable

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BinaryFieldCode

variable {t : ℕ} [NeZero t]

def booleanFunction (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (x : Fin t → ZMod 2) : ZMod 2 :=
  BooleanCoefficientArithmetic.evaluate (BinaryMaterializedField.coordinates t
    (BinaryCubicObservation.value weighted w ((BinaryMaterializedField.coordinates t).symm x))) L

def numericValue (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (j : ℕ) : ℕ :=
  if hj : j < 2 ^ t then (booleanFunction weighted w L (point t ⟨j, hj⟩)).val else 0

theorem numericValue_bit (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (j : ℕ) : numericValue weighted w L j < 2 := by
  unfold numericValue
  split_ifs
  · exact ZMod.val_lt _
  · decide

def kernelRegs : Fin 52 → Fin 54 := Fin.castLE (by decide)
def kernelLists : Fin 16 → Fin 17 := Fin.castLE (by decide)
def fieldKernel (weighted : Bool) : Stmt 54 17 :=
  (BinaryCubicObservation.kernel weighted).rename kernelRegs kernelLists

/-- The semantic parameters and stored source arrays preserved throughout the loop. -/
def Context (w : BinaryMaterializedField.Element t) (L : Coefficients t 1)
    (st : State 54 17) : Prop :=
  st.regs 20 = t ∧ st.regs 51 = (fieldEquiv t w).val ∧
    st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t) ∧ st.lists 7 = [] ∧
    st.lists 12 = BooleanMask.masks t 1 ∧ st.lists 13 = encode L ∧
    st.regs 52 = 2 ^ t ∧ st.regs 53 = 1

theorem fieldKernel_run (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 54 17) (hc : Context w L st)
    (hj : st.regs 24 < 2 ^ t) :
    ((fieldKernel weighted).run st).1.regs 46 = numericValue weighted w L (st.regs 24) := by
  let i : Fin (2 ^ t) := ⟨st.regs 24, hj⟩
  let a := (fieldEquiv t).symm i
  have h := congrArg (fun z : State 52 16 × ℕ => z.1.regs 46)
    ((BinaryCubicObservation.kernel weighted).run_rename kernelRegs kernelLists
      (Fin.castLE_injective _) (Fin.castLE_injective _) st)
  have hh := h.trans (BinaryCubicObservation.kernel_run weighted a w L
    (st.restrict kernelRegs kernelLists) hc.1
    (by change st.regs 24 = (fieldEquiv t a).val; simp [a, i])
    hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1)
  have hp : (BinaryMaterializedField.coordinates t).symm (point t i) = a := by
    have hpoint := point_fieldEquiv a
    simp only [a, Equiv.apply_symm_apply] at hpoint
    rw [hpoint, LinearEquiv.symm_apply_apply]
  have hv : numericValue weighted w L (st.regs 24) =
      (BooleanCoefficientArithmetic.evaluate
        (BinaryMaterializedField.coordinates t
          (BinaryCubicObservation.value weighted w a)) L).val := by
    rw [numericValue, dite_eq_left hj]
    change (booleanFunction weighted w L (point t i)).val = _
    rw [booleanFunction, hp]
  unfold fieldKernel
  rw [hv]
  simpa only [State.restrict_regs, show kernelRegs 46 = (46 : Fin 54) from rfl] using hh

theorem fieldKernel_source (weighted : Bool) (st : State 54 17) :
    ((fieldKernel weighted).run st).1.regs 24 = st.regs 24 := by
  have h := congrArg (fun z : State 52 16 × ℕ => z.1.regs 24)
    ((BinaryCubicObservation.kernel weighted).run_rename kernelRegs kernelLists
      (Fin.castLE_injective _) (Fin.castLE_injective _) st)
  have hh := h.trans (BinaryCubicObservation.kernel_source weighted
    (st.restrict kernelRegs kernelLists))
  unfold fieldKernel
  simpa only [State.restrict_regs, show kernelRegs 24 = (24 : Fin 54) from rfl] using hh

theorem fieldKernel_reg (weighted : Bool) (st : State 54 17) (i : Fin 54)
    (hi : i ∈ ([20, 51, 52, 53] : List (Fin 54))) :
    ((fieldKernel weighted).run st).1.regs i = st.regs i := by
  apply run_regs_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> cases weighted <;> decide

theorem fieldKernel_list (weighted : Bool) (st : State 54 17) (i : Fin 17)
    (hi : i ∈ ([3, 7, 12, 13, 16] : List (Fin 17))) :
    ((fieldKernel weighted).run st).1.lists i = st.lists i := by
  apply run_lists_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> cases weighted <;> decide

def body (weighted : Bool) : Stmt 54 17 :=
  .seq (fieldKernel weighted) (.seq (.push 16 46) (.assign 24 (.add 24 53)))

theorem body_step (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 54 17) (hc : Context w L st)
    (hj : st.regs 24 < 2 ^ t) :
    ((body weighted).run st).1.regs 24 = st.regs 24 + 1 ∧
      ((body weighted).run st).1.lists 16 =
        numericValue weighted w L (st.regs 24) :: st.lists 16 := by
  have hr := fieldKernel_run weighted w L st hc hj
  have hs24 := fieldKernel_source weighted st
  have hs53 := fieldKernel_reg weighted st 53 (by decide)
  have hs16 := fieldKernel_list weighted st 16 (by decide)
  simp only [body, run_seq_fst]
  generalize hs : ((fieldKernel weighted).run st).1 = s at *
  simp [run_push_fst, run_assign_fst, Expr.eval, Function.update,
    hr, hs24, hs53, hs16, hc.2.2.2.2.2.2.2]

theorem body_context (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 54 17) (hc : Context w L st) :
    Context w L ((body weighted).run st).1 := by
  have hreg (i : Fin 54) (hi : i ∈ ([20, 51, 52, 53] : List (Fin 54))) :
      ((body weighted).run st).1.regs i = st.regs i := by
    apply run_regs_frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> cases weighted <;> decide
  have hlist (i : Fin 17) (hi : i ∈ ([3, 7, 12, 13] : List (Fin 17))) :
      ((body weighted).run st).1.lists i = st.lists i := by
    apply run_lists_frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> cases weighted <;> decide
  unfold Context at hc ⊢
  rw [hreg 20 (by decide), hreg 51 (by decide), hreg 52 (by decide), hreg 53 (by decide),
    hlist 3 (by decide), hlist 7 (by decide), hlist 12 (by decide), hlist 13 (by decide)]
  exact hc

/-- Count `52` is the field size; list `16` is created from the reusable empty source. -/
def tabulate (weighted : Bool) : Stmt 54 17 :=
  .seq (.copy 7 16) (.seq (.assign 24 (.const 0)) (.seq (.assign 53 (.const 1))
    (.seq (.loop 52 (body weighted)) (.rev 16))))

theorem tabulate_run (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 54 17) (hc : Context w L st) :
    ((tabulate weighted).run st).1.lists 16 =
      (List.range (2 ^ t)).map (numericValue weighted w L) := by
  let q := 2 ^ t
  let s := setReg (setReg (setList st 16 []) 24 0) 53 1
  have hinit : Context w L s ∧ s.regs 24 = 0 ∧
      s.lists 16 = ((List.range 0).map (numericValue weighted w L)).reverse := by
    simp [Context, s, Function.update, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
      hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1]
  have hout := iterate_inv (body weighted).run (Nat.size q + 1) q
    (fun j u => Context w L u ∧ u.regs 24 = j ∧
      u.lists 16 = ((List.range j).map (numericValue weighted w L)).reverse)
    (by
      intro j u hj hu
      have hh := body_step weighted w L u hu.1 (by rw [hu.2.1]; exact hj)
      refine ⟨body_context weighted w L u hu.1, hh.1.trans (by rw [hu.2.1]), ?_⟩
      rw [hh.2, hu.2.1, hu.2.2]
      simp [List.range_succ]) s hinit
  simp only [tabulate, run_seq_fst, run_copy_fst, run_assign_fst, Expr.eval,
    run_loop_fst, run_rev_fst, setReg_regs, setList_regs, Function.update,
    Fin.reduceEq, dite_false, hc.2.2.2.1, hc.2.2.2.2.2.2.1]
  change ((iterate (body weighted).run (Nat.size q + 1) q s).1.lists 16).reverse = _
  rw [hout.2.2, List.reverse_reverse]

theorem range_values (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) :
    (List.range (2 ^ t)).map (numericValue weighted w L) =
      table t (booleanFunction weighted w L) := by
  rw [← BooleanCoefficientTransform.fullMasks_range]
  simp only [fullMasks, List.map_ofFn, table]
  apply congrArg List.ofFn
  funext i
  simp [numericValue, i.isLt]

/-- The emitted data are the exact input truth table for coefficient recovery. -/
theorem tabulate_table (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 54 17) (hc : Context w L st) :
    ((tabulate weighted).run st).1.lists 16 = table t (booleanFunction weighted w L) :=
  (tabulate_run weighted w L st hc).trans (range_values weighted w L)

end PCP.Lang.BinaryCubicTable
