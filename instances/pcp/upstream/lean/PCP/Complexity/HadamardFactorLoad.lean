/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowSpec

/-!
# Materializing one degree-dependent Hadamard factor

The source factor codes form a stored natural list. One code is removed from the
work cursor, its exact coefficient dimension is computed by the mask enumeration,
and the fixed-width serializer materializes the factor. The field width is saved
and restored explicitly.
-/

namespace PCP.Lang.HadamardFactorLoad

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList HadamardLabel

variable {t a : ℕ}

def masks : Stmt 80 32 :=
  (BooleanLabelTransform.masks false).rename transformRegs transformLists

theorem masks_run (st : State 80 32) (ht : st.regs 20 = t)
    (ha : st.regs 54 = a) (he : st.lists 7 = []) :
    (masks.run st).1.lists 12 = BooleanMask.masks t a := by
  have h := congrArg (fun z : State 57 20 × ℕ => z.1.lists 12)
    ((BooleanLabelTransform.masks false).run_rename transformRegs transformLists
      (Fin.castLE_injective _) (Fin.castLE_injective _) st)
  have hh := h.trans (BooleanLabelTransform.masks_run false
    (st.restrict transformRegs transformLists) ht ha he)
  unfold masks
  simpa only [State.restrict_lists, show transformLists 12 = (12 : Fin 32) from rfl] using hh

def materializeRegs : Fin 36 → Fin 80 := Fin.castLE (by decide)
def materializeLists : Fin 2 → Fin 32 := ![7, 18]

theorem materializeLists_injective : Function.Injective materializeLists := by decide

def materialize : Stmt 80 32 :=
  BinaryPolynomialSelector.materialize.rename materializeRegs materializeLists

theorem materialize_run (p : Coefficients t a) (st : State 80 32)
    (hn : st.regs 20 = BooleanCoefficientIndex.dimension t a)
    (hp : st.regs 33 = code p) (he : st.lists 7 = []) :
    (materialize.run st).1.lists 18 = encode p := by
  have h := congrArg (fun z : State 36 2 × ℕ => z.1.lists 1)
    (BinaryPolynomialSelector.materialize.run_rename materializeRegs materializeLists
      (Fin.castLE_injective _) materializeLists_injective st)
  have hh := h.trans (materialize_coefficients p (st.restrict materializeRegs materializeLists)
    hn hp he)
  unfold materialize
  simpa only [State.restrict_lists, show materializeLists 1 = (18 : Fin 32) from rfl] using hh

def saveAndPop : Stmt 80 32 :=
  .seq (.assign 57 (.var 20)) (.seq (.pop 25 64 65) (.assign 54 (.var 60)))

theorem saveAndPop_run (st : State 80 32) (c : ℕ) (cs : List ℕ)
    (hs : st.lists 25 = c :: cs) :
    (saveAndPop.run st).1.regs 57 = st.regs 20 ∧
    (saveAndPop.run st).1.regs 64 = c ∧
    (saveAndPop.run st).1.regs 54 = st.regs 60 ∧
    (saveAndPop.run st).1.lists 25 = cs := by
  simp [saveAndPop, Stmt.run, Expr.eval, Function.update, hs]

def setup : Stmt 80 32 := .seq saveAndPop masks

def Prepared (p : Coefficients t a) (cs : List ℕ) (st : State 80 32) : Prop :=
  st.regs 57 = t ∧ st.regs 64 = code p ∧ st.lists 12 = BooleanMask.masks t a ∧
    st.lists 25 = cs ∧ st.lists 7 = []

theorem setup_run (p : Coefficients t a) (cs : List ℕ) (st : State 80 32)
    (ht : st.regs 20 = t) (ha : st.regs 60 = a) (he : st.lists 7 = [])
    (hp : st.lists 25 = code p :: cs) : Prepared p cs (setup.run st).1 := by
  have hs := saveAndPop_run st (code p) cs hp
  have hs20 := run_regs_frame saveAndPop 20 (by decide) st
  have hs7 := run_lists_frame saveAndPop 7 (by decide) st
  simp only [setup, run_seq_fst]
  generalize hu : (saveAndPop.run st).1 = u at *
  have hm := masks_run u (hs20.trans ht) (hs.2.2.1.trans ha) (hs7.trans he)
  have hu57 := run_regs_frame masks 57 (by decide) u
  have hu64 := run_regs_frame masks 64 (by decide) u
  have hu25 := run_lists_frame masks 25 (by decide) u
  have hu7 := run_lists_frame masks 7 (by decide) u
  exact ⟨hu57.trans (hs.1.trans ht), hu64.trans hs.2.1, hm,
    hu25.trans hs.2.2.2, hu7.trans (hs7.trans he)⟩

def loadTail : Stmt 80 32 :=
  .seq (.len 12 20) (.seq (.assign 33 (.var 64))
    (.seq materialize (.assign 20 (.var 57))))

theorem loadTail_run (p : Coefficients t a) (cs : List ℕ) (st : State 80 32)
    (hp : Prepared p cs st) :
    (loadTail.run st).1.lists 18 = encode p ∧
    (loadTail.run st).1.regs 20 = t ∧ (loadTail.run st).1.lists 25 = cs := by
  let u := setReg (setReg st 20 (st.lists 12).length) 33 (st.regs 64)
  have hn : u.regs 20 = BooleanCoefficientIndex.dimension t a := by
    simp [u, Function.update, hp.2.2.1]
  have hcode : u.regs 33 = code p := by simpa [u] using hp.2.1
  have hm := materialize_run p u hn hcode hp.2.2.2.2
  have hu57 := run_regs_frame materialize 57 (by decide) u
  have hu25 := run_lists_frame materialize 25 (by decide) u
  dsimp only [u] at hm hu57 hu25
  simp only [loadTail, run_seq_fst, run_len_fst, run_assign_fst, Expr.eval, setReg_regs,
    Function.update_of_ne (by decide : (64 : Fin 80) ≠ 20)]
  generalize hv : (materialize.run
    (setReg (setReg st 20 (st.lists 12).length) 33 (st.regs 64))).1 = v at *
  simp [Function.update, hm, hu57, hp.1, hu25, hp.2.2.2.1]

/-- Inputs: width `20`, factor degree `60`, empty `7`, nonempty factor-code cursor `25`.
The factor bits appear in list `18`, the cursor advances once, and width `20` is restored. -/
def load : Stmt 80 32 := .seq setup loadTail

theorem load_run (p : Coefficients t a) (cs : List ℕ) (st : State 80 32)
    (ht : st.regs 20 = t) (ha : st.regs 60 = a) (he : st.lists 7 = [])
    (hp : st.lists 25 = code p :: cs) :
    (load.run st).1.lists 18 = encode p ∧
    (load.run st).1.regs 20 = t ∧ (load.run st).1.lists 25 = cs := by
  rw [load, run_seq_fst]
  exact loadTail_run p cs _ (setup_run p cs st ht ha he hp)

/-- Loading a factor retains the complete immutable row seed. -/
theorem load_context {r : ℕ} (s : Hadamard.TestRandomness t r)
    (p : Coefficients t a) (cs : List ℕ) (st : State 80 32)
    (hc : HadamardRow.Context s st) (ha : st.regs 60 = a)
    (hp : st.lists 25 = code p :: cs) : HadamardRow.Context s (load.run st).1 := by
  have hwidth := (load_run p cs st hc.1 ha hc.2.2.1 hp).2.1
  have h56 := run_regs_frame load 56 (by decide) st
  have h7 := run_lists_frame load 7 (by decide) st
  have h20 := run_lists_frame load 20 (by decide) st
  have h21 := run_lists_frame load 21 (by decide) st
  have h22 := run_lists_frame load 22 (by decide) st
  have h23 := run_lists_frame load 23 (by decide) st
  exact ⟨hwidth, h56.trans hc.2.1, h7.trans hc.2.2.1,
    h20.trans hc.2.2.2.1, h21.trans hc.2.2.2.2.1,
    h22.trans hc.2.2.2.2.2.1, h23.trans hc.2.2.2.2.2.2⟩

end PCP.Lang.HadamardFactorLoad
