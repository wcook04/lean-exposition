/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientRecoveryCost

/-!
# Complete stored-mask preparation and Boolean subset transform

The program constructs both mask lists internally before recovering coefficients.
Only the width, requested degree, truth table, and an empty list are inputs.
-/

namespace PCP.Lang.BooleanCoefficientTransform

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientIndex
open BooleanCoefficientList BooleanMask BinaryPolynomialSelector

theorem fullMasks_range (t : ℕ) : fullMasks t = List.range (2 ^ t) := by
  apply List.ext_getElem (by simp [fullMasks])
  intro i hi hj
  simp [fullMasks]

theorem masks_full (t : ℕ) : masks t t = fullMasks t := by
  rw [fullMasks_range, masks]
  apply List.filter_eq_self.mpr
  intro i _
  exact decide_eq_true (digits_sum_le t i)

def fullLists (i : Fin 2) : Fin 8 := if i = 0 then 7 else 0

def requestedLists (i : Fin 2) : Fin 8 := if i = 0 then 7 else 4

theorem fullLists_injective : Function.Injective fullLists := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [fullLists]

theorem requestedLists_injective : Function.Injective requestedLists := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [requestedLists]

def full : Stmt 36 8 :=
  .seq (.assign 21 (.var 20)) (enumerateMasks.rename id fullLists)

def requested : Stmt 36 8 :=
  .seq (.assign 21 (.var 23)) (enumerateMasks.rename id requestedLists)

theorem full_run (t : ℕ) (st : State 36 8) (ht : st.regs 20 = t) (he : st.lists 7 = []) :
    (full.run st).1.lists 0 = fullMasks t := by
  simp only [full, run_seq_fst, run_assign_fst, Expr.eval]
  have h := congrArg (fun z : State 36 2 × ℕ => z.1.lists 1)
    (enumerateMasks.run_rename id fullLists Function.injective_id fullLists_injective
      (setReg st 21 (st.regs 20)))
  have h' := enumerateMasks_run t t ((setReg st 21 (st.regs 20)).restrict id fullLists)
    (by simpa [State.restrict, Function.update] using ht)
    (by simpa [State.restrict] using ht)
    (by simpa [State.restrict, fullLists] using he)
  exact (h.trans h').trans (masks_full t)

theorem requested_run (t r : ℕ) (st : State 36 8)
    (ht : st.regs 20 = t) (hr : st.regs 23 = r) (he : st.lists 7 = []) :
    (requested.run st).1.lists 4 = masks t r := by
  simp only [requested, run_seq_fst, run_assign_fst, Expr.eval]
  have h := congrArg (fun z : State 36 2 × ℕ => z.1.lists 1)
    (enumerateMasks.run_rename id requestedLists Function.injective_id requestedLists_injective
      (setReg st 21 (st.regs 23)))
  exact h.trans (enumerateMasks_run t r
    ((setReg st 21 (st.regs 23)).restrict id requestedLists)
    (by simpa [State.restrict, Function.update] using ht)
    (by simpa [State.restrict] using hr)
    (by simpa [State.restrict, requestedLists] using he))

def prepare : Stmt 36 8 := .seq full requested

theorem prepare_run (t r : ℕ) (st : State 36 8)
    (ht : st.regs 20 = t) (hr : st.regs 23 = r) (he : st.lists 7 = []) :
    (prepare.run st).1.lists 0 = fullMasks t ∧
      (prepare.run st).1.lists 4 = masks t r := by
  have hf := full_run t st ht he
  have hs20 := run_regs_frame full 20 (by decide) st
  have hs23 := run_regs_frame full 23 (by decide) st
  have hs7 := run_lists_frame full 7 (by decide) st
  simp only [prepare, run_seq_fst]
  generalize hs : (full.run st).1 = s at *
  exact ⟨(run_lists_frame requested 0 (by decide) s).trans hf,
    requested_run t r s (hs20.trans ht) (hs23.trans hr) (hs7.trans he)⟩

def recoveryRegs : Fin 16 → Fin 36 := Fin.castLE (by decide)
def recovery36 : Stmt 36 8 := BooleanCoefficientRecoveryLang.recover.rename recoveryRegs id

/-- Width `20`, requested degree `23`, truth table list `1`, empty list `7` are inputs.
The stored coefficient word is returned in list `5`. -/
def transform : Stmt 36 8 :=
  .seq prepare (.seq (.assign 0 (.var 20)) recovery36)

theorem transform_run {t r : ℕ} (f : (Fin t → ZMod 2) → ZMod 2) (st : State 36 8)
    (ht : st.regs 20 = t) (hr : st.regs 23 = r) (hv : st.lists 1 = table t f)
    (he : st.lists 7 = []) :
    (transform.run st).1.lists 5 =
      BooleanCoefficientList.encode (BooleanCoefficientRecovery.recover f : Coefficients t r) := by
  have hp := prepare_run t r st ht hr he
  have hs20 := run_regs_frame prepare 20 (by decide) st
  have hs1 := run_lists_frame prepare 1 (by decide) st
  have hs7 := run_lists_frame prepare 7 (by decide) st
  simp only [transform, run_seq_fst, run_assign_fst, Expr.eval]
  generalize hs : (prepare.run st).1 = s at *
  have h := congrArg (fun z : State 16 8 × ℕ => z.1.lists 5)
    (BooleanCoefficientRecoveryLang.recover.run_rename recoveryRegs id
      (Fin.castLE_injective _) Function.injective_id (setReg s 0 (s.regs 20)))
  exact h.trans (BooleanCoefficientRecoveryLang.recover_coefficients f
    ((setReg s 0 (s.regs 20)).restrict recoveryRegs id)
    (by simpa [State.restrict, recoveryRegs] using hs20.trans ht)
    hp.1 (hs1.trans hv) hp.2 (hs7.trans he))

end PCP.Lang.BooleanCoefficientTransform
