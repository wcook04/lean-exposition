/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientTransformCost

/-!
# Stored kernels for coefficient-label transformations

Two coefficient evaluators share scratch space while retaining both source words.
Their product is a Boolean observation suitable for the proved subset transform.
-/

namespace PCP.Lang.BooleanLabelKernel

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList

variable {t a b : ℕ}

def evalRegs (i : Fin 15) : Fin 57 := ⟨36 + i.val, by omega⟩
def evalLists (right : Bool) : Fin 4 → Fin 20 :=
  if right then ![19, 18, 14, 15] else ![12, 13, 14, 15]

theorem evalRegs_injective : Function.Injective evalRegs := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [evalRegs] at hv
  omega

theorem evalLists_injective (right : Bool) : Function.Injective (evalLists right) := by
  cases right <;> decide

def evaluate (right : Bool) : Stmt 57 20 :=
  .seq (.assign 36 (.var 20)) (.seq (.assign 38 (.var 24))
    (BooleanCoefficientEvaluation.evaluate.rename evalRegs (evalLists right)))

theorem evaluate_run (right : Bool) (p : Coefficients t a) (x : Fin (2 ^ t))
    (st : State 57 20) (ht : st.regs 20 = t) (hx : st.regs 24 = x.val)
    (hm : st.lists (evalLists right 0) = BooleanMask.masks t a)
    (hp : st.lists (evalLists right 1) = encode p) :
    ((evaluate right).run st).1.regs 46 =
      (BooleanCoefficientArithmetic.evaluate (point t x) p).val := by
  let s := setReg (setReg st 36 (st.regs 20)) 38 (st.regs 24)
  have h := congrArg (fun z : State 15 4 × ℕ => z.1.regs 10)
    (BooleanCoefficientEvaluation.evaluate.run_rename evalRegs (evalLists right)
      evalRegs_injective (evalLists_injective right) s)
  have hh := h.trans (BooleanCoefficientEvaluation.evaluate_coefficients p x
    (s.restrict evalRegs (evalLists right))
    (by simpa [State.restrict, evalRegs, s, Function.update] using ht)
    (by simpa [State.restrict, evalRegs, s] using hx) hm hp)
  exact hh

def productTail : Stmt 57 20 :=
  .seq (.assign 51 (.var 46)) (.seq (evaluate true) (.assign 46 (.mul 51 46)))

def kernel (product : Bool) : Stmt 57 20 :=
  .seq (evaluate false) (if product then productTail else .skip)

def function (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (x : Fin t → ZMod 2) : ZMod 2 :=
  if product then BooleanCoefficientArithmetic.evaluate x p *
    BooleanCoefficientArithmetic.evaluate x q else BooleanCoefficientArithmetic.evaluate x p

def Context (p : Coefficients t a) (q : Coefficients t b) (st : State 57 20) : Prop :=
  st.regs 20 = t ∧ st.lists 12 = BooleanMask.masks t a ∧ st.lists 13 = encode p ∧
    st.lists 19 = BooleanMask.masks t b ∧ st.lists 18 = encode q

theorem kernel_run (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (x : Fin (2 ^ t)) (st : State 57 20) (hc : Context p q st)
    (hx : st.regs 24 = x.val) :
    ((kernel product).run st).1.regs 46 = (function product p q (point t x)).val := by
  have hl := evaluate_run false p x st hc.1 hx hc.2.1 hc.2.2.1
  have hs20 := run_regs_frame (evaluate false) 20 (by decide) st
  have hs24 := run_regs_frame (evaluate false) 24 (by decide) st
  have hs19 := run_lists_frame (evaluate false) 19 (by decide) st
  have hs18 := run_lists_frame (evaluate false) 18 (by decide) st
  simp only [kernel, run_seq_fst]
  generalize hs : ((evaluate false).run st).1 = s at *
  cases product with
  | false => exact hl
  | true =>
    let u := setReg s 51 (s.regs 46)
    have hr := evaluate_run true q x u
      (by simpa [u, Function.update] using hs20.trans hc.1)
      (by simpa [u, Function.update] using hs24.trans hx)
      (hs19.trans hc.2.2.2.1) (hs18.trans hc.2.2.2.2)
    have h51 := run_regs_frame (evaluate true) 51 (by decide) u
    dsimp only [u] at hr h51
    simp only [ite_true, productTail, run_seq_fst, run_assign_fst, Expr.eval]
    generalize hu : ((evaluate true).run (setReg s 51 (s.regs 46))).1 = v at *
    simp only [setReg_regs, Function.update_self, h51, hl, hr, function, ↓reduceIte,
      ZMod.val_mul]
    symm
    apply Nat.mod_eq_of_lt
    have hpv := ZMod.val_lt (BooleanCoefficientArithmetic.evaluate (point t x) p)
    have hqv := ZMod.val_lt (BooleanCoefficientArithmetic.evaluate (point t x) q)
    nlinarith

theorem kernel_reg (product : Bool) (st : State 57 20) (i : Fin 57)
    (hi : i ∈ ([20, 24, 52, 53, 54, 55, 56] : List (Fin 57))) :
    ((kernel product).run st).1.regs i = st.regs i := by
  apply run_regs_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases product <;> decide

theorem kernel_list (product : Bool) (st : State 57 20) (i : Fin 20)
    (hi : i ∈ ([7, 12, 13, 16, 18, 19] : List (Fin 20))) :
    ((kernel product).run st).1.lists i = st.lists i := by
  apply run_lists_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> cases product <;> decide

end PCP.Lang.BooleanLabelKernel
