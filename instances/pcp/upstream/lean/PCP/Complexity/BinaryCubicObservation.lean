/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientCode
import PCP.Complexity.BooleanCoefficientTransformCost
import PCP.Complexity.BinaryCubicCodeLang

/-!
# Affine observations of the concrete cubic colour constraint

Numeric field arithmetic is followed by the stored Boolean coefficient evaluator.
The label and mask source lists occupy disjoint slots from all field scratch data.
-/

namespace PCP.Lang.BinaryCubicObservation

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BinaryFieldCode

def evalRegs (i : Fin 15) : Fin 52 := ⟨36 + i.val, by omega⟩
def evalLists (i : Fin 4) : Fin 16 := ⟨12 + i.val, by omega⟩

theorem evalRegs_injective : Function.Injective evalRegs := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  simp only [evalRegs] at h
  omega

theorem evalLists_injective : Function.Injective evalLists := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  simp only [evalLists] at h
  omega

def evaluate52 : Stmt 52 16 :=
  BooleanCoefficientEvaluation.evaluate.rename evalRegs evalLists

/-- Width `20`, field output `26`, affine masks `12`, label bits `13`; result bit `46`. -/
def observe : Stmt 52 16 :=
  .seq (.assign 36 (.var 20)) (.seq (.assign 38 (.var 26)) evaluate52)

theorem observe_run {t : ℕ} [NeZero t] (a : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 52 16)
    (ht : st.regs 20 = t) (ha : st.regs 26 = (fieldEquiv t a).val)
    (hm : st.lists 12 = BooleanMask.masks t 1) (hL : st.lists 13 = encode L) :
    (observe.run st).1.regs 46 =
      (BooleanCoefficientArithmetic.evaluate (BinaryMaterializedField.coordinates t a) L).val := by
  let s := setReg (setReg st 36 (st.regs 20)) 38 (st.regs 26)
  have h := congrArg (fun z : State 15 4 × ℕ => z.1.regs 10)
    (BooleanCoefficientEvaluation.evaluate.run_rename evalRegs evalLists
      evalRegs_injective evalLists_injective s)
  have h' := BooleanCoefficientEvaluation.evaluate_coefficients L (fieldEquiv t a)
    (s.restrict evalRegs evalLists)
    (by simpa [State.restrict, evalRegs, s, Function.update] using ht)
    (by simpa [State.restrict, evalRegs, s] using ha) hm hL
  rw [point_fieldEquiv] at h'
  exact h.trans h'

def fieldRegs : Fin 36 → Fin 52 := Fin.castLE (by decide)
def fieldLists : Fin 11 → Fin 16 := Fin.castLE (by decide)
def cube52 : Stmt 52 16 := cubeMinusOne.rename fieldRegs fieldLists

theorem cube52_run {t : ℕ} [NeZero t] (a : BinaryMaterializedField.Element t)
    (st : State 52 16) (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t a).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) :
    (cube52.run st).1.regs 26 = (fieldEquiv t (a ^ 3 - 1)).val := by
  have h := congrArg (fun z : State 36 11 × ℕ => z.1.regs 26)
    (cubeMinusOne.run_rename fieldRegs fieldLists (Fin.castLE_injective _)
      (Fin.castLE_injective _) st)
  have hh := h.trans (cubeMinusOne_run (st.restrict fieldRegs fieldLists) a ht ha hm he)
  unfold cube52
  simpa only [State.restrict_regs, show fieldRegs 26 = (26 : Fin 52) from rfl,
    show fieldRegs 24 = (24 : Fin 52) from rfl] using hh

theorem cube52_source (st : State 52 16) : (cube52.run st).1.regs 24 = st.regs 24 := by
  have h := congrArg (fun z : State 36 11 × ℕ => z.1.regs 24)
    (cubeMinusOne.run_rename fieldRegs fieldLists (Fin.castLE_injective _)
      (Fin.castLE_injective _) st)
  have hh := h.trans (cubeMinusOne_frame (st.restrict fieldRegs fieldLists)).2.1
  unfold cube52
  simpa only [State.restrict_regs, show fieldRegs 26 = (26 : Fin 52) from rfl,
    show fieldRegs 24 = (24 : Fin 52) from rfl] using hh

def cubic : Stmt 52 16 := .seq cube52 observe

theorem cubic_run {t : ℕ} [NeZero t] (a : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 52 16)
    (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t a).val)
    (hmod : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hm : st.lists 12 = BooleanMask.masks t 1)
    (hL : st.lists 13 = encode L) :
    (cubic.run st).1.regs 46 =
      (BooleanCoefficientArithmetic.evaluate
        (BinaryMaterializedField.coordinates t (a ^ 3 - 1)) L).val := by
  have hc := cube52_run a st ht ha hmod he
  have hs20 := run_regs_frame cube52 20 (by decide) st
  have hs12 := run_lists_frame cube52 12 (by decide) st
  have hs13 := run_lists_frame cube52 13 (by decide) st
  simp only [cubic, run_seq_fst]
  generalize hs : (cube52.run st).1 = s at *
  exact observe_run (a ^ 3 - 1) L s (hs20.trans ht) hc
    (hs12.trans hm) (hs13.trans hL)

def mul52 : Stmt 52 16 := (binary .mul).rename fieldRegs fieldLists

theorem mul52_run {t : ℕ} [NeZero t] (a b : BinaryMaterializedField.Element t)
    (st : State 52 16) (ht : st.regs 20 = t)
    (ha : st.regs 24 = (fieldEquiv t a).val) (hb : st.regs 25 = (fieldEquiv t b).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) :
    (mul52.run st).1.regs 26 = (fieldEquiv t (a * b)).val := by
  have h := congrArg (fun z : State 36 11 × ℕ => z.1.regs 26)
    ((binary .mul).run_rename fieldRegs fieldLists (Fin.castLE_injective _)
      (Fin.castLE_injective _) st)
  have hh := h.trans (binary_run_field .mul (st.restrict fieldRegs fieldLists) a b ht ha hb hm he)
  unfold mul52
  simpa only [State.restrict_regs, show fieldRegs 26 = (26 : Fin 52) from rfl,
    Op.fieldEval] using hh

def weightedTail : Stmt 52 16 :=
  .seq (.assign 24 (.var 51)) (.seq (.assign 25 (.var 26))
    (.seq mul52 (.assign 24 (.var 50))))

theorem weightedTail_run {t : ℕ} [NeZero t] (a w : BinaryMaterializedField.Element t)
    (st : State 52 16) (ht : st.regs 20 = t)
    (ha : st.regs 26 = (fieldEquiv t a).val) (hw : st.regs 51 = (fieldEquiv t w).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) :
    (weightedTail.run st).1.regs 26 = (fieldEquiv t (w * a)).val := by
  let s := setReg (setReg st 24 (st.regs 51)) 25 (st.regs 26)
  have h := mul52_run w a s (by simpa [s, Function.update] using ht)
    (by simpa [s, Function.update] using hw) (by simpa [s] using ha) hm he
  dsimp only [s] at h
  simpa only [weightedTail, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_of_ne (by decide : (26 : Fin 52) ≠ 24)] using h

theorem weightedTail_source (st : State 52 16) :
    (weightedTail.run st).1.regs 24 = st.regs 50 := by
  let s := setReg (setReg st 24 (st.regs 51)) 25 (st.regs 26)
  have h := run_regs_frame mul52 50 (by decide) s
  simpa [weightedTail, run_seq_fst, run_assign_fst, Expr.eval, s, Function.update] using h

def weightedField : Stmt 52 16 :=
  .seq (.assign 50 (.var 24)) (.seq cube52 weightedTail)

theorem weightedField_run {t : ℕ} [NeZero t] (a w : BinaryMaterializedField.Element t)
    (st : State 52 16) (ht : st.regs 20 = t)
    (ha : st.regs 24 = (fieldEquiv t a).val) (hw : st.regs 51 = (fieldEquiv t w).val)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) :
    (weightedField.run st).1.regs 26 = (fieldEquiv t (w * (a ^ 3 - 1))).val := by
  let s := setReg st 50 (st.regs 24)
  have hc := cube52_run a s (by simpa [s, Function.update] using ht)
    (by simpa [s, Function.update] using ha) hm he
  have hs20 := run_regs_frame cube52 20 (by decide) s
  have hs51 := run_regs_frame cube52 51 (by decide) s
  have hs3 := run_lists_frame cube52 3 (by decide) s
  have hs7 := run_lists_frame cube52 7 (by decide) s
  have hst : s.regs 20 = t := by simpa [s, Function.update] using ht
  have hsw : s.regs 51 = (fieldEquiv t w).val := by simpa [s, Function.update] using hw
  dsimp only [s] at hc hs20 hs51 hs3 hs7 hst hsw
  simp only [weightedField, run_seq_fst, run_assign_fst, Expr.eval]
  generalize hsu : (cube52.run (setReg st 50 (st.regs 24))).1 = u at *
  exact weightedTail_run (a ^ 3 - 1) w u (hs20.trans hst) hc
    (hs51.trans hsw) (hs3.trans hm) (hs7.trans he)

theorem weightedField_source (st : State 52 16) :
    (weightedField.run st).1.regs 24 = st.regs 24 := by
  simp only [weightedField, run_seq_fst, run_assign_fst, Expr.eval, weightedTail_source]
  have h := run_regs_frame cube52 50 (by decide) (setReg st 50 (st.regs 24))
  simp only [setReg_regs, Function.update_self] at h
  generalize hs : (cube52.run (setReg st 50 (st.regs 24))).1 = s at *
  exact h

def weightedCubic : Stmt 52 16 := .seq weightedField observe

theorem weightedCubic_run {t : ℕ} [NeZero t] (a w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 52 16) (ht : st.regs 20 = t)
    (ha : st.regs 24 = (fieldEquiv t a).val) (hw : st.regs 51 = (fieldEquiv t w).val)
    (hmod : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hm : st.lists 12 = BooleanMask.masks t 1)
    (hL : st.lists 13 = encode L) :
    (weightedCubic.run st).1.regs 46 =
      (BooleanCoefficientArithmetic.evaluate
        (BinaryMaterializedField.coordinates t (w * (a ^ 3 - 1))) L).val := by
  have hc := weightedField_run a w st ht ha hw hmod he
  have hs20 := run_regs_frame weightedField 20 (by decide) st
  have hs12 := run_lists_frame weightedField 12 (by decide) st
  have hs13 := run_lists_frame weightedField 13 (by decide) st
  simp only [weightedCubic, run_seq_fst]
  generalize hs : (weightedField.run st).1 = s at *
  exact observe_run (w * (a ^ 3 - 1)) L s (hs20.trans ht) hc
    (hs12.trans hm) (hs13.trans hL)

def kernel (weighted : Bool) : Stmt 52 16 := if weighted then weightedCubic else cubic

def value {t : ℕ} [NeZero t] (weighted : Bool) (w a : BinaryMaterializedField.Element t) :
    BinaryMaterializedField.Element t := if weighted then w * (a ^ 3 - 1) else a ^ 3 - 1

theorem kernel_run {t : ℕ} [NeZero t] (weighted : Bool)
    (a w : BinaryMaterializedField.Element t) (L : Coefficients t 1) (st : State 52 16)
    (ht : st.regs 20 = t) (ha : st.regs 24 = (fieldEquiv t a).val)
    (hw : st.regs 51 = (fieldEquiv t w).val)
    (hmod : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus t))
    (he : st.lists 7 = []) (hm : st.lists 12 = BooleanMask.masks t 1)
    (hL : st.lists 13 = encode L) :
    ((kernel weighted).run st).1.regs 46 =
      (BooleanCoefficientArithmetic.evaluate
        (BinaryMaterializedField.coordinates t (value weighted w a)) L).val := by
  cases weighted <;> simp only [kernel, value, Bool.false_eq_true, ite_false, ite_true]
  · exact cubic_run a L st ht ha hmod he hm hL
  · exact weightedCubic_run a w L st ht ha hw hmod he hm hL

theorem kernel_source (weighted : Bool) (st : State 52 16) :
    ((kernel weighted).run st).1.regs 24 = st.regs 24 := by
  cases weighted <;> simp only [kernel, Bool.false_eq_true, ite_false, ite_true]
  · simp only [cubic, run_seq_fst]
    have h := run_regs_frame observe 24 (by decide) (cube52.run st).1
    exact h.trans (cube52_source st)
  · simp only [weightedCubic, run_seq_fst]
    have h := run_regs_frame observe 24 (by decide) (weightedField.run st).1
    exact h.trans (weightedField_source st)

end PCP.Lang.BinaryCubicObservation
