/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardLabelCost

/-!
# Numeric homogeneous query labels at arbitrary row degree

The program constructs the padded homogeneous coefficient array and serializes its
actual increasing-mask coordinate index. Input coordinates and parameters survive.
-/

namespace PCP.Lang.HadamardHomogeneousCode

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList HadamardLabel

variable {t r : ℕ}

def construct : Stmt 80 32 :=
  BooleanLabelConstructors.homogeneous.rename transformRegs transformLists

theorem construct_run (hr : 1 ≤ r) (w : Fin t → ZMod 2) (st : State 80 32)
    (ht : st.regs 20 = t) (hd : st.regs 56 = r) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn fun i => (w i).val) :
    (construct.run st).1.lists 5 =
      encode (BooleanCoefficientArithmetic.homogeneousIndex hr w) := by
  have h := congrArg (fun z : State 57 20 × ℕ => z.1.lists 5)
    (BooleanLabelConstructors.homogeneous.run_rename transformRegs transformLists
      (Fin.castLE_injective _) (Fin.castLE_injective _) st)
  have hh := h.trans (BooleanLabelConstructors.homogeneous_run hr w
    (st.restrict transformRegs transformLists) ht hd he hw)
  unfold construct
  simpa only [State.restrict_lists, show transformLists 5 = (5 : Fin 32) from rfl] using hh

def program : Stmt 80 32 := .seq construct (.seq (.copy 5 0) HadamardLabel.decode)

theorem program_run (hr : 1 ≤ r) (w : Fin t → ZMod 2) (st : State 80 32)
    (ht : st.regs 20 = t) (hd : st.regs 56 = r) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn fun i => (w i).val) :
    (program.run st).1.regs 1 = code (BooleanCoefficientArithmetic.homogeneousIndex hr w) ∧
      (program.run st).1.lists 5 =
        encode (BooleanCoefficientArithmetic.homogeneousIndex hr w) := by
  have hc := construct_run hr w st ht hd he hw
  simp only [program, run_seq_fst]
  generalize hu : (construct.run st).1 = u at *
  simp only [run_copy_fst]
  have hd := decode_run (BooleanCoefficientArithmetic.homogeneousIndex hr w)
    (setList u 0 (u.lists 5)) (by simpa using hc)
  have h5 := run_lists_frame HadamardLabel.decode 5 (by decide) (setList u 0 (u.lists 5))
  exact ⟨hd, by simpa [Function.update] using h5.trans hc⟩

theorem program_frame (st : State 80 32) :
    (program.run st).1.regs 20 = st.regs 20 ∧
      (program.run st).1.regs 56 = st.regs 56 ∧
      (program.run st).1.lists 7 = st.lists 7 ∧
      (program.run st).1.lists 17 = st.lists 17 := by
  exact ⟨run_regs_frame program 20 (by decide) st,
    run_regs_frame program 56 (by decide) st,
    run_lists_frame program 7 (by decide) st,
    run_lists_frame program 17 (by decide) st⟩

theorem construct_cost (w : Fin t → ZMod 2) (st : State 80 32)
    (ht : st.regs 20 = t) (hd : st.regs 56 = r) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn fun i => (w i).val) :
    (construct.run st).2 ≤ (BooleanLabelTransform.queryConstant + 200) *
      (2 ^ t + Nat.size r + 5) ^ 8 := by
  rw [construct, Stmt.run_rename_cost BooleanLabelConstructors.homogeneous
    transformRegs transformLists (show Function.Injective transformRegs from Fin.castLE_injective _)
    (show Function.Injective transformLists from Fin.castLE_injective _)]
  exact BooleanLabelConstructors.homogeneous_cost w
    (st.restrict transformRegs transformLists) ht hd he hw

theorem program_cost (hr : 1 ≤ r) (w : Fin t → ZMod 2) (st : State 80 32)
    (ht : st.regs 20 = t) (hd : st.regs 56 = r) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn fun i => (w i).val) :
    (program.run st).2 ≤ (BooleanLabelTransform.queryConstant + 3 * WordCodec.passConstant + 300) *
      (2 ^ t + Nat.size r + 5) ^ 8 := by
  have hc := construct_cost w st ht hd he hw
  have ho := construct_run hr w st ht hd he hw
  simp only [program, run_seq_snd]
  generalize hu : (construct.run st).1 = u at *
  simp only [run_copy_snd, run_copy_fst]
  have hd := decode_cost (BooleanCoefficientArithmetic.homogeneousIndex hr w)
    (setList u 0 (u.lists 5)) (by simpa using ho)
  have hs : listSize (u.lists 5) ≤ 2 * 2 ^ t := by
    rw [ho]; exact encode_size _
  have hp : (2 ^ t + 1) ^ 2 ≤ (2 ^ t + Nat.size r + 5) ^ 8 :=
    (Nat.pow_le_pow_left (by omega) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide))
  have hd' := hd.trans (Nat.mul_le_mul_left _ hp)
  have hlow : 2 ^ t + 5 ≤ (2 ^ t + Nat.size r + 5) ^ 8 :=
    (by omega : 2 ^ t + 5 ≤ 2 ^ t + Nat.size r + 5).trans (Nat.le_pow (by decide))
  nlinarith only [hc, hd', hs, hlow, Nat.zero_le WordCodec.passConstant]

end PCP.Lang.HadamardHomogeneousCode
