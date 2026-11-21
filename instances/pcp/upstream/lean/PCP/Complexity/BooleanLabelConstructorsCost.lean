/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanLabelConstructors

/-!
# Charged bounds for constant and homogeneous label constructors

The estimates include the actual source-word construction and complete stored
coefficient embedding, rather than assuming access to coefficient padding.
-/

namespace PCP.Lang.BooleanLabelConstructors

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList
open BooleanLabelTransform (queryConstant)

variable {t r : ℕ}

theorem homogeneousPrepare_cost (w : Fin t → ZMod 2) (st : State 57 20)
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (homogeneousPrepare.run st).2 ≤ 2 * t + 10 := by
  have hb : BinaryField.Bits (List.ofFn (fun i => (w i).val)) := by
    intro n hn
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
    exact ZMod.val_lt _
  have hs := BinaryField.listSize_bits hb
  simp only [List.length_ofFn] at hs
  simp only [homogeneousPrepare, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    setReg_regs, setList_regs, Function.update, dite_true, Nat.size_zero, Nat.size_one, hw]
  omega

theorem homogeneous_cost (w : Fin t → ZMod 2) (st : State 57 20)
    (ht : st.regs 20 = t) (hd : st.regs 56 = r) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val)) :
    (homogeneous.run st).2 ≤ (queryConstant + 200) * (2 ^ t + Nat.size r + 5) ^ 8 := by
  have hcost := homogeneousPrepare_cost w st hw
  have hp := homogeneousPrepare_run w st hw
  have hs20 := run_regs_frame homogeneousPrepare 20 (by decide) st
  have hs56 := run_regs_frame homogeneousPrepare 56 (by decide) st
  have hs7 := run_lists_frame homogeneousPrepare 7 (by decide) st
  simp only [homogeneous, run_seq_snd]
  generalize hs : (homogeneousPrepare.run st).1 = s at *
  have hembed := BooleanLabelTransform.embed_cost
    (BooleanCoefficientArithmetic.homogeneousIndex (by decide : 1 ≤ 1) w)
    s (hs20.trans ht) hp.2 (hs56.trans hd) (hs7.trans he) hp.1
  have hb : 2 ^ t + Nat.size 1 + Nat.size 1 + Nat.size r + 3 =
      2 ^ t + Nat.size r + 5 := by simp only [Nat.size_one]; omega
  rw [hb] at hembed
  have htq := (Nat.lt_two_pow_self (n := t)).le
  have hlow : t + 5 ≤ (2 ^ t + Nat.size r + 5) ^ 8 :=
    (by omega : t + 5 ≤ 2 ^ t + Nat.size r + 5).trans (Nat.le_pow (by decide))
  nlinarith only [hcost, hembed, hlow]

theorem constantPrepare_cost (z : ZMod 2) (st : State 57 20)
    (hz : st.regs 51 = z.val) (he : st.lists 7 = []) :
    (constantPrepare.run st).2 ≤ 8 := by
  have hs := size_le_one_of_le_one (Nat.le_of_lt_succ (ZMod.val_lt z))
  simp only [constantPrepare, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    setList_regs, setList_lists, Function.update, dite_true, Nat.size_zero, hz, he,
    listSize, List.map_nil, List.sum_nil]
  omega

theorem constant_cost (z : ZMod 2) (st : State 57 20)
    (ht : st.regs 20 = t) (hd : st.regs 56 = r) (hz : st.regs 51 = z.val)
    (he : st.lists 7 = []) :
    (constant.run st).2 ≤ (queryConstant + 200) * (2 ^ t + Nat.size r + 3) ^ 8 := by
  have hcost := constantPrepare_cost z st hz he
  have hp := constantPrepare_run (t := t) z st hz he
  have hs20 := run_regs_frame constantPrepare 20 (by decide) st
  have hs56 := run_regs_frame constantPrepare 56 (by decide) st
  have hs7 := run_lists_frame constantPrepare 7 (by decide) st
  simp only [constant, run_seq_snd]
  generalize hs : (constantPrepare.run st).1 = s at *
  have hembed := BooleanLabelTransform.embed_cost
    (BooleanCoefficientArithmetic.constant (t := t) (r := 0) z)
    s (hs20.trans ht) hp.2 (hs56.trans hd) (hs7.trans he) hp.1
  simp only [Nat.size_zero, Nat.add_zero] at hembed
  have hpos : 1 ≤ (2 ^ t + Nat.size r + 3) ^ 8 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  nlinarith only [hcost, hembed, hpos]

end PCP.Lang.BooleanLabelConstructors
