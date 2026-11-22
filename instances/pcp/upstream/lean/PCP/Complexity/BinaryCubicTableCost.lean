/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryCubicTable

/-!
# Polynomial charged cost of the concrete cubic truth table

The degree-seven domain-size bound includes all field arithmetic, stored affine
observations, numeric loop control, emitted bits, and final list reversal.
-/

namespace PCP.Lang.BinaryCubicTable

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BinaryFieldCode
open BinaryCubicObservation

variable {t : ℕ} [NeZero t]

theorem fieldKernel_cost (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 54 17) (hc : Context w L st)
    (hj : st.regs 24 < 2 ^ t) :
    ((fieldKernel weighted).run st).2 ≤ observationConstant * (2 ^ t + 3) ^ 6 := by
  rw [fieldKernel, Stmt.run_rename_cost (kernel weighted) kernelRegs kernelLists
    (show Function.Injective kernelRegs from Fin.castLE_injective _)
    (show Function.Injective kernelLists from Fin.castLE_injective _)]
  exact kernel_cost weighted ((fieldEquiv t).symm ⟨st.regs 24, hj⟩) w L
    (st.restrict kernelRegs kernelLists) hc.1 (by simp [State.restrict, kernelRegs])
    hc.2.1 hc.2.2.1 hc.2.2.2.1
    hc.2.2.2.2.1 hc.2.2.2.2.2.1

theorem body_cost (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 54 17) (hc : Context w L st)
    (hj : st.regs 24 < 2 ^ t) :
    ((body weighted).run st).2 ≤ (observationConstant + 10) * (2 ^ t + 3) ^ 6 := by
  have hk := fieldKernel_cost weighted w L st hc hj
  have hr := fieldKernel_run weighted w L st hc hj
  have hs24 := fieldKernel_source weighted st
  have hs53 := fieldKernel_reg weighted st 53 (by decide)
  have hsize : Nat.size (st.regs 24) ≤ t := Nat.size_le.mpr hj
  have hnext : Nat.size (st.regs 24 + 1) ≤ t + 1 := by
    apply Nat.size_le.mpr
    have hle := Nat.succ_le_of_lt hj
    have hq : 0 < 2 ^ t := by positivity
    rw [pow_succ]
    omega
  have hbit : Nat.size (numericValue weighted w L (st.regs 24)) ≤ 1 :=
    size_le_one_of_le_one (Nat.le_of_lt_succ (numericValue_bit weighted w L _))
  simp only [body, run_seq_snd]
  generalize hs : ((fieldKernel weighted).run st).1 = s at *
  change ((fieldKernel weighted).run st).2 +
    ((Nat.size (s.regs 46) + 1) +
      (Expr.add 24 53).cost (setList s 16 (s.regs 46 :: s.lists 16)).regs + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setList_regs, hr, hs24, hs53,
    hc.2.2.2.2.2.2.2, Nat.size_one]
  have htq := (Nat.lt_two_pow_self (n := t)).le
  have hlow : t + 3 ≤ (2 ^ t + 3) ^ 6 :=
    (Nat.add_le_add_right htq 3).trans (Nat.le_pow (by decide))
  nlinarith only [hk, hsize, hnext, hbit, hlow]

theorem tabulate_cost (weighted : Bool) (w : BinaryMaterializedField.Element t)
    (L : Coefficients t 1) (st : State 54 17) (hc : Context w L st) :
    ((tabulate weighted).run st).2 ≤ (observationConstant + 40) * (2 ^ t + 3) ^ 7 := by
  let q := 2 ^ t
  let K := observationConstant + 10
  let s := setReg (setReg (setList st 16 []) 24 0) 53 1
  let Inv := fun j (u : State 54 17) => Context w L u ∧ u.regs 24 = j ∧
    listSize (u.lists 16) ≤ 2 * j
  have hinit : Inv 0 s := by
    simp [Inv, Context, s, Function.update, listSize, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
      hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1]
  have hstep : ∀ j u, j < q → Inv j u → Inv (j + 1) ((body weighted).run u).1 := by
    intro j u hj hu
    have hh := body_step weighted w L u hu.1 (by rw [hu.2.1]; exact hj)
    refine ⟨body_context weighted w L u hu.1, hh.1.trans (by rw [hu.2.1]), ?_⟩
    rw [hh.2]
    have hb : Nat.size (numericValue weighted w L (u.regs 24)) ≤ 1 :=
      size_le_one_of_le_one (Nat.le_of_lt_succ (numericValue_bit weighted w L _))
    change Nat.size (numericValue weighted w L (u.regs 24)) + 1 + listSize (u.lists 16) ≤ _
    have hp := hu.2.2
    omega
  have hit := iterate_cost_idx (body weighted).run (Nat.size q + 1) (K * (q + 3) ^ 6) q Inv
    (by
      intro j u hj hu
      exact ⟨hstep j u hj hu, body_cost weighted w L u hu.1 (by rw [hu.2.1]; exact hj)⟩)
    s hinit
  have hout := iterate_inv (body weighted).run (Nat.size q + 1) q Inv hstep s hinit
  have hsz : Nat.size q ≤ q := size_le_self _
  have hit' : (iterate (body weighted).run (Nat.size q + 1) q s).2 ≤
      (q + 3) * (q + 3 + K * (q + 3) ^ 6) := hit.trans
    (Nat.mul_le_mul (by omega) (Nat.add_le_add_right (by omega) _))
  simp only [tabulate, run_seq_snd, run_copy_snd, run_copy_fst, run_assign_fst, Expr.eval,
    run_loop_snd, run_loop_fst, run_rev_snd, setReg_regs, setList_regs,
    Function.update, Fin.reduceEq, dite_false, hc.2.2.2.1, hc.2.2.2.2.2.2.1]
  change (listSize ([] : List ℕ) + 1) + ((Expr.const 0).cost _ + ((Expr.const 1).cost _ +
    (((iterate (body weighted).run (Nat.size q + 1) q s).2 + Nat.size q + 1) +
      (listSize ((iterate (body weighted).run (Nat.size q + 1) q s).1.lists 16) + 1) + 1) + 1)
      + 1) + 1 ≤ _
  simp only [show listSize ([] : List ℕ) = 0 from rfl,
    Expr.cost, Expr.readSize, Expr.eval, Nat.size_zero, Nat.size_one]
  change _ ≤ (K + 30) * (q + 3) ^ 7
  have hpow : (q + 3) ^ 2 ≤ (q + 3) ^ 7 := Nat.pow_le_pow_right (by omega) (by decide)
  have hlow : q + 3 ≤ (q + 3) ^ 7 := Nat.le_pow (by decide)
  nlinarith only [hit', hout.2.2, hsz, hpow, hlow]

end PCP.Lang.BinaryCubicTable
