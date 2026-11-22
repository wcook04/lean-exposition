/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanLabelTable

/-!
# Charged cost of Boolean label truth tables

The degree-seven bound includes numeric point enumeration, both stored source
observations, and materialization of the truth table.
-/

namespace PCP.Lang.BooleanLabelTable

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList BooleanLabelKernel

variable {t a b : ℕ}

theorem body_cost (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (st : State 57 20) (hc : Context p q st) (hj : st.regs 24 < 2 ^ t) :
    ((body product).run st).2 ≤ (kernelConstant + 10) * (2 ^ t + 3) ^ 6 := by
  have hk := kernel_cost product p q ⟨st.regs 24, hj⟩ st hc.1 rfl
  have hr := kernel_run product p q ⟨st.regs 24, hj⟩ st hc.1 rfl
  have hs24 := kernel_reg product st 24 (by decide)
  have hs53 := kernel_reg product st 53 (by decide)
  have hsize : Nat.size (st.regs 24) ≤ t := Nat.size_le.mpr hj
  have hnext : Nat.size (st.regs 24 + 1) ≤ t + 1 := by
    apply Nat.size_le.mpr
    have hle := Nat.succ_le_of_lt hj
    have hq : 0 < 2 ^ t := by positivity
    rw [pow_succ]
    omega
  have hbit : Nat.size (function product p q (point t ⟨st.regs 24, hj⟩)).val ≤ 1 :=
    size_le_one_of_le_one (Nat.le_of_lt_succ (ZMod.val_lt _))
  simp only [body, run_seq_snd]
  generalize hs : ((kernel product).run st).1 = s at *
  change ((kernel product).run st).2 + ((Nat.size (s.regs 46) + 1) +
    (Expr.add 24 53).cost (setList s 16 (s.regs 46 :: s.lists 16)).regs + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, setList_regs, hr, hs24, hs53,
    hc.2.2.1, Nat.size_one]
  have htq := (Nat.lt_two_pow_self (n := t)).le
  have hlow : t + 3 ≤ (2 ^ t + 3) ^ 6 :=
    (Nat.add_le_add_right htq 3).trans (Nat.le_pow (by decide))
  nlinarith only [hk, hsize, hnext, hbit, hlow]

theorem tabulate_cost (product : Bool) (p : Coefficients t a) (q : Coefficients t b)
    (st : State 57 20) (hc : Context p q st) :
    ((tabulate product).run st).2 ≤ (kernelConstant + 40) * (2 ^ t + 3) ^ 7 := by
  let N := 2 ^ t
  let K := kernelConstant + 10
  let s := setReg (setList st 16 []) 24 0
  let Inv := fun j (u : State 57 20) => Context p q u ∧ u.regs 24 = j ∧
    listSize (u.lists 16) ≤ 2 * j
  have hinit : Inv 0 s := by
    simp [Inv, Context, BooleanLabelKernel.Context, s, Function.update, listSize,
      hc.1.1, hc.1.2.1, hc.1.2.2.1, hc.1.2.2.2.1, hc.1.2.2.2.2,
      hc.2.1, hc.2.2.1, hc.2.2.2]
  have hstep : ∀ j u, j < N → Inv j u → Inv (j + 1) ((body product).run u).1 := by
    intro j u hj hu
    have hh := body_step product p q u hu.1 (by rw [hu.2.1]; exact hj)
    refine ⟨body_context product p q u hu.1, hh.1.trans (by rw [hu.2.1]), ?_⟩
    rw [hh.2]
    have hb : Nat.size (value product p q (u.regs 24)) ≤ 1 :=
      size_le_one_of_le_one (Nat.le_of_lt_succ (value_lt_two product p q _))
    change Nat.size (value product p q (u.regs 24)) + 1 + listSize (u.lists 16) ≤ _
    have hp := hu.2.2
    omega
  have hit := iterate_cost_idx (body product).run (Nat.size N + 1) (K * (N + 3) ^ 6) N Inv
    (by
      intro j u hj hu
      exact ⟨hstep j u hj hu, body_cost product p q u hu.1 (by rw [hu.2.1]; exact hj)⟩)
    s hinit
  have hout := iterate_inv (body product).run (Nat.size N + 1) N Inv hstep s hinit
  have hsz : Nat.size N ≤ N := size_le_self _
  have hit' : (iterate (body product).run (Nat.size N + 1) N s).2 ≤
      (N + 3) * (N + 3 + K * (N + 3) ^ 6) := hit.trans
    (Nat.mul_le_mul (by omega) (Nat.add_le_add_right (by omega) _))
  simp only [tabulate, run_seq_snd, run_copy_snd, run_copy_fst, run_assign_fst, Expr.eval,
    run_loop_snd, run_loop_fst, run_rev_snd, setReg_regs, setList_regs,
    Function.update, Fin.reduceEq, dite_false, hc.2.1, hc.2.2.2]
  change (listSize ([] : List ℕ) + 1) + ((Expr.const 0).cost _ +
    (((iterate (body product).run (Nat.size N + 1) N s).2 + Nat.size N + 1) +
      (listSize ((iterate (body product).run (Nat.size N + 1) N s).1.lists 16) + 1) + 1) + 1) +
    1 ≤ _
  simp only [show listSize ([] : List ℕ) = 0 from rfl,
    Expr.cost, Expr.readSize, Expr.eval, Nat.size_zero]
  change _ ≤ (K + 30) * (N + 3) ^ 7
  have hpow : (N + 3) ^ 2 ≤ (N + 3) ^ 7 := Nat.pow_le_pow_right (by omega) (by decide)
  have hlow : N + 3 ≤ (N + 3) ^ 7 := Nat.le_pow (by decide)
  nlinarith only [hit', hout.2.2, hsz, hpow, hlow]

end PCP.Lang.BooleanLabelTable
