/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientEvaluation

/-!
# Charged cost of the stored coefficient evaluator

The bound includes copying the two inputs and traversing their stored masks.
Coefficient data are bits; masks and the point are arbitrary naturals.
-/

namespace PCP.Lang.BooleanCoefficientEvaluation

open BooleanLoops BooleanCoefficientList

theorem headD_size (xs : List ℕ) : Nat.size (xs.headD 0) ≤ listSize xs := by
  cases xs with
  | nil => simp [listSize]
  | cons x xs => exact size_le_listSize (by simp)

theorem tail_size (xs : List ℕ) : listSize xs.tail ≤ listSize xs := by
  cases xs <;> simp [listSize]

theorem headD_bit (xs : List ℕ) (h : ∀ x ∈ xs, x < 2) : xs.headD 0 ≤ 1 := by
  cases xs with
  | nil => simp
  | cons x xs => exact Nat.le_of_lt_succ (h x (by simp))

theorem popInputs_cost (st : State 15 4) :
    (popInputs.run st).2 =
      Nat.size ((st.lists 2).headD 0) + Nat.size ((st.lists 3).headD 0) + 3 := by
  cases hm : st.lists 2 <;> cases hc : st.lists 3 <;>
    simp [popInputs, Stmt.run, hm, hc, Function.update] <;> omega

theorem addTerm_cost (st : State 15 4) (n : ℕ)
    (h10 : st.regs 10 ≤ n) (h11 : st.regs 11 ≤ 1) (h3 : st.regs 3 ≤ 1) :
    (addTerm.run st).2 ≤ 10 * (n + 2) := by
  have hprod : st.regs 11 * st.regs 3 ≤ 1 := by nlinarith
  have hsprod := size_le_one_of_le_one hprod
  have hs11 := size_le_one_of_le_one h11
  have hs3 := size_le_one_of_le_one h3
  have hs10 : Nat.size (st.regs 10) ≤ n := (size_le_self _).trans h10
  have hsum : Nat.size (st.regs 10 + st.regs 11 * st.regs 3) ≤ n + 1 :=
    (size_le_self _).trans (by omega)
  simp only [addTerm, Stmt.run, Expr.cost, Expr.readSize, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false]
  omega

theorem body_cost (st : State 15 4) (t x A n : ℕ)
    (ht : st.regs 0 = t) (hx : Nat.size (st.regs 2) ≤ x)
    (hm : listSize (st.lists 2) ≤ A) (hb : ∀ c ∈ st.lists 3, c < 2)
    (ha : st.regs 10 ≤ n) :
    (body.run st).2 ≤ (BooleanMaskSubset.passConstant + 100) * (t + x + A + n + 4) ^ 2 := by
  have hp := popInputs_step st
  have hpop := popInputs_cost st
  have hhead := (headD_size (st.lists 2)).trans hm
  have hbit := headD_bit (st.lists 3) hb
  have hbitSize := size_le_one_of_le_one hbit
  have hp0 := run_regs_frame popInputs 0 (by decide) st
  have hp2 := run_regs_frame popInputs 2 (by decide) st
  have hp10 := run_regs_frame popInputs 10 (by decide) st
  simp only [body, run_seq_snd]
  generalize hps : (popInputs.run st).1 = s at *
  have hsub : (subset15.run s).2 ≤ (BooleanMaskSubset.passConstant + 30) *
      (t + A + x + 3) ^ 2 := by
    rw [subset15, Stmt.run_rename_cost BooleanMaskSubset.subset subsetRegs subsetLists
      (show Function.Injective subsetRegs from Fin.castLE_injective _)
      (show Function.Injective subsetLists from Fin.castLE_injective _)]
    have hh := BooleanMaskSubset.subset_cost (s.restrict subsetRegs subsetLists)
    change _ ≤ (BooleanMaskSubset.passConstant + 30) *
      (s.regs 0 + Nat.size (s.regs 1) + Nat.size (s.regs 2) + 3) ^ 2 at hh
    rw [hp0, ht, hp.1, hp2] at hh
    exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hs3 := subset15_run s
  have hs10 := run_regs_frame subset15 10 (by decide) s
  have hs11 := run_regs_frame subset15 11 (by decide) s
  generalize hss : (subset15.run s).1 = u at *
  have hadd := addTerm_cost u n (by rw [hs10, hp10]; exact ha)
    (by rw [hs11, hp.2.1]; exact hbit) (by rw [hs3]; exact Nat.le_of_lt_succ (truth_lt_two _))
  have hsub' : (subset15.run s).2 ≤ (BooleanMaskSubset.passConstant + 30) *
      (t + x + A + n + 4) ^ 2 :=
    hsub.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  nlinarith [Nat.zero_le (t ^ 2), Nat.zero_le (x ^ 2), Nat.zero_le (A ^ 2),
    Nat.zero_le (n ^ 2)]

/-- A cubic charged-cost bound for evaluation of stored binary coefficients. -/
theorem evaluate_cost (st : State 15 4) (hb : ∀ c ∈ st.lists 1, c < 2) :
    (evaluate.run st).2 ≤ (BooleanMaskSubset.passConstant + 200) *
      (st.regs 0 + Nat.size (st.regs 2) + listSize (st.lists 0) +
        listSize (st.lists 1) + (st.lists 0).length + 4) ^ 3 := by
  let t := st.regs 0
  let x := Nat.size (st.regs 2)
  let A := listSize (st.lists 0)
  let B := listSize (st.lists 1)
  let n := (st.lists 0).length
  let M := t + x + A + B + n + 4
  let K := BooleanMaskSubset.passConstant + 100
  let s := setReg (setReg (setReg (setList (setList st 2 (st.lists 0)) 3 (st.lists 1))
    14 n) 10 0) 13 2
  let Inv := fun j (u : State 15 4) => u.regs 0 = t ∧ Nat.size (u.regs 2) ≤ x ∧
    u.regs 13 = 2 ∧ listSize (u.lists 2) ≤ A ∧
      (∀ c ∈ u.lists 3, c < 2) ∧ u.regs 10 ≤ j
  have hinit : Inv 0 s := by
    have hbits : ∀ c ∈ st.lists 1, c ≤ 1 := fun c hc => Nat.le_of_lt_succ (hb c hc)
    simpa [Inv, s, t, x, A, Function.update] using hbits
  have hstep : ∀ j u, j < n → Inv j u → Inv (j + 1) (body.run u).1 := by
    intro j u _ hu
    have hh := body_step u
    refine ⟨(body_width u).trans hu.1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [body_point]; exact hu.2.1
    · exact (run_regs_frame body 13 (by decide) u).trans hu.2.2.1
    · rw [hh.2.1]; exact (tail_size _).trans hu.2.2.2.1
    · rw [hh.2.2]
      intro c hc
      exact hu.2.2.2.2.1 c (List.mem_of_mem_tail hc)
    · rw [hh.1]
      have hcoef := headD_bit (u.lists 3) hu.2.2.2.2.1
      have hflag := truth_lt_two (BooleanMaskSubset.Contains (u.regs 0)
        ((u.lists 2).headD 0) (u.regs 2))
      nlinarith [hu.2.2.2.2.2]
  have hit := iterate_cost_idx body.run (Nat.size n + 1) (K * M ^ 2) n Inv
    (by
      intro j u hj hu
      refine ⟨hstep j u hj hu, ?_⟩
      have hh := body_cost u t x A n hu.1 hu.2.1 hu.2.2.2.1 hu.2.2.2.2.1
        (hu.2.2.2.2.2.trans hj.le)
      exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [M]; omega) 2)))
    s hinit
  have hout := iterate_inv body.run (Nat.size n + 1) n Inv hstep s hinit
  have hfinal : (Expr.mod 10 13).cost
      (iterate body.run (Nat.size n + 1) n s).1.regs ≤ n + 4 := by
    have hacc := (size_le_self _).trans hout.2.2.2.2.2
    have hmod : Nat.size ((iterate body.run (Nat.size n + 1) n s).1.regs 10 % 2) ≤ 1 :=
      size_le_one_of_le_one (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 2)))
    simp only [Expr.cost, Expr.readSize, Expr.eval, hout.2.2.1, show Nat.size 2 = 2 from rfl]
    omega
  have hsz : Nat.size n ≤ n := size_le_self _
  have hnM : n ≤ M := by dsimp [M]; omega
  have hit' : (iterate body.run (Nat.size n + 1) n s).2 ≤
      M * (M + 1 + K * M ^ 2) := hit.trans
    (Nat.mul_le_mul hnM (Nat.add_le_add_right (by omega) _))
  simp only [evaluate, run_seq_snd, run_copy_snd, run_copy_fst, run_len_snd, run_len_fst,
    run_assign_fst, Expr.eval, run_loop_snd, run_loop_fst, setReg_regs, setList_regs,
    setList_lists, Function.update, Fin.reduceEq, dite_true, dite_false]
  change (A + 1) + ((B + 1) + ((A + Nat.size n + 1) + ((Expr.const 0).cost _ +
    ((Expr.const 2).cost _ + (((iterate body.run (Nat.size n + 1) n s).2 + Nat.size n + 1) +
      (Expr.mod 10 13).cost (iterate body.run (Nat.size n + 1) n s).1.regs + 1) + 1) + 1) + 1)
      + 1) + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval, Nat.size_zero, show Nat.size 2 = 2 from rfl]
  change _ ≤ (BooleanMaskSubset.passConstant + 200) * M ^ 3
  have hM : t + x + A + B + n + 4 = M := rfl
  change _ ≤ (K + 100) * M ^ 3
  change Nat.size ((iterate body.run (Nat.size n + 1) n s).1.regs 10) +
    Nat.size ((iterate body.run (Nat.size n + 1) n s).1.regs 13) +
    Nat.size ((iterate body.run (Nat.size n + 1) n s).1.regs 10 %
      (iterate body.run (Nat.size n + 1) n s).1.regs 13) + 1 ≤ n + 4 at hfinal
  nlinarith [Nat.zero_le (M ^ 3), Nat.zero_le (M ^ 2)]

end PCP.Lang.BooleanCoefficientEvaluation
