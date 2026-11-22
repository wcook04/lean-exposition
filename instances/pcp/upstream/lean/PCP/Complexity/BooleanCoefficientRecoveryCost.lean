/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientRecoveryLang

/-!
# Polynomial charged cost for stored coefficient recovery

Every requested support invokes the proved coefficient evaluator. The cost
includes source copies, both nested list traversals, and output reversal.
-/

namespace PCP.Lang.BooleanCoefficientRecoveryLang

open BooleanCoefficientList BooleanCoefficientEvaluation

theorem popMask_cost (st : State 16 8) :
    (popMask.run st).2 = Nat.size ((st.lists 6).headD 0) + 1 := by
  cases h : st.lists 6 <;> simp [popMask, Stmt.run, h]

theorem body_cost (st : State 16 8) (t A B D C : ℕ)
    (ht : st.regs 0 = t) (ha : listSize (st.lists 0) = A)
    (hb : listSize (st.lists 1) = B) (hd : (st.lists 0).length = D)
    (hc : listSize (st.lists 6) ≤ C) (hbits : ∀ c ∈ st.lists 1, c < 2) :
    (body.run st).2 ≤ (BooleanMaskSubset.passConstant + 210) * (t + A + B + D + C + 5) ^ 3 := by
  have hp := popMask_step st
  have hpop := popMask_cost st
  have hhead := (headD_size (st.lists 6)).trans hc
  have hp0 := run_regs_frame popMask 0 (by decide) st
  have hpl0 := run_lists_frame popMask 0 (by decide) st
  have hpl1 := run_lists_frame popMask 1 (by decide) st
  simp only [body, run_seq_snd]
  generalize hps : (popMask.run st).1 = s at *
  have heval : (eval16.run s).2 ≤ (BooleanMaskSubset.passConstant + 200) *
      (t + A + B + D + C + 5) ^ 3 := by
    rw [eval16, Stmt.run_rename_cost BooleanCoefficientEvaluation.evaluate evalRegs evalLists
      (show Function.Injective evalRegs from Fin.castLE_injective _)
      (show Function.Injective evalLists from Fin.castLE_injective _)]
    have hh := evaluate_cost (s.restrict evalRegs evalLists) (by
      change ∀ c ∈ s.lists 1, c < 2
      rw [hpl1]
      exact hbits)
    change _ ≤ (BooleanMaskSubset.passConstant + 200) *
      (s.regs 0 + Nat.size (s.regs 2) + listSize (s.lists 0) + listSize (s.lists 1) +
        (s.lists 0).length + 4) ^ 3 at hh
    rw [hp0, ht, hp.1, hpl0, hpl1, ha, hb, hd] at hh
    exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  have hs10 := eval16_run s
  have hbit : Nat.size ((eval16.run s).1.regs 10) ≤ 1 := by
    rw [hs10]
    exact size_le_one_of_le_one (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 2)))
  change (popMask.run st).2 +
    ((eval16.run s).2 + (Nat.size ((eval16.run s).1.regs 10) + 1) + 1) + 1 ≤ _
  generalize hM : t + A + B + D + C + 5 = M at *
  have hl : C + 5 ≤ M ^ 3 := by
    calc
      _ ≤ M := by omega
      _ ≤ M ^ 3 := Nat.le_pow (by decide)
  nlinarith only [heval, hpop, hhead, hbit, hl]

/-- Recovery is polynomial in stored input sizes and the binary-coordinate width. -/
theorem recover_cost (st : State 16 8) (he : st.lists 7 = [])
    (hbits : ∀ c ∈ st.lists 1, c < 2) :
    (recover.run st).2 ≤ (BooleanMaskSubset.passConstant + 300) *
      (st.regs 0 + listSize (st.lists 0) + listSize (st.lists 1) +
        (st.lists 0).length + listSize (st.lists 4) + (st.lists 4).length + 5) ^ 4 := by
  let t := st.regs 0
  let A := listSize (st.lists 0)
  let B := listSize (st.lists 1)
  let D := (st.lists 0).length
  let C := listSize (st.lists 4)
  let n := (st.lists 4).length
  let M := t + A + B + D + C + n + 5
  let K := BooleanMaskSubset.passConstant + 210
  let s := setReg (setList (setList st 6 (st.lists 4)) 5 []) 15 n
  let Inv := fun j (u : State 16 8) => u.regs 0 = t ∧ u.lists 0 = st.lists 0 ∧
    u.lists 1 = st.lists 1 ∧ listSize (u.lists 6) ≤ C ∧ listSize (u.lists 5) ≤ 2 * j
  have hinit : Inv 0 s := by simp [Inv, s, t, C, Function.update, listSize]
  have hstep : ∀ j u, j < n → Inv j u → Inv (j + 1) (body.run u).1 := by
    intro j u _ hu
    have hh := body_step u
    refine ⟨(body_width u).trans hu.1,
      (body_source u 0 (Or.inl rfl)).trans hu.2.1,
      (body_source u 1 (Or.inr rfl)).trans hu.2.2.1, ?_, ?_⟩
    · rw [hh.2]
      exact (tail_size _).trans hu.2.2.2.1
    · rw [hh.1]
      have hb := size_le_one_of_le_one
        (Nat.le_of_lt_succ (Nat.mod_lt (terms (u.regs 0) ((u.lists 6).headD 0)
          (u.lists 0) (u.lists 1)) (by decide : 0 < 2)))
      change Nat.size (terms (u.regs 0) ((u.lists 6).headD 0)
        (u.lists 0) (u.lists 1) % 2) + 1 + listSize (u.lists 5) ≤ 2 * (j + 1)
      change Nat.size (terms (u.regs 0) ((u.lists 6).headD 0)
        (u.lists 0) (u.lists 1) % 2) ≤ 1 at hb
      have hprev := hu.2.2.2.2
      omega
  have hit := iterate_cost_idx body.run (Nat.size n + 1) (K * M ^ 3) n Inv
    (by
      intro j u hj hu
      refine ⟨hstep j u hj hu, ?_⟩
      have hh := body_cost u t A B D C hu.1 (by rw [hu.2.1])
        (by rw [hu.2.2.1]) (by rw [hu.2.1]) hu.2.2.2.1
        (by rw [hu.2.2.1]; exact hbits)
      exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [M]; omega) 3)))
    s hinit
  have hout := iterate_inv body.run (Nat.size n + 1) n Inv hstep s hinit
  have hsz : Nat.size n ≤ n := size_le_self _
  have hnM : n ≤ M := by dsimp [M]; omega
  have hit' : (iterate body.run (Nat.size n + 1) n s).2 ≤ M * (M + 1 + K * M ^ 3) :=
    hit.trans (Nat.mul_le_mul hnM (Nat.add_le_add_right (by omega) _))
  simp only [recover, run_seq_snd, run_copy_snd, run_copy_fst, run_len_snd, run_len_fst,
    run_loop_snd, run_loop_fst, run_rev_snd, setReg_regs, setList_regs,
    setList_lists, Function.update, Fin.reduceEq, dite_true, dite_false, he]
  change (C + 1) + ((listSize ([] : List ℕ) + 1) + ((C + Nat.size n + 1) +
    (((iterate body.run (Nat.size n + 1) n s).2 + Nat.size n + 1) +
      (listSize ((iterate body.run (Nat.size n + 1) n s).1.lists 5) + 1) + 1) + 1) + 1) + 1 ≤ _
  rw [show listSize ([] : List ℕ) = 0 from rfl]
  change _ ≤ (K + 90) * M ^ 4
  have hM : t + A + B + D + C + n + 5 = M := rfl
  nlinarith [hout.2.2.2.2, Nat.zero_le (M ^ 4), Nat.zero_le (M ^ 3), Nat.zero_le (M ^ 2)]

end PCP.Lang.BooleanCoefficientRecoveryLang
