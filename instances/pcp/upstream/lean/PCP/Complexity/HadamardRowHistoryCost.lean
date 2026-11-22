/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowHistory
import PCP.Complexity.HadamardRowPhysicalCost

/-!
# Charged cost of collecting a row's received answers

The bound includes actual scans through both global history sources. It permits
arbitrary repeated addresses, missing answers, and initial scratch contents.
-/

namespace PCP.Lang.HadamardRow

theorem historyRead_size (qs bs : List ℕ) (a : ℕ) :
    Nat.size (QueryHistory.read qs bs a) ≤ listSize bs := by
  induction qs generalizing bs with
  | nil => simp [QueryHistory.read]
  | cons q qs ih =>
      cases bs with
      | nil => simp [QueryHistory.read]
      | cons b bs =>
          have hb := ih bs
          simp only [QueryHistory.read]
          split
          · simp only [listSize, List.map_cons, List.sum_cons]; omega
          · simp only [listSize, List.map_cons, List.sum_cons] at hb ⊢; omega

theorem readHistory_cost (st : State 100 32) :
    (readHistory.run st).2 ≤ (QueryHistory.passConstant + 20) *
      (listSize (st.lists 30) + listSize (st.lists 31) + Nat.size (st.regs 66) + 2) ^ 2 := by
  rw [readHistory, Stmt.run_rename_cost QueryHistory.program historyRegs historyLists
    historyRegs_injective historyLists_injective]
  exact QueryHistory.program_cost (st.restrict historyRegs historyLists)

def answerBodyConstant : ℕ := 9 * (QueryHistory.passConstant + 20) + 5

theorem answerBody_cost (z : ℕ) (zs : List ℕ) (W : ℕ) (st : State 100 32)
    (hz : st.lists 25 = z :: zs) (ha : Nat.size z ≤ W)
    (hq : listSize (st.lists 30) ≤ W) (hb : listSize (st.lists 31) ≤ W) :
    (answerBody.run st).2 ≤ answerBodyConstant * (W + 1) ^ 2 := by
  let u := setReg (setReg (setList st 25 zs) 66 z) 65 1
  have hc := readHistory_cost u
  have ho := readHistory_run u
  dsimp only [u] at hc ho
  have hpop : ((Stmt.pop 25 66 65).run st).2 = Nat.size z + 1 := by
    simp only [Stmt.run, hz]
  simp only [answerBody, run_seq_snd, run_pop_cons_fst st 25 66 65 hz, hpop]
  generalize hv : (readHistory.run (setReg (setReg (setList st 25 zs) 66 z) 65 1)).1 = v at *
  have hc' : (readHistory.run (setReg (setReg (setList st 25 zs) 66 z) 65 1)).2 ≤
      9 * (QueryHistory.passConstant + 20) * (W + 1) ^ 2 := by
    simp only [setReg_regs, setReg_lists, setList_lists, Function.update, Fin.reduceEq,
      dite_false, dite_true] at hc
    calc
      _ ≤ (QueryHistory.passConstant + 20) * (3 * (W + 1)) ^ 2 :=
        hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      _ = _ := by ring
  have hread : Nat.size (v.regs 68) ≤ W := by
    simpa [ho, Function.update] using (historyRead_size (st.lists 30) (st.lists 31) z).trans hb
  simp only [run_push_snd]
  unfold answerBodyConstant
  nlinarith only [hc', hread, ha, Nat.zero_le (W ^ 2)]

theorem answer_iterate_cost (zs : List ℕ) (c W : ℕ) (st : State 100 32)
    (hz : st.lists 25 = zs) (ha : ∀ z ∈ zs, Nat.size z ≤ W)
    (hq : listSize (st.lists 30) ≤ W) (hb : listSize (st.lists 31) ≤ W) :
    (iterate answerBody.run c zs.length st).2 ≤
      zs.length * (c + answerBodyConstant * (W + 1) ^ 2) := by
  induction zs generalizing st with
  | nil => simp [iterate]
  | cons z zs ih =>
      have hstep := answerBody_step z zs st hz
      have hframe := answerBody_sources st
      have hc := answerBody_cost z zs W st hz (ha z (by simp)) hq hb
      have hh := ih (answerBody.run st).1 hstep.1 (fun y hy => ha y (by simp [hy]))
        (hframe.1 ▸ hq) (hframe.2 ▸ hb)
      simp only [List.length_cons, iterate, Nat.succ_mul]
      nlinarith only [hc, hh]

theorem collectAnswers_cost (zs : List ℕ) (W : ℕ) (st : State 100 32)
    (hz : st.lists 26 = zs) (he : st.lists 7 = [])
    (ha : ∀ z ∈ zs, Nat.size z ≤ W)
    (hq : listSize (st.lists 30) ≤ W) (hb : listSize (st.lists 31) ≤ W) :
    (collectAnswers.run st).2 ≤ (answerBodyConstant + 20) * (zs.length + W + 1) ^ 3 := by
  let u := setReg (setList (setList st 29 []) 25 zs) 58 zs.length
  have hc := answer_iterate_cost zs (Nat.size zs.length + 1) W u (by simp [u]) ha
    (by simpa [u, Function.update] using hq) (by simpa [u, Function.update] using hb)
  have hh := answer_iterate zs (Nat.size zs.length + 1) u (by simp [u])
  have hzsize := listSize_bounded zs W ha
  have hasize : listSize (zs.map (QueryHistory.read (st.lists 30) (st.lists 31))) ≤
      zs.length * (W + 1) := by
    simpa only [List.length_map] using listSize_bounded
      (zs.map (QueryHistory.read (st.lists 30) (st.lists 31))) W (by
        intro z hz
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hz
        exact (historyRead_size _ _ y).trans hb)
  have hlen := size_le_self zs.length
  simp only [collectAnswers, run_seq_snd, run_copy_snd, run_copy_fst,
    run_len_snd, run_len_fst, run_loop_snd, run_loop_fst, setReg_regs, setList_regs,
    setList_lists, Function.update, Fin.reduceEq, dite_false, dite_true, he, hz]
  change (listSize [] + 1) + ((listSize zs + 1) +
    ((listSize zs + Nat.size zs.length + 1) +
      (((iterate answerBody.run (Nat.size zs.length + 1) zs.length u).2 +
        Nat.size zs.length + 1) +
          ((Stmt.rev 29).run (iterate answerBody.run
            (Nat.size zs.length + 1) zs.length u).1).2 + 1) + 1) + 1) + 1 ≤ _
  generalize hv : (iterate answerBody.run (Nat.size zs.length + 1) zs.length u).1 = v at *
  have houtput : listSize (v.lists 29) ≤ zs.length * (W + 1) := by
    simpa [hh, u, Function.update, listSize_reverse] using hasize
  simp only [run_rev_snd, listSize, List.map_nil, List.sum_nil]
  change 0 + 1 + ((listSize zs + 1) + ((listSize zs + Nat.size zs.length + 1) +
    (((iterate answerBody.run (Nat.size zs.length + 1) zs.length u).2 +
      Nat.size zs.length + 1) + (listSize (v.lists 29) + 1) + 1) + 1) + 1) + 1 ≤ _
  have hprod : zs.length * (W + 1) ^ 2 ≤ (zs.length + W + 1) ^ 3 := by
    calc
      _ ≤ (zs.length + W + 1) * (zs.length + W + 1) ^ 2 :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by ring
  have hmult := Nat.mul_le_mul_left answerBodyConstant hprod
  have hsmall : (zs.length + W + 1) ^ 2 ≤ (zs.length + W + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le _)) (by decide)
  nlinarith only [hc, hzsize, houtput, hlen, hmult, hsmall,
    Nat.zero_le (zs.length ^ 2), Nat.zero_le (W ^ 2)]

end PCP.Lang.HadamardRow
