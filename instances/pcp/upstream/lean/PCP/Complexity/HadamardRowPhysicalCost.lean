/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowPhysical

/-!
# Charged cost of global Hadamard row addresses

Address arithmetic is charged by the component and result bit lengths. The map
loop traverses stored label codes and retains both global answer-history lists.
-/

set_option maxRecDepth 4096

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace HadamardLabel

def addressConstant : ℕ :=
  QueryAddress.program.C * (QueryAddress.program.width + QueryAddress.program.csize + 1) + 2

theorem addressProgram_stack (st : State 100 32) :
    (addressProgram.run st).1.lists 27 = st.lists 27 := by
  have h := congrArg (fun a : State 14 2 × ℕ => a.1.lists 1)
    (QueryAddress.program.run_rename addressRegs addressLists addressRegs_injective
      addressLists_injective st)
  have hh := h.trans (QueryAddress.program_frame (st.restrict addressRegs addressLists)).2.2
  unfold addressProgram
  simpa only [State.restrict_lists, show addressLists 1 = (27 : Fin 32) from rfl] using hh

theorem addressEmit_stack (st : State 100 32) :
    (addressEmit.run st).1.lists 27 = st.lists 27 := by
  simpa [addressEmit, run_seq_fst, run_push_fst, Function.update] using addressProgram_stack st

theorem addressProgram_cost (p : Fin 10 → ℕ) (z W : ℕ) (st : State 100 32)
    (hp : Payload p st) (hz : st.regs 90 = z) (hps : ∀ i, Nat.size (p i) ≤ W)
    (hzs : Nat.size z ≤ W) (hs : listSize (st.lists 27) ≤ W) :
    (addressProgram.run st).2 ≤ (addressConstant - 2) * (W + 1) := by
  rw [addressProgram, Stmt.run_rename_cost QueryAddress.program addressRegs addressLists
    addressRegs_injective addressLists_injective]
  apply QueryAddress.program_cost_state (st.restrict addressRegs addressLists) W
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hz ▸ hzs
    · have hi : addressRegs (Fin.castAdd 3 j.castSucc) = payloadReg j := by
        apply Fin.ext
        rfl
      simpa only [State.restrict_regs, hi, hp j] using hps j
  · exact hs

theorem addressEmit_cost (p : Fin 10 → ℕ) (z W : ℕ) (st : State 100 32)
    (hp : Payload p st) (hz : st.regs 90 = z) (hps : ∀ i, Nat.size (p i) ≤ W)
    (hzs : Nat.size z ≤ W) (hs : listSize (st.lists 27) ≤ W)
    (ha : Nat.size (address p z) ≤ W) :
    (addressEmit.run st).2 ≤ addressConstant * (W + 1) := by
  have hc := addressProgram_cost p z W st hp hz hps hzs hs
  have ho := addressProgram_run p z st hp hz
  simp only [addressEmit, run_seq_snd, run_push_snd, ho]
  unfold addressConstant at *
  simp only [Nat.add_sub_cancel] at hc
  nlinarith only [hc, ha]

theorem addressBody_stack (st : State 100 32) (z : ℕ) (zs : List ℕ)
    (hz : st.lists 25 = z :: zs) :
    (addressBody.run st).1.lists 27 = st.lists 27 := by
  rw [addressBody, run_seq_fst, run_pop_cons_fst st 25 90 95 hz, addressEmit_stack]
  simp [Function.update]

theorem addressBody_cost (p : Fin 10 → ℕ) (z W : ℕ) (zs : List ℕ) (st : State 100 32)
    (hp : Payload p st) (hz : st.lists 25 = z :: zs) (hps : ∀ i, Nat.size (p i) ≤ W)
    (hzs : Nat.size z ≤ W) (hs : listSize (st.lists 27) ≤ W)
    (ha : Nat.size (address p z) ≤ W) :
    (addressBody.run st).2 ≤ (addressConstant + 2) * (W + 1) := by
  let u := setReg (setReg (setList st 25 zs) 90 z) 95 1
  have hu : Payload p u := by
    intro i
    have h90 : payloadReg i ≠ 90 := by
      intro h; have hh := congrArg Fin.val h; dsimp [payloadReg] at hh; omega
    have h95 : payloadReg i ≠ 95 := by
      intro h; have hh := congrArg Fin.val h; dsimp [payloadReg] at hh; omega
    simpa [u, h90, h95] using hp i
  have hc := addressEmit_cost p z W u hu (by simp [u, Function.update]) hps hzs
    (by simpa [u, Function.update] using hs) ha
  dsimp only [u] at hc
  have hpop : ((Stmt.pop 25 90 95).run st).2 = Nat.size z + 1 := by
    simp only [Stmt.run, hz]
  simp only [addressBody, run_seq_snd, run_pop_cons_fst st 25 90 95 hz, hpop]
  nlinarith only [hc, hzs]

theorem address_iterate_cost (p : Fin 10 → ℕ) (zs : List ℕ) (c W : ℕ) (st : State 100 32)
    (hp : Payload p st) (hz : st.lists 25 = zs) (hps : ∀ i, Nat.size (p i) ≤ W)
    (hzs : ∀ z ∈ zs, Nat.size z ≤ W) (hs : listSize (st.lists 27) ≤ W)
    (ha : ∀ z ∈ zs, Nat.size (address p z) ≤ W) :
    (iterate addressBody.run c zs.length st).2 ≤
      zs.length * (c + (addressConstant + 2) * (W + 1)) := by
  induction zs generalizing st with
  | nil => simp [iterate]
  | cons z zs ih =>
      have hstep := addressBody_step p z zs st hp hz
      have hstack := addressBody_stack st z zs hz
      have hc := addressBody_cost p z W zs st hp hz hps (hzs z (by simp)) hs (ha z (by simp))
      have hh := ih (addressBody.run st).1 hstep.1 hstep.2.1
        (fun y hy => hzs y (by simp [hy])) (hstack ▸ hs) (fun y hy => ha y (by simp [hy]))
      simp only [List.length_cons, iterate, Nat.succ_mul]
      nlinarith only [hc, hh]

/-- Bit-size accounting for a stored natural list. -/
theorem listSize_bounded (zs : List ℕ) (W : ℕ) (h : ∀ z ∈ zs, Nat.size z ≤ W) :
    listSize zs ≤ zs.length * (W + 1) := by
  induction zs with
  | nil => simp [listSize]
  | cons z zs ih =>
      have hhead := h z (by simp)
      have htail := ih (fun y hy => h y (by simp [hy]))
      simp only [listSize, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      change Nat.size z + 1 + listSize zs ≤ _
      omega

theorem physicalQueries_cost (p : Fin 10 → ℕ) (zs : List ℕ) (W : ℕ) (st : State 100 32)
    (hp : Payload p st) (hz : st.lists 24 = zs) (he : st.lists 7 = [])
    (hps : ∀ i, Nat.size (p i) ≤ W) (hzs : ∀ z ∈ zs, Nat.size z ≤ W)
    (hs : listSize (st.lists 27) ≤ W) (ha : ∀ z ∈ zs, Nat.size (address p z) ≤ W) :
    (physicalQueries.run st).2 ≤ (addressConstant + 20) * (zs.length + W + 1) ^ 2 := by
  let u := setReg (setList (setList st 26 []) 25 zs) 94 zs.length
  have hu : Payload p u := by
    intro i
    have hi : payloadReg i ≠ 94 := by
      intro h; have hh := congrArg Fin.val h; dsimp [payloadReg] at hh; omega
    simpa [u, hi] using hp i
  have hc := address_iterate_cost p zs (Nat.size zs.length + 1) W u hu (by simp [u])
    hps hzs (by simpa [u, Function.update] using hs) ha
  have hh := address_iterate p zs (Nat.size zs.length + 1) u hu (by simp [u])
  have hzsize := listSize_bounded zs W hzs
  have hasize : listSize (zs.map (address p)) ≤ zs.length * (W + 1) := by
    simpa only [List.length_map] using listSize_bounded (zs.map (address p)) W (by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact ha y hy)
  have hlen := size_le_self zs.length
  simp only [physicalQueries, run_seq_snd, run_copy_snd, run_copy_fst,
    run_len_snd, run_len_fst, run_loop_snd, run_loop_fst, setReg_regs, setList_regs,
    setList_lists, Function.update, Fin.reduceEq, dite_false, dite_true, he, hz]
  change (listSize [] + 1) + ((listSize zs + 1) +
    ((listSize zs + Nat.size zs.length + 1) +
      (((iterate addressBody.run (Nat.size zs.length + 1) zs.length u).2 +
        Nat.size zs.length + 1) +
          ((Stmt.rev 26).run (iterate addressBody.run
            (Nat.size zs.length + 1) zs.length u).1).2 + 1) + 1) + 1) + 1 ≤ _
  generalize hv : (iterate addressBody.run (Nat.size zs.length + 1) zs.length u).1 = v at *
  have houtput : listSize (v.lists 26) ≤ zs.length * (W + 1) := by
    simpa [hh.2, u, Function.update, listSize_reverse] using hasize
  simp only [run_rev_snd, listSize, List.map_nil, List.sum_nil]
  change 0 + 1 + ((listSize zs + 1) + ((listSize zs + Nat.size zs.length + 1) +
    (((iterate addressBody.run (Nat.size zs.length + 1) zs.length u).2 +
      Nat.size zs.length + 1) + (listSize (v.lists 26) + 1) + 1) + 1) + 1) + 1 ≤ _
  nlinarith only [hc, hzsize, houtput, hlen,
    Nat.zero_le (addressConstant * zs.length ^ 2), Nat.zero_le (addressConstant * W ^ 2)]

end PCP.Lang.HadamardRow
