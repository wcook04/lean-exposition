/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowLocation

/-!
# Materializing physical addresses for a fixed Hadamard row

Registers `80` through `89` contain the fixed table and point payload. The numeric
labels in list `24` are mapped to actual global proof addresses in list `26`.
-/

set_option maxRecDepth 4096

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace HadamardLabel

/-- Address arithmetic lives above all registers used by coefficient arithmetic. -/
def addressRegs (i : Fin 14) : Fin 100 := ⟨80 + i.val, by omega⟩
def addressLists : Fin 2 → Fin 32 := ![26, 27]
def payloadReg (i : Fin 10) : Fin 100 := ⟨80 + i.val, by omega⟩

theorem addressRegs_injective : Function.Injective addressRegs := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa only [addressRegs, Nat.add_left_cancel_iff] using hv

theorem addressLists_injective : Function.Injective addressLists := by decide

def Payload (p : Fin 10 → ℕ) (st : State 100 32) : Prop :=
  ∀ i, st.regs (payloadReg i) = p i

def addressProgram : Stmt 100 32 :=
  QueryAddress.program.rename addressRegs addressLists

theorem addressProgram_run (p : Fin 10 → ℕ) (z : ℕ) (st : State 100 32)
    (hp : Payload p st) (hz : st.regs 90 = z) :
    (addressProgram.run st).1.regs 91 = address p z := by
  have h := congrArg (fun a : State 14 2 × ℕ => a.1.regs 11)
    (QueryAddress.program.run_rename addressRegs addressLists addressRegs_injective
      addressLists_injective st)
  have he : (fun i : Fin 11 => (st.restrict addressRegs addressLists).regs (i.castAdd 3)) =
      Fin.lastCases z p := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hz
    · have hi : addressRegs (Fin.castAdd 3 j.castSucc) = payloadReg j := by
        apply Fin.ext
        rfl
      simpa only [Fin.lastCases_castSucc, State.restrict_regs, hi] using hp j
  have hh := (ArithmeticExpression.scalar_spec QueryAddress.term
    (st.restrict addressRegs addressLists)).1
  rw [he] at hh
  have hout := h.trans hh
  unfold addressProgram address
  simpa only [State.restrict_regs, show addressRegs 11 = (91 : Fin 100) from rfl] using hout

def addressEmit : Stmt 100 32 := .seq addressProgram (.push 26 91)

theorem addressEmit_run (p : Fin 10 → ℕ) (z : ℕ) (st : State 100 32)
    (hp : Payload p st) (hz : st.regs 90 = z) :
    (addressEmit.run st).1.lists 26 = address p z :: st.lists 26 := by
  have hout := addressProgram_run p z st hp hz
  have hsource := run_lists_frame addressProgram 26 (by decide) st
  simp only [addressEmit, run_seq_fst, run_push_fst, setList_lists, Function.update_self,
    hout, hsource]

theorem addressEmit_payload (p : Fin 10 → ℕ) (st : State 100 32) (hp : Payload p st) :
    Payload p (addressEmit.run st).1 := by
  intro i
  have hf : payloadReg i ∉ addressEmit.regWrites := by fin_cases i <;> decide
  exact (run_regs_frame addressEmit _ hf st).trans (hp i)

def addressBody : Stmt 100 32 := .seq (.pop 25 90 95) addressEmit

theorem addressBody_step (p : Fin 10 → ℕ) (z : ℕ) (zs : List ℕ) (st : State 100 32)
    (hp : Payload p st) (hz : st.lists 25 = z :: zs) :
    Payload p (addressBody.run st).1 ∧ (addressBody.run st).1.lists 25 = zs ∧
      (addressBody.run st).1.lists 26 = address p z :: st.lists 26 := by
  let u := setReg (setReg (setList st 25 zs) 90 z) 95 1
  have hu : Payload p u := by
    intro i
    have h90 : payloadReg i ≠ 90 := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [payloadReg] at hh
      omega
    have h95 : payloadReg i ≠ 95 := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [payloadReg] at hh
      omega
    simpa [u, h90, h95] using hp i
  have he := addressEmit_run p z u hu (by simp [u, Function.update])
  have hctx := addressEmit_payload p u hu
  have hcursor := run_lists_frame addressEmit 25 (by decide) u
  dsimp only [u] at he hctx hcursor
  simp only [addressBody, run_seq_fst, run_pop_cons_fst st 25 90 95 hz]
  generalize hv : (addressEmit.run (setReg (setReg (setList st 25 zs) 90 z) 95 1)).1 = v at *
  exact ⟨hctx, by simpa using hcursor, by simpa [Function.update] using he⟩

theorem address_iterate (p : Fin 10 → ℕ) (zs : List ℕ) (c : ℕ) (st : State 100 32)
    (hp : Payload p st) (hz : st.lists 25 = zs) :
    Payload p (iterate addressBody.run c zs.length st).1 ∧
      (iterate addressBody.run c zs.length st).1.lists 26 =
        (zs.map (address p)).reverse ++ st.lists 26 := by
  induction zs generalizing st with
  | nil => exact ⟨hp, rfl⟩
  | cons z zs ih =>
      have hs := addressBody_step p z zs st hp hz
      simp only [List.length_cons, iterate_succ_fst]
      generalize hu : (addressBody.run st).1 = u at *
      have hh := ih u hs.1 hs.2.1
      refine ⟨hh.1, ?_⟩
      rw [hh.2, hs.2.2]
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append]

/-- The label source is retained; output addresses are in the same order. -/
def physicalQueries : Stmt 100 32 :=
  .seq (.copy 7 26) (.seq (.copy 24 25) (.seq (.len 25 94)
    (.seq (.loop 94 addressBody) (.rev 26))))

theorem physicalQueries_run (p : Fin 10 → ℕ) (zs : List ℕ) (st : State 100 32)
    (hp : Payload p st) (hz : st.lists 24 = zs) (he : st.lists 7 = []) :
    Payload p (physicalQueries.run st).1 ∧
      (physicalQueries.run st).1.lists 26 = zs.map (address p) := by
  let u := setReg (setList (setList st 26 []) 25 zs) 94 zs.length
  have hu : Payload p u := by
    intro i
    have hi : payloadReg i ≠ 94 := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [payloadReg] at hh
      omega
    simpa [u, hi] using hp i
  have hh := address_iterate p zs (Nat.size zs.length + 1) u hu (by simp [u])
  simp only [physicalQueries, run_seq_fst, run_copy_fst, run_len_fst, run_loop_fst,
    setReg_regs, setList_regs, setList_lists, Function.update, Fin.reduceEq,
    dite_false, dite_true, he, hz]
  change Payload p ((Stmt.rev 26).run (iterate addressBody.run
    (Nat.size zs.length + 1) zs.length u).1).1 ∧ _
  generalize hv : (iterate addressBody.run (Nat.size zs.length + 1) zs.length u).1 = v at *
  refine ⟨hh.1, ?_⟩
  simp [run_rev_fst, hh.2, u, Function.update]

/-- Global histories and the numeric source labels are preserved by address mapping. -/
theorem physicalQueries_frame (st : State 100 32) :
    (physicalQueries.run st).1.lists 24 = st.lists 24 ∧
      (physicalQueries.run st).1.lists 30 = st.lists 30 ∧
      (physicalQueries.run st).1.lists 31 = st.lists 31 := by
  exact ⟨run_lists_frame physicalQueries 24 (by decide) st,
    run_lists_frame physicalQueries 30 (by decide) st,
    run_lists_frame physicalQueries 31 (by decide) st⟩

end PCP.Lang.HadamardRow
