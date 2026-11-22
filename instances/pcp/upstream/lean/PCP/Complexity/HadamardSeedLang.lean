/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardSeedRadices
import PCP.Complexity.HadamardSeedMaterialize

/-!
# The actual Hadamard seed-code loader

The fixed degree is a program parameter (one or three in production). Live
inputs are width 20, seed code 96, and empty list 7. The complete stored row seed
is produced in lists 20 through 23, with degree 56 and restored width 20.
-/

namespace PCP.Lang.HadamardSeed

open PCP.Algebraic ThreeColorSeedIndex

variable {t r : ℕ}

def decoderRegs : Fin 5 → Fin 100 := ![97, 58, 59, 60, 61]
def decoderLists : Fin 2 → Fin 32 := ![25, 24]

theorem decoderRegs_injective : Function.Injective decoderRegs := by decide
theorem decoderLists_injective : Function.Injective decoderLists := by decide

def decoder : Stmt 100 32 :=
  MixedRadixDecode.program.rename decoderRegs decoderLists

def decode : Stmt 100 32 := .seq (.copy 7 24) (.seq (.assign 97 (.var 96))
  (.seq decoder (.copy 24 25)))

theorem decoder_run (st : State 100 32) :
    (decoder.run st).1.lists 24 = (st.lists 24).reverse ++
      (MixedRadixDecode.split (st.regs 97) (st.lists 25)).1 := by
  have h := (MixedRadixDecode.program_run (st.restrict decoderRegs decoderLists)).2.2
  have hr := MixedRadixDecode.program.run_rename decoderRegs decoderLists
    decoderRegs_injective decoderLists_injective st
  rw [← hr] at h
  exact h

theorem decode_run (st : State 100 32) (he : st.lists 7 = []) :
    (decode.run st).1.lists 25 =
      (MixedRadixDecode.split (st.regs 96) (st.lists 25)).1 := by
  have h := decoder_run (setReg (setList st 24 []) 97 (st.regs 96))
  simp only [setReg_lists, setList_lists, Function.update_self, setReg_regs,
    Function.update_of_ne (by decide : (25 : Fin 32) ≠ 24), List.reverse_nil,
    List.nil_append] at h
  simp only [decode, run_seq_fst, run_copy_fst, he, run_assign_fst, Expr.eval, setList_regs]
  generalize hu : (decoder.run (setReg (setList st 24 []) 97 (st.regs 96))).1 = u at *
  simpa using h

theorem decode_frame (st : State 100 32) :
    (decode.run st).1.regs 20 = st.regs 20 ∧
      (decode.run st).1.regs 96 = st.regs 96 ∧
      (decode.run st).1.lists 7 = st.lists 7 := by
  exact ⟨run_regs_frame decode 20 (by decide) st, run_regs_frame decode 96 (by decide) st,
    run_lists_frame decode 7 (by decide) st⟩

/-- A uniform field-width program for each fixed production row degree. -/
def program (r : ℕ) : Stmt 100 32 :=
  .seq (radixProgram r) (.seq decode (materialize r))

theorem program_run (s : Hadamard.TestRandomness t r) (st : State 100 32)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hc : st.regs 96 = ((hadamardCodec t r).equiv s).val) :
    HadamardRow.Context s (((program r).run st).1.restrict subRegs id) := by
  have hr := radixProgram_run r st ht he
  have hf := radixProgram_protected r st 96 (by decide)
  simp only [program, run_seq_fst]
  generalize hu : ((radixProgram r).run st).1 = u at *
  have hd := decode_run u hr.2.2
  rw [hf, hc, hr.1, split_hadamard] at hd
  have hdf := decode_frame u
  generalize hv : (decode.run u).1 = v at *
  exact materialize_run s v (hdf.1.trans hr.2.1) (hdf.2.2.trans hr.2.2) hd

end PCP.Lang.HadamardSeed
