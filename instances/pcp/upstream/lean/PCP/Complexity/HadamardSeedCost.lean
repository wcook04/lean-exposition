/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardSeedLang
import PCP.Complexity.HadamardSeedRadicesCost
import PCP.Complexity.HadamardSeedMaterializeCost

/-!
# Polynomial charged cost of loading actual Hadamard seeds

The bound uses the bit size of the supplied numeric seed, field cardinality,
and the fixed row degree. It includes every materialized coefficient array.
-/

namespace PCP.Lang.HadamardSeed

open PCP.Algebraic ThreeColorSeedIndex

variable {t r : ℕ}

theorem decoder_cost (st : State 100 32) :
    (decoder.run st).2 ≤ (MixedRadixDecode.passConstant + 12) *
      (listSize (st.lists 25) + listSize (st.lists 24) + Nat.size (st.regs 97) + 2) ^ 2 := by
  rw [decoder, Stmt.run_rename_cost MixedRadixDecode.program decoderRegs decoderLists
    decoderRegs_injective decoderLists_injective]
  exact MixedRadixDecode.program_cost (st.restrict decoderRegs decoderLists)

theorem decode_cost (st : State 100 32) (he : st.lists 7 = []) :
    (decode.run st).2 ≤ (MixedRadixDecode.passConstant + 20) *
      (listSize (st.lists 25) + Nat.size (st.regs 96) + 3) ^ 2 := by
  let u := setReg (setList st 24 []) 97 (st.regs 96)
  have hc := decoder_cost u
  have ho := decoder_run u
  simp only [u, setReg_lists, setList_lists, Function.update_self, setReg_regs,
    Function.update_of_ne (by decide : (25 : Fin 32) ≠ 24), listSize,
    List.map_nil, List.sum_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hc ho
  have hs : listSize ((decoder.run u).1.lists 24) ≤
      (st.lists 25).length * (Nat.size (st.regs 96) + 1) := by
    rw [ho]; exact MixedRadixDecode.split_listSize _ _
  have hn := length_le_listSize (st.lists 25)
  have hprod := Nat.mul_le_mul_right (Nat.size (st.regs 96) + 1) hn
  simp only [decode, run_seq_snd, run_copy_snd, run_copy_fst, he,
    run_assign_fst, Expr.eval, setList_regs]
  change 1 + (Nat.size (st.regs 96) + Nat.size (st.regs 96) + 1 +
    ((decoder.run u).2 + (listSize ((decoder.run u).1.lists 24) + 1) + 1) + 1) + 1 ≤ _
  change (decoder.run u).2 ≤ (MixedRadixDecode.passConstant + 12) *
    (listSize (st.lists 25) + Nat.size (st.regs 96) + 2) ^ 2 at hc
  nlinarith only [hc, hs, hprod, Nat.zero_le MixedRadixDecode.passConstant,
    Nat.zero_le (listSize (st.lists 25)), Nat.zero_le (Nat.size (st.regs 96)),
    Nat.zero_le ((listSize (st.lists 25)) ^ 2), Nat.zero_le ((Nat.size (st.regs 96)) ^ 2)]

def seedConstant : ℕ := MixedRadixDecode.passConstant + 3000022

theorem program_cost (s : Hadamard.TestRandomness t r) (st : State 100 32)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hc : st.regs 96 = ((hadamardCodec t r).equiv s).val) :
    ((program r).run st).2 ≤ seedConstant *
      (2 ^ t + r + Nat.size (st.regs 96) + 5) ^ 5 := by
  let B := 2 ^ t + r + Nat.size (st.regs 96) + 5
  have hr := radixProgram_run r st ht he
  have hrc := radixProgram_cost r st ht he
  have hf := radixProgram_protected r st 96 (by decide)
  simp only [program, run_seq_snd]
  generalize hu : ((radixProgram r).run st).1 = u at *
  have hd := decode_run u hr.2.2
  have hdc := decode_cost u hr.2.2
  rw [hf, hr.1] at hdc
  rw [hf, hc, hr.1, split_hadamard] at hd
  have hdf := decode_frame u
  generalize hv : (decode.run u).1 = v at *
  have hm := materialize_cost s v (hdf.1.trans hr.2.1) (hdf.2.2.trans hr.2.2) hd
  have hB : 1 ≤ B := Nat.succ_le_succ (Nat.zero_le _)
  have hb : 2 ^ t + r + 4 ≤ B := by dsimp [B]; omega
  have hr' := hrc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 5))
  have h4 : B ^ 4 ≤ B ^ 5 := Nat.pow_le_pow_right hB (by decide)
  have hm' := hm.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hb 4).trans h4))
  have hs := radices_size t r
  have hdB : listSize (radices t r) + Nat.size (st.regs 96) + 3 ≤ B ^ 2 := by
    dsimp [B]
    nlinarith only [hs, Nat.zero_le (2 ^ t), Nat.zero_le r,
      Nat.zero_le (Nat.size (st.regs 96)), Nat.zero_le ((2 ^ t) ^ 2),
      Nat.zero_le (r ^ 2), Nat.zero_le ((Nat.size (st.regs 96)) ^ 2)]
  have hdc' := hdc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdB 2))
  rw [← pow_mul, show 2 * 2 = 4 from rfl] at hdc'
  have hd' := hdc'.trans (Nat.mul_le_mul_left _ h4)
  have hpos : 1 ≤ B ^ 5 := Nat.one_le_pow _ _ hB
  change _ ≤ seedConstant * B ^ 5
  have sumBound : ∀ C P x y z : ℕ, x ≤ 700000 * P → y ≤ (C + 20) * P →
      z ≤ 2300000 * P → 1 ≤ P → x + (y + z + 1) + 1 ≤ (C + 3000022) * P := by
    intros
    nlinarith
  exact sumBound _ _ _ _ _ hr' hd' hm' hpos

end PCP.Lang.HadamardSeed
