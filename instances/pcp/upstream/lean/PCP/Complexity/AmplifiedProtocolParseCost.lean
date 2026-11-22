/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.AmplifiedProtocolParse

/-! # Charged polynomial cost of parsing the public encoded triple -/

namespace PCP.Lang.AmplifiedProtocolSetup

open PCP.Machine PCP.Machine.LangSymbolBridge

attribute [local irreducible] split

theorem split_cost (dst : Fin 140) (hd : dst ≠ 0) (st : State 420 140)
    (hb : ∀ v ∈ st.lists 0, v ≤ 2) (he : st.lists dst = []) :
    ((split dst).run st).2 ≤ 100 * (listSize (st.lists 0) + 1) ^ 2 := by
  have h := SplitFirst.program_cost
    (st.restrict (Fin.castLE (by decide)) (splitLists dst)) hb he
  rw [← split_result dst hd] at h
  exact h

theorem code_le_two (xs : List Sym) : ∀ v ∈ code xs, v ≤ 2 := by
  intro v hv
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
  cases b with
  | bit b => cases b <;> decide
  | sep => decide

theorem code_listSize (xs : List Sym) : listSize (code xs) ≤ 3 * xs.length := by
  unfold listSize
  have h := List.sum_le_length_nsmul (code xs |>.map fun v => Nat.size v + 1) 3 (by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have h := (size_le_self w).trans (code_le_two xs w hw)
    omega)
  simpa [code, Nat.mul_comm] using h

theorem parse_cost (t : List Bool × List Bool × List Bool) :
    (parse.run (AmplifiedProtocol.initial (code (encodeTriple t)))).2 ≤
      2000 * ((encodeTriple t).length + 1) ^ 2 := by
  let N := (encodeTriple t).length
  let st := AmplifiedProtocol.initial (code (encodeTriple t))
  let u := setReg st 414 (code (encodeTriple t)).length
  have h0 : u.lists 0 = t.1.map Bool.toNat ++ 2 ::
      (t.2.1.map Bool.toNat ++ 2 :: t.2.2.map Bool.toNat) := code_triple t
  have he130 : u.lists 130 = [] := rfl
  have he131 : u.lists 131 = [] := rfl
  have he139 : u.lists 139 = [] := rfl
  have hc1 := split_cost 130 (by decide) u (code_le_two (encodeTriple t)) he130
  have hs1 := split_run 130 (by decide) _ _ (bits_no_separator t.1) u h0 he130
  have hf131 := (split_list 130 u 131 (by decide) (by decide)).trans he131
  have hf139 := (split_list 130 u 139 (by decide) (by decide)).trans he139
  have hn : N = t.1.length + t.2.1.length + t.2.2.length + 2 := by
    simp [N]
  have hinput := code_listSize (encodeTriple t)
  have hc1' : ((split 130).run u).2 ≤ 900 * (N + 1) ^ 2 := by
    change _ ≤ 100 * (listSize (code (encodeTriple t)) + 1) ^ 2 at hc1
    have harg : listSize (code (encodeTriple t)) + 1 ≤ 3 * (N + 1) := by
      dsimp [N]
      omega
    have h := hc1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
    nlinarith only [h]
  have hprefix : listSize (t.2.1.map Bool.toNat ++ 2 :: t.2.2.map Bool.toNat) ≤ 3 * N := by
    have hb := AmplifiedStream.boolList_size t.2.1
    have ha := AmplifiedStream.boolList_size t.2.2
    simp only [listSize_append]
    change listSize (t.2.1.map Bool.toNat) +
      (3 + listSize (t.2.2.map Bool.toNat)) ≤ 3 * N
    omega
  simp only [parse, run_seq_snd, run_len_snd, run_len_fst]
  change listSize (code (encodeTriple t)) + Nat.size (code (encodeTriple t)).length + 1 +
    (((split 130).run u).2 + (((split 131).run ((split 130).run u).1).2 +
      (((Stmt.seq (.copy 0 132) (.copy 139 1)).run
        ((split 131).run ((split 130).run u).1).1).2) + 1) + 1) + 1 ≤ _
  generalize hv : ((split 130).run u).1 = v at *
  have hvsmall : ∀ z ∈ v.lists 0, z ≤ 2 := by
    rw [hs1.1]
    intro z hz
    simp only [List.mem_append, List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hz
      cases b <;> decide
    · decide
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hz
      cases b <;> decide
  have hc2 := split_cost 131 (by decide) v hvsmall hf131
  rw [hs1.1] at hc2
  have hc2' : ((split 131).run v).2 ≤ 900 * (N + 1) ^ 2 := by
    have harg : listSize (t.2.1.map Bool.toNat ++ 2 :: t.2.2.map Bool.toNat) + 1 ≤
        3 * (N + 1) := by omega
    have h := hc2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 2))
    nlinarith only [h]
  have hs2 := split_run 131 (by decide) _ _ (bits_no_separator t.2.1) v hs1.1 hf131
  have he := (split_list 131 v 139 (by decide) (by decide)).trans hf139
  generalize hw : ((split 131).run v).1 = w at *
  have ha := AmplifiedStream.boolList_size t.2.2
  have hnsize := size_le_self N
  simp only [run_seq_snd, run_copy_snd, run_copy_fst, setList_lists,
    Function.update_of_ne (by decide : (139 : Fin 140) ≠ 132), he,
    show listSize [] = 0 from rfl, hs2.1, code, List.length_map]
  change _ ≤ 2000 * (N + 1) ^ 2
  change listSize (code (encodeTriple t)) ≤ 3 * N at hinput
  dsimp only [code] at hinput
  dsimp only [N] at hnsize hc1' hc2' hn hinput
  nlinarith only [hinput, hc1', hc2', hnsize, ha, hn, Nat.zero_le (N ^ 2)]

end PCP.Lang.AmplifiedProtocolSetup
