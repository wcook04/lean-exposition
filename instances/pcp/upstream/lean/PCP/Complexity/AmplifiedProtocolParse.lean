/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.AmplifiedProtocol
import PCP.Complexity.LangSplitFirstCost
import PCP.Complexity.LangClog

/-! # Actual public triple parsing for the amplified verifier protocol -/

namespace PCP.Lang.AmplifiedProtocolSetup

open PCP.Machine PCP.Machine.LangSymbolBridge

/-- The public symbols retain the declared zero/one/two representation. -/
theorem code_bits (xs : List Bool) : code (ofBits xs) = xs.map Bool.toNat := by
  unfold code ofBits
  rw [List.map_map]
  congr 1
  funext b
  cases b <;> rfl

theorem code_triple (t : List Bool × List Bool × List Bool) :
    code (encodeTriple t) = t.1.map Bool.toNat ++ 2 ::
      (t.2.1.map Bool.toNat ++ 2 :: t.2.2.map Bool.toNat) := by
  simp only [encodeTriple, code, List.map_append, List.map_cons, symbolCode]
  change code (ofBits t.1) ++ 2 :: code (ofBits t.2.1) ++
    2 :: code (ofBits t.2.2) = _
  rw [code_bits, code_bits, code_bits]
  simp only [List.append_assoc, List.cons_append]

theorem bits_no_separator (xs : List Bool) : ∀ v ∈ xs.map Bool.toNat, v ≠ 2 := by
  intro v hv
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
  cases b <;> decide

def splitLists (dst : Fin 140) : Fin 2 → Fin 140 := ![0, dst]

theorem splitLists_injective (dst : Fin 140) (hd : dst ≠ 0) :
    Function.Injective (splitLists dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [splitLists]

def split (dst : Fin 140) : Stmt 420 140 :=
  SplitFirst.program.rename (Fin.castLE (by decide)) (splitLists dst)

theorem split_result (dst : Fin 140) (hd : dst ≠ 0) (st : State 420 140) :
    (((split dst).run st).1.restrict (Fin.castLE (by decide)) (splitLists dst),
      ((split dst).run st).2) =
    SplitFirst.program.run (st.restrict (Fin.castLE (by decide)) (splitLists dst)) :=
  SplitFirst.program.run_rename _ _ (Fin.castLE_injective _) (splitLists_injective dst hd) st

theorem split_run (dst : Fin 140) (hd : dst ≠ 0) (xs ys : List ℕ)
    (hx : ∀ v ∈ xs, v ≠ 2) (st : State 420 140)
    (h0 : st.lists 0 = xs ++ 2 :: ys) (he : st.lists dst = []) :
    ((split dst).run st).1.lists 0 = ys ∧ ((split dst).run st).1.lists dst = xs := by
  have h := SplitFirst.program_run xs ys hx
    (st.restrict (Fin.castLE (by decide)) (splitLists dst)) h0 he
  rw [← split_result dst hd st] at h
  exact h

theorem split_list (dst : Fin 140) (st : State 420 140) (L : Fin 140)
    (h0 : L ≠ 0) (hd : L ≠ dst) : ((split dst).run st).1.lists L = st.lists L := by
  apply Stmt.run_rename_list_outside
  intro i hi
  fin_cases i
  · exact h0 hi.symm
  · exact hd hi.symm

theorem split_reg (dst : Fin 140) (st : State 420 140) (i : Fin 420) (hi : 5 ≤ i.val) :
    ((split dst).run st).1.regs i = st.regs i := by
  apply Stmt.run_rename_reg_outside
  intro j hj
  have := congrArg Fin.val hj
  simp only [Fin.val_castLE] at this
  omega

def parse : Stmt 420 140 := .seq (.len 0 414) (.seq (split 130)
  (.seq (split 131) (.seq (.copy 0 132) (.copy 139 1))))

structure Parsed (t : List Bool × List Bool × List Bool) (st : State 420 140) : Prop where
  graph : st.lists 130 = t.1.map Bool.toNat
  bits : st.lists 131 = t.2.1.map Bool.toNat
  answers : st.lists 132 = t.2.2.map Bool.toNat
  empty : st.lists 139 = []
  output : st.lists 1 = []
  length : st.regs 414 = (encodeTriple t).length

attribute [local irreducible] split

theorem parse_run (t : List Bool × List Bool × List Bool) :
    Parsed t (parse.run (AmplifiedProtocol.initial (code (encodeTriple t)))).1 := by
  let st := AmplifiedProtocol.initial (code (encodeTriple t))
  let u := setReg st 414 (code (encodeTriple t)).length
  have h0 : u.lists 0 = t.1.map Bool.toNat ++ 2 ::
      (t.2.1.map Bool.toNat ++ 2 :: t.2.2.map Bool.toNat) := code_triple t
  have he130 : u.lists 130 = [] := rfl
  have he131 : u.lists 131 = [] := rfl
  have he139 : u.lists 139 = [] := rfl
  have hlen : u.regs 414 = (encodeTriple t).length := by simp [u, code]
  have hfirst := split_run 130 (by decide) _ _ (bits_no_separator t.1) u h0 he130
  have he' := (split_list 130 u 131 (by decide) (by decide)).trans he131
  have hf139 := (split_list 130 u 139 (by decide) (by decide)).trans he139
  have hf414 := (split_reg 130 u 414 (by decide)).trans hlen
  change Parsed t ((Stmt.seq (split 130)
    (.seq (split 131) (.seq (.copy 0 132) (.copy 139 1)))).run u).1
  simp only [run_seq_fst]
  generalize hv : ((split 130).run u).1 = v at *
  have hsecond := split_run 131 (by decide) _ _ (bits_no_separator t.2.1) v hfirst.1 he'
  have hg := (split_list 131 v 130 (by decide) (by decide)).trans hfirst.2
  have he := (split_list 131 v 139 (by decide) (by decide)).trans hf139
  have hn := (split_reg 131 v 414 (by decide)).trans hf414
  generalize hw : ((split 131).run v).1 = w at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [run_copy_fst, setList_lists, setList_regs, Function.update_self,
      Function.update_of_ne (by decide : (130 : Fin 140) ≠ 1),
      Function.update_of_ne (by decide : (130 : Fin 140) ≠ 132),
      Function.update_of_ne (by decide : (131 : Fin 140) ≠ 1),
      Function.update_of_ne (by decide : (131 : Fin 140) ≠ 132),
      Function.update_of_ne (by decide : (132 : Fin 140) ≠ 1),
      Function.update_of_ne (by decide : (139 : Fin 140) ≠ 1),
      Function.update_of_ne (by decide : (139 : Fin 140) ≠ 132)]
  · exact hg
  · exact hsecond.2
  · exact hsecond.1
  · exact he
  · exact he
  · exact hn

end PCP.Lang.AmplifiedProtocolSetup
