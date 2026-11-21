import PCP.Complexity.LangReset
import PCP.Complexity.LangSpace

/-!
# Isolated workspace for calls to the concrete base verifier

The base program uses 400 scalar registers and 128 list registers. Repetition
keeps its public input, seed stream and answer stream in disjoint storage.
Every call clears the base workspace before loading its three Boolean words.
-/

namespace PCP.Lang.AmplifiedWorkspace

def r : Fin 400 → Fin 420 := Fin.castAdd 20
def q : Fin 128 → Fin 140 := Fin.castAdd 12

def reset : Stmt 420 140 :=
  .seq (Reset.regs ((List.finRange 400).map r))
    (Reset.lists 139 ((List.finRange 128).map q))

def loadSources : Stmt 420 140 :=
  .seq (.copy 130 100) (.seq (.copy 133 101) (.copy 132 102))

def prepare : Stmt 420 140 := .seq reset loadSources

def initial (x bits answers : List ℕ) : State 400 128 :=
  ⟨fun _ => 0, fun L => if L = 100 then x else if L = 101 then bits
    else if L = 102 then answers else []⟩

theorem mem_regs (i : Fin 420) :
    i ∈ (List.finRange 400).map r ↔ i.val < 400 := by
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro h
    exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩

theorem mem_lists (i : Fin 140) :
    i ∈ (List.finRange 128).map q ↔ i.val < 128 := by
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro h
    exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩

theorem reset_run (st : State 420 140) (he : st.lists 139 = []) :
    reset.run st = (⟨fun i => if i.val < 400 then 0 else st.regs i,
      fun L => if L.val < 128 then [] else st.lists L⟩, 1059) := by
  have hn : (139 : Fin 140) ∉ (List.finRange 128).map q := by rw [mem_lists]; decide
  simp only [reset, Stmt.run, Reset.regs_run]
  rw [Reset.lists_run 139 _ ⟨fun i => if i ∈ (List.finRange 400).map r then 0
    else st.regs i, st.lists⟩ he hn]
  simp only [mem_regs, mem_lists, List.length_map, List.length_finRange]

theorem prepare_initial (st : State 420 140) (he : st.lists 139 = []) :
    ((prepare.run st).1.restrict r q) =
      initial (st.lists 130) (st.lists 133) (st.lists 132) := by
  simp only [prepare, run_seq_fst, reset_run st he]
  simp only [loadSources, run_seq_fst, run_copy_fst]
  unfold State.restrict initial
  congr 1
  · funext i
    simp [r, i.isLt]
  · funext L
    simp only [setList_lists, Function.comp_apply, Function.update_apply, q,
      Fin.ext_iff, Fin.val_castAdd, L.isLt, ↓reduceIte]
    norm_num
    split_ifs <;> simp_all

theorem prepare_regs (st : State 420 140) (he : st.lists 139 = [])
    (i : Fin 420) (hi : 400 ≤ i.val) :
    (prepare.run st).1.regs i = st.regs i := by
  simp [prepare, run_seq_fst, reset_run st he, loadSources, run_copy_fst, hi.not_gt]

theorem prepare_lists (st : State 420 140) (he : st.lists 139 = [])
    (L : Fin 140) (hL : 128 ≤ L.val) :
    (prepare.run st).1.lists L = st.lists L := by
  simp only [prepare, run_seq_fst, reset_run st he, loadSources, run_copy_fst,
    setList_lists, Function.update_apply]
  split_ifs <;> simp_all
  omega

theorem prepare_cost (st : State 420 140) (he : st.lists 139 = []) :
    (prepare.run st).2 = listSize (st.lists 130) + listSize (st.lists 133) +
      listSize (st.lists 132) + 1065 := by
  simp [prepare, run_seq_snd, reset_run st he, loadSources,
    run_copy_snd, run_copy_fst, Function.update]
  omega

attribute [local irreducible] prepare

def call (P : Stmt 400 128) : Stmt 420 140 := .seq prepare (P.rename r q)

theorem call_result (P : Stmt 400 128) (st : State 420 140) (he : st.lists 139 = []) :
    ((call P).run st).1.restrict r q =
      (P.run (initial (st.lists 130) (st.lists 133) (st.lists 132))).1 := by
  have hr := congrArg Prod.fst (P.run_rename r q (Fin.castAdd_injective _ _)
    (Fin.castAdd_injective _ _) (prepare.run st).1)
  rw [prepare_initial st he] at hr
  exact hr

theorem call_regs (P : Stmt 400 128) (st : State 420 140) (he : st.lists 139 = [])
    (i : Fin 420) (hi : 400 ≤ i.val) :
    ((call P).run st).1.regs i = st.regs i := by
  rw [call, run_seq_fst, P.run_rename_reg_outside r q i]
  · exact prepare_regs st he i hi
  · intro j h
    have hv := congrArg Fin.val h
    change j.val = i.val at hv
    omega

theorem call_lists (P : Stmt 400 128) (st : State 420 140) (he : st.lists 139 = [])
    (L : Fin 140) (hL : 128 ≤ L.val) :
    ((call P).run st).1.lists L = st.lists L := by
  rw [call, run_seq_fst, P.run_rename_list_outside r q L]
  · exact prepare_lists st he L hL
  · intro j h
    have hv := congrArg Fin.val h
    change j.val = L.val at hv
    omega

theorem call_cost (P : Stmt 400 128) (st : State 420 140) (he : st.lists 139 = []) :
    ((call P).run st).2 =
      (P.run (initial (st.lists 130) (st.lists 133) (st.lists 132))).2 +
        listSize (st.lists 130) + listSize (st.lists 133) + listSize (st.lists 132) + 1066 := by
  have hr := congrArg Prod.snd (P.run_rename r q (Fin.castAdd_injective _ _)
    (Fin.castAdd_injective _ _) (prepare.run st).1)
  dsimp only [Prod.snd] at hr
  rw [prepare_initial st he] at hr
  rw [call, run_seq_snd, hr, prepare_cost st he]
  omega

end PCP.Lang.AmplifiedWorkspace
