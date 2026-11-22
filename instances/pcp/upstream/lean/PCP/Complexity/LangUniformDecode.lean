import PCP.Complexity.LangSeedDecode
import PCP.Complexity.LangRenaming

/-!
# Materialized uniform-radix decoding

The program constructs its own radix list from a numeric length and base, then
runs successive division. It keeps leading zero coordinates and preserves the
stored base, length, and empty-list source.
-/

namespace PCP.Lang.UniformDecode

open PCP.Algebraic.ThreeColorSeedIndex

def decoder : Stmt 7 3 := MixedRadixDecode.program.rename
  (Fin.castLE (by decide)) (Fin.castLE (by decide))

def prepare : Stmt 7 3 := .seq (.copy 2 0) (.seq (.copy 2 1) (.loop 5 (.push 0 6)))

def program : Stmt 7 3 := .seq prepare decoder

theorem decoder_result (st : State 7 3) :
    ((decoder.run st).1.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)),
      (decoder.run st).2) = MixedRadixDecode.program.run
        (st.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide))) := by
  unfold decoder
  exact MixedRadixDecode.program.run_rename _ _ (Fin.castLE_injective _)
    (Fin.castLE_injective _) st

theorem repeat_run (n c : ℕ) (st : State 7 3) :
    (iterate (Stmt.push 0 6).run c n st).1.regs = st.regs ∧
    (iterate (Stmt.push 0 6).run c n st).1.lists 0 =
      List.replicate n (st.regs 6) ++ st.lists 0 ∧
    (iterate (Stmt.push 0 6).run c n st).1.lists 1 = st.lists 1 ∧
    (iterate (Stmt.push 0 6).run c n st).1.lists 2 = st.lists 2 := by
  induction n generalizing st with
  | zero => simp [iterate]
  | succ n ih =>
      rw [iterate_succ_fst]
      have h := ih (setList st 0 (st.regs 6 :: st.lists 0))
      simpa only [run_push_fst, setList_regs, setList_lists,
        Function.update_self, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
        Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0),
        List.replicate_succ', List.append_assoc, List.singleton_append] using h

theorem prepare_run (st : State 7 3) (he : st.lists 2 = []) :
    (prepare.run st).1.regs = st.regs ∧
    (prepare.run st).1.lists 0 = List.replicate (st.regs 5) (st.regs 6) ∧
    (prepare.run st).1.lists 1 = [] ∧ (prepare.run st).1.lists 2 = [] := by
  have h := repeat_run (st.regs 5) (Nat.size (st.regs 5) + 1)
    (setList (setList st 0 []) 1 [])
  simp only [prepare, run_seq_fst, run_copy_fst, run_loop_fst, setList_regs,
    setList_lists, Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0), he]
  simpa [Function.update, he] using h

/-- Every requested coordinate is present, including leading zero coordinates. -/
theorem program_run (st : State 7 3) (he : st.lists 2 = []) :
    (program.run st).1.lists 1 =
      (MixedRadixDecode.split (st.regs 0) (List.replicate (st.regs 5) (st.regs 6))).1 ∧
    (program.run st).1.regs 0 =
      st.regs 0 / (st.regs 6) ^ (st.regs 5) ∧
    (program.run st).1.lists 0 = [] := by
  have hp := prepare_run st he
  generalize hs : (prepare.run st).1 = s at *
  have hd := MixedRadixDecode.program_run
    (s.restrict (Fin.castLE (by decide)) (Fin.castLE (by decide)))
  rw [← decoder_result s] at hd
  simp only [State.restrict_regs, State.restrict_lists,
    show Fin.castLE (by decide : 5 ≤ 7) (0 : Fin 5) = (0 : Fin 7) from rfl,
    show Fin.castLE (by decide : 2 ≤ 3) (0 : Fin 2) = (0 : Fin 3) from rfl,
    show Fin.castLE (by decide : 2 ≤ 3) (1 : Fin 2) = (1 : Fin 3) from rfl] at hd
  simp only [hp.1, hp.2.1, hp.2.2.1, List.reverse_nil, List.nil_append,
    MixedRadixDecode.split_quotient, List.prod_replicate] at hd
  simp only [program, run_seq_fst, hs]
  exact ⟨hd.2.2, hd.1, hd.2.1⟩

theorem program_frame (st : State 7 3) :
    (program.run st).1.regs 5 = st.regs 5 ∧
    (program.run st).1.regs 6 = st.regs 6 ∧
    (program.run st).1.lists 2 = st.lists 2 := by
  constructor
  · apply run_regs_frame program 5
    simp only [program, decoder, prepare, Stmt.regWrites, Stmt.regWrites_rename,
      List.mem_append, List.not_mem_nil, false_or, List.mem_map]
    rintro ⟨i, _, hi⟩
    have := congrArg Fin.val hi
    simp only [Fin.val_castLE] at this
    omega
  constructor
  · apply run_regs_frame program 6
    simp only [program, decoder, prepare, Stmt.regWrites, Stmt.regWrites_rename,
      List.mem_append, List.not_mem_nil, false_or, List.mem_map]
    rintro ⟨i, _, hi⟩
    have := congrArg Fin.val hi
    simp only [Fin.val_castLE] at this
    omega
  · exact run_lists_frame program 2 (by simp [program, decoder, prepare, Stmt.listWrites]) st

/-- Uniform finite functions are decoded in the actual production coordinate order. -/
theorem program_finFunction (base n : ℕ) (code : Fin (base ^ n)) (st : State 7 3)
    (hc : st.regs 0 = code.val) (hn : st.regs 5 = n) (hb : st.regs 6 = base)
    (he : st.lists 2 = []) :
    (program.run st).1.lists 1 =
      List.ofFn (fun i : Fin n => ((finFunctionFinEquiv.symm code) i).val) := by
  rw [(program_run st he).1, hc, hn, hb, MixedRadixDecode.split_finFunction]

/-- This includes product/sum domain codecs used by all production point types. -/
theorem program_codecFunction {A B : Type*} (a : Codec A) (b : Codec B) (f : A → B)
    (st : State 7 3) (hc : st.regs 0 = ((a.function b).equiv f).val)
    (hn : st.regs 5 = a.size) (hb : st.regs 6 = b.size) (he : st.lists 2 = []) :
    (program.run st).1.lists 1 = List.ofFn (fun i => (b.equiv (f (a.equiv.symm i))).val) := by
  rw [program_finFunction b.size a.size ((a.function b).equiv f) st hc hn hb he]
  congr 1
  funext i
  change ((finFunctionFinEquiv.symm (finFunctionFinEquiv
    ((Equiv.arrowCongr a.equiv b.equiv) f))) i).val = _
  rw [Equiv.symm_apply_apply]
  rfl

end PCP.Lang.UniformDecode
