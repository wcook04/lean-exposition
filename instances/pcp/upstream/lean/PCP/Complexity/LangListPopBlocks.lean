import PCP.Complexity.LangListTransforms
import PCP.Complexity.TransducerBlocks
import PCP.Complexity.LangListMachine
import PCP.Complexity.LangRegisterBlocks
import PCP.Complexity.BlockConditionalExecution

/-!
# Concrete list pop on materialized shared tapes

The head is read from a snapshot, the presence flag is written afterwards, and
the source list is replaced by its tail. Consequently the value and flag may
share a register: the flag wins, exactly as in the source-language semantics.
-/

namespace PCP.Lang.ListBlocks

open PCP.Machine Turing Turing.TM2 StateTransition FiniteBlocks MachineLayout

variable {R Q : ℕ} {F : Type} [DecidableEq F] [Fintype F]

abbrev readHead (L : Fin Q) (x : Fin R) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (loadList L)
    (BlockControl.sequence (TransducerBlocks.placed LangList.headSpec lengthPorts) (storeReg x))

theorem headWork_executes (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (xs : List ℕ) :
    (TransducerBlocks.placed LangList.headSpec lengthPorts).Executes input output
      (Function.update (tapes st frame) (work 0) (encodeNats xs))
      (Function.update (tapes st frame) (work 3) (natTape (xs.headD 0)))
      (2 * listSize xs + 2) := by
  rw [← listTape_length xs]
  apply TransducerBlocks.executes LangList.headSpec lengthPorts lengthPorts_injective
    input output (encodeNats xs)
  · intro w
    cases w <;> simp [lengthPorts, ListPrimitiveBlocks.workTapes, work, tapes, Function.update]
  · change ∀ w, _ = ListPrimitiveBlocks.workTapes [] []
      (LangList.headSpec.output false (encodeNats xs)) w
    rw [LangList.head_output_encode]
    intro w
    cases w <;> simp [lengthPorts, ListPrimitiveBlocks.workTapes, work, tapes, Function.update]
  · intro k
    have h0 := (k.property .src).symm
    have h3 := (k.property .dst).symm
    simp only [lengthPorts] at h0 h3
    simp only [Function.update_of_ne h0, Function.update_of_ne h3]

theorem readHead_executes (L : Fin Q) (x : Fin R) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (readHead L x).Executes input output (tapes st frame)
      (tapes (setReg st x ((st.lists L).headD 0)) frame)
      (4 * listSize (st.lists L) + Nat.size (st.regs x) +
        3 * Nat.size ((st.lists L).headD 0) + 20) := by
  have h := Block.Executes.seq input output (loadList_executes L input output st frame)
    (Block.Executes.seq input output (headWork_executes input output st frame (st.lists L))
      (storeReg_executes input output st frame x ((st.lists L).headD 0)))
  exact h.mono input output (by omega)

/-- Consume a canonical list result, restoring all scratch tapes. -/
abbrev storeList (L : Fin Q) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (BlockCleanup.one (list L))
    (BlockControl.sequence (BlockCopy.block (work 3) (work 4) (list L))
      (BlockCleanup.one (work 3)))

theorem storeList_executes (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (L : Fin Q) (xs : List ℕ) :
    (storeList L).Executes input output
      (Function.update (tapes st frame) (work 3) (encodeNats xs))
      (tapes (setList st L xs) frame)
      (listSize (st.lists L) + 3 * listSize xs + 10) := by
  let S := Function.update (tapes st frame) (work 3) (encodeNats xs)
  let T := Function.update S (list L) []
  let U := Function.update T (list L) (encodeNats xs)
  have hs : S (list L) = encodeNats (st.lists L) := by
    simp [S, work, list, tapes, stateTapes]
  have ht3 : T (work 3) = encodeNats xs := by simp [T, S, list, work]
  have ht4 : T (work 4) = [] := by simp [T, S, list, work, tapes]
  have htL : T (list L) = [] := by simp [T]
  have hu3 : U (work 3) = encodeNats xs := by simp [U, T, S, list, work]
  have hfinal : Function.update U (work 3) [] = tapes (setList st L xs) frame := by
    rw [tapes_setList]
    funext k
    by_cases hL : k = list L
    · subst k; simp [U, T, S, list, work]
    · by_cases h3 : k = work 3
      · subst k; simp [U, T, S, list, work, tapes]
      · simp [U, T, S, Function.update_of_ne hL, Function.update_of_ne h3]
  have hc := clear_executes input output (list L) S
  have hp := BlockCopy.executes (work 3) (work 4) (list L) input output
    (by simp [work]) (by simp [work, list]) (by simp [work, list]) T ht4
  have hr := clear_executes input output (work 3) U
  simp only [ht3, htL, List.append_nil, listTape_length] at hp
  change (BlockCopy.block (work 3) (work 4) (list L)).Executes input output T U
    (2 * listSize xs + 2) at hp
  rw [hu3, listTape_length, hfinal] at hr
  rw [hs, listTape_length] at hc
  have h := Block.Executes.seq input output hc (Block.Executes.seq input output hp hr)
  exact h.mono input output (by omega)

def tailPorts (L : Fin Q) : MoveSlot → Tapes R Q F
  | .src => list L
  | .scratch => work 1
  | .dst => work 3

omit [DecidableEq F] [Fintype F] in
theorem tailPorts_injective (L : Fin Q) :
    Function.Injective (tailPorts (R := R) (F := F) L) := by
  intro x y h
  cases x <;> cases y <;> first | rfl | simp [tailPorts, work, list] at h

theorem tailWork_executes (L : Fin Q) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (TransducerBlocks.placed LangList.tailSpec (tailPorts L)).Executes input output
      (tapes st frame)
      (Function.update (tapes (setList st L []) frame) (work 3)
        (encodeNats (st.lists L).tail)) (2 * listSize (st.lists L) + 2) := by
  rw [← listTape_length (st.lists L)]
  apply TransducerBlocks.executes LangList.tailSpec (tailPorts L) (tailPorts_injective L)
    input output (encodeNats (st.lists L))
  · intro w
    cases w <;> simp [tailPorts, ListPrimitiveBlocks.workTapes, work, list, tapes, stateTapes]
  · change ∀ w, _ = ListPrimitiveBlocks.workTapes [] []
      (LangList.tailSpec.output false (encodeNats (st.lists L))) w
    rw [LangList.tail_output_encode]
    intro w
    rw [tapes_setList]
    cases w <;> simp [tailPorts, ListPrimitiveBlocks.workTapes, work, list, tapes,
      Function.update, encodeNats]
  · intro k
    have hL := (k.property .src).symm
    have h3 := (k.property .dst).symm
    simp only [tailPorts] at hL h3
    rw [tapes_setList]
    simp only [Function.update_of_ne hL, Function.update_of_ne h3]

abbrev dropHead (L : Fin Q) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (TransducerBlocks.placed LangList.tailSpec (tailPorts L)) (storeList L)

theorem dropHead_executes (L : Fin Q) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (dropHead L).Executes input output (tapes st frame)
      (tapes (setList st L (st.lists L).tail) frame)
      (2 * listSize (st.lists L) + 3 * listSize (st.lists L).tail + 15) := by
  have h := Block.Executes.seq input output (tailWork_executes L input output st frame)
    (storeList_executes input output (setList st L []) frame L (st.lists L).tail)
  simp only [setList, Function.update_self, Function.update_idem] at h
  apply h.mono input output
  simp only [listSize, List.map_nil, List.sum_nil]
  omega

/-- The source list is peeked before the flag register is replaced. -/
abbrev writeFlag (L : Fin Q) (flag : Fin R) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.conditional (assignConst flag 0) (assignConst flag 1) (list L)

theorem writeFlag_executes (L : Fin Q) (flag : Fin R) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (writeFlag L flag).Executes input output (tapes st frame)
      (tapes (setReg st flag (if (st.lists L).isEmpty then 0 else 1)) frame)
      (Nat.size (st.regs flag) + 7) := by
  cases hl : st.lists L with
  | nil =>
      have he : tapes st frame (list L) = [] := by simp [hl, encodeNats]
      simpa only [hl, List.isEmpty_nil, Bool.true_eq, ite_true, Nat.add_assoc, Nat.reduceAdd] using
        (assignConst_executes input output st frame flag 0).ifEmpty input output
          (right := assignConst flag 1) he
  | cons a xs =>
      have he : tapes st frame (list L) ≠ [] := by
        simp [hl, encodeNats, List.append_assoc]
      simpa only [hl, List.isEmpty_cons, Bool.false_eq_true, ite_false,
        Nat.add_assoc, Nat.reduceAdd] using
        (assignConst_executes input output st frame flag 1).ifNonempty input output
          (left := assignConst flag 0) he

abbrev pop (L : Fin Q) (x flag : Fin R) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (readHead L x)
    (BlockControl.sequence (writeFlag L flag) (dropHead L))

/-- Exact source semantics, including an empty list and a shared value/flag register. -/
theorem pop_executes (L : Fin Q) (x flag : Fin R) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (pop L x flag).Executes input output (tapes st frame)
      (tapes ((Stmt.pop L x flag).run st).1 frame)
      (6 * listSize (st.lists L) + 3 * listSize (st.lists L).tail +
        Nat.size (st.regs x) + 3 * Nat.size ((st.lists L).headD 0) +
        Nat.size ((setReg st x ((st.lists L).headD 0)).regs flag) + 48) := by
  let sx := setReg st x ((st.lists L).headD 0)
  let sf := setReg sx flag (if (st.lists L).isEmpty then 0 else 1)
  have hh := readHead_executes L x input output st frame
  have hf := writeFlag_executes L flag input output sx frame
  have ht := dropHead_executes L input output sf frame
  have h := Block.Executes.seq input output hh (Block.Executes.seq input output hf ht)
  have he : setList sf L (sf.lists L).tail = ((Stmt.pop L x flag).run st).1 := by
    cases hl : st.lists L with
    | nil =>
        rw [run_pop_nil_fst st L x flag hl]
        simp [sf, sx, hl, setReg, setList]
    | cons a xs =>
        rw [run_pop_cons_fst st L x flag hl]
        simp [sf, sx, hl, setReg, setList]
  rw [he] at h
  apply h.mono input output
  simp only [sf, sx, setReg_lists]
  omega

/-- A quadratic source-size allowance suffices for every list-pop alias case. -/
theorem pop_sized (L : Fin Q) (x flag : Fin R) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (B : ℕ) (hB : st.Sized B) :
    (pop L x flag).Executes input output (tapes st frame)
      (tapes ((Stmt.pop L x flag).run st).1 frame) (66 * (B + 1) ^ 2) := by
  apply (pop_executes L x flag input output st frame).mono input output
  have hL := hB.2 L
  have hx := hB.1 x
  have hhead : Nat.size ((st.lists L).headD 0) ≤ B := by
    cases hl : st.lists L with
    | nil => simp
    | cons a xs => simp only [hl, listSize, List.map_cons, List.sum_cons,
        List.headD_cons] at *; omega
  have htail : listSize (st.lists L).tail ≤ B := by
    cases hl : st.lists L with
    | nil => simp [listSize]
    | cons a xs => simp only [hl, listSize, List.map_cons, List.sum_cons,
        List.tail_cons] at *; omega
  have hf := (hB.setReg x ((st.lists L).headD 0) hhead).1 flag
  nlinarith

end PCP.Lang.ListBlocks
