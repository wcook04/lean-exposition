import PCP.Complexity.LangListBlocks
import PCP.Complexity.ListPrimitiveBlocks
import PCP.Complexity.LangArithmeticBlocks

/-!
# Shared-tape list length, reversal, and reverse-append

Each operation copies its source before consuming work tapes. Thus reverse-append
also handles identical source and destination lists. All reusable scratch and
local control are reset, and arbitrary caller storage is retained.
-/

namespace PCP.Lang.ListBlocks

open PCP.Machine Turing Turing.TM2 StateTransition FiniteBlocks MachineLayout

variable {R Q : ℕ} {F : Type} [DecidableEq F] [Fintype F]

abbrev loadList (L : Fin Q) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockCopy.block (list L) (work 4) (work 0)

theorem loadList_executes (L : Fin Q) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (loadList L).Executes input output (tapes st frame)
      (Function.update (tapes st frame) (work 0) (encodeNats (st.lists L)))
      (2 * listSize (st.lists L) + 2) := by
  have h := BlockCopy.executes (list L) (work 4) (work 0) input output
    (by simp [list, work]) (by simp [list, work]) (by simp [work]) (tapes st frame) (by rfl)
  simpa only [tapes_list, tapes_work, List.append_nil, listTape_length] using h

def reversePorts (M : Fin Q) : MoveSlot → Tapes R Q F
  | .src => work 0
  | .scratch => work 1
  | .dst => list M

omit [DecidableEq F] [Fintype F] in
theorem reversePorts_injective (M : Fin Q) :
    Function.Injective (reversePorts (R := R) (F := F) M) := by
  intro x y h
  cases x <;> cases y <;> first | rfl | simp [reversePorts, work, list] at h

/-- A saved list is consumed into a target list, restoring the statement boundary. -/
theorem reverseWork_executes (M : Fin Q) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (xs : List ℕ) :
    (ListPrimitiveBlocks.placedReverse (reversePorts M)).Executes input output
      (Function.update (tapes st frame) (work 0) (encodeNats xs))
      (tapes (setList st M (xs.reverse ++ st.lists M)) frame) (2 * listSize xs + 1) := by
  apply ListPrimitiveBlocks.reverse_executes (reversePorts M) (reversePorts_injective M)
    input output xs (encodeNats (st.lists M))
  · intro w
    cases w <;> simp [reversePorts, ListPrimitiveBlocks.workTapes, work, list,
      tapes, stateTapes, Function.update]
  · intro w
    rw [tapes_setList]
    cases w <;> simp [reversePorts, ListPrimitiveBlocks.workTapes, work, list,
      tapes, Function.update, encodeNats, List.flatMap_append]
  · intro k
    have h0 := (k.property .src).symm
    have hM := (k.property .dst).symm
    simp only [reversePorts] at h0 hM
    rw [tapes_setList]
    simp only [Function.update_of_ne h0, Function.update_of_ne hM]

abbrev revApp (L M : Fin Q) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (loadList L) (ListPrimitiveBlocks.placedReverse (reversePorts M))

/-- Source and destination may coincide. The source snapshot is made first. -/
theorem revApp_executes (L M : Fin Q) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (revApp L M).Executes input output (tapes st frame)
      (tapes ((Stmt.revApp L M).run st).1 frame) (4 * listSize (st.lists L) + 6) := by
  have h := Block.Executes.seq input output (loadList_executes L input output st frame)
    (reverseWork_executes M input output st frame (st.lists L))
  simpa only [run_revApp_fst] using h.mono input output (by omega)

abbrev rev (L : Fin Q) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (loadList L)
    (BlockControl.sequence (BlockCleanup.one (list L))
      (ListPrimitiveBlocks.placedReverse (reversePorts L)))

/-- Reversal clears the original only after copying it to the work tape. -/
theorem rev_executes (L : Fin Q) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (rev L).Executes input output (tapes st frame)
      (tapes ((Stmt.rev L).run st).1 frame) (5 * listSize (st.lists L) + 10) := by
  let S := tapes st frame
  let T := Function.update S (work 0) (encodeNats (st.lists L))
  have hc := clear_executes input output (list L) T
  have hT : T (list L) = encodeNats (st.lists L) := by
    simp [T, S, list, work, tapes, stateTapes]
  have hclear : Function.update T (list L) [] =
      Function.update (tapes (setList st L []) frame) (work 0) (encodeNats (st.lists L)) := by
    rw [tapes_setList]
    change Function.update (Function.update S (work 0) (encodeNats (st.lists L)))
      (list L) [] = Function.update (Function.update S (list L) [])
      (work 0) (encodeNats (st.lists L))
    exact Function.update_comm (by simp [work, list]) _ _ _
  rw [hT, listTape_length, hclear] at hc
  have hr := reverseWork_executes L input output (setList st L []) frame (st.lists L)
  have hfinal : tapes (setList (setList st L []) L
      ((st.lists L).reverse ++ (setList st L []).lists L)) frame =
      tapes ((Stmt.rev L).run st).1 frame := by
    rw [run_rev_fst]
    simp [setList, Function.update_idem]
  rw [hfinal] at hr
  have h := Block.Executes.seq input output (loadList_executes L input output st frame)
    (Block.Executes.seq input output hc hr)
  convert h using 1
  omega

def lengthPorts : MoveSlot → Tapes R Q F
  | .src => work 0
  | .scratch => work 1
  | .dst => work 3

omit [DecidableEq F] [Fintype F] in
theorem lengthPorts_injective :
    Function.Injective (lengthPorts (R := R) (Q := Q) (F := F)) := by
  intro x y h
  cases x <;> cases y <;> first | rfl | simp [lengthPorts, work] at h

/-- Materialized length counting leaves a binary result ready for the common register store. -/
theorem lengthWork_executes (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (xs : List ℕ) :
    (ListPrimitiveBlocks.placedLength lengthPorts).Executes input output
      (Function.update (tapes st frame) (work 0) (encodeNats xs))
      (Function.update (tapes st frame) (work 3) (natTape xs.length))
      ((2 * listSize xs + 4) * listSize xs + 1) := by
  apply ListPrimitiveBlocks.length_executes lengthPorts lengthPorts_injective input output xs
  · intro w
    cases w <;> simp [lengthPorts, ListPrimitiveBlocks.workTapes, work, tapes, Function.update]
  · intro w
    cases w <;> simp [lengthPorts, ListPrimitiveBlocks.workTapes, work, tapes, Function.update]
  · intro k
    have h0 := (k.property .src).symm
    have h3 := (k.property .dst).symm
    simp only [lengthPorts] at h0 h3
    simp only [Function.update_of_ne h0, Function.update_of_ne h3]

abbrev len (L : Fin Q) (x : Fin R) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (loadList L)
    (BlockControl.sequence (ListPrimitiveBlocks.placedLength lengthPorts) (storeReg x))

theorem len_executes (L : Fin Q) (x : Fin R) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (len L x).Executes input output (tapes st frame)
      (tapes ((Stmt.len L x).run st).1 frame)
      ((2 * listSize (st.lists L) + 6) * listSize (st.lists L) +
        Nat.size (st.regs x) + 3 * Nat.size (st.lists L).length + 19) := by
  have h := Block.Executes.seq input output (loadList_executes L input output st frame)
    (Block.Executes.seq input output (lengthWork_executes input output st frame (st.lists L))
      (storeReg_executes input output st frame x (st.lists L).length))
  rw [run_len_fst]
  exact h.mono input output (by ring_nf; omega)

/-- Uniform source-state bounds for reverse-append, including the alias case. -/
theorem revApp_sized (L M : Fin Q) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (B : ℕ) (hB : st.Sized B) :
    (revApp L M).Executes input output (tapes st frame)
      (tapes ((Stmt.revApp L M).run st).1 frame) (32 * (B + 1) ^ 2) := by
  apply (revApp_executes L M input output st frame).mono input output
  have h := hB.2 L
  nlinarith

theorem rev_sized (L : Fin Q) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (B : ℕ) (hB : st.Sized B) :
    (rev L).Executes input output (tapes st frame)
      (tapes ((Stmt.rev L).run st).1 frame) (32 * (B + 1) ^ 2) := by
  apply (rev_executes L input output st frame).mono input output
  have h := hB.2 L
  nlinarith

theorem len_sized (L : Fin Q) (x : Fin R) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (B : ℕ) (hB : st.Sized B) :
    (len L x).Executes input output (tapes st frame)
      (tapes ((Stmt.len L x).run st).1 frame) (32 * (B + 1) ^ 2) := by
  apply (len_executes L x input output st frame).mono input output
  have hL := hB.2 L
  have hx := hB.1 x
  have hn := (size_le_self (st.lists L).length).trans ((length_le_listSize _).trans hL)
  have hsq := Nat.mul_self_le_mul_self hL
  nlinarith

end PCP.Lang.ListBlocks
