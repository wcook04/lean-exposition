import PCP.Complexity.LangMachineState
import PCP.Complexity.BlockExecution
import PCP.Complexity.LangSpace

/-!
# List push and copy on the compiler's shared materialized tapes

Registers are retained when pushed. List copying handles identical source and
destination by a concrete no-op block; distinct destinations are cleared before
copying. Every operation restores all scratch tapes and preserves the caller's
frame, including enclosing loop counters.
-/

namespace PCP.Lang.ListBlocks

open PCP.Machine Turing Turing.TM2 StateTransition FiniteBlocks MachineLayout

variable {R Q : ℕ} {F : Type} [DecidableEq F] [Fintype F]

/-- A fixed symbol is pushed in a single actual machine transition. -/
abbrev pushSymbol (k : Tapes R Q F) (c : Sym) : Block (Tapes R Q F) (fun _ => Sym) where
  Label := Unit
  Control := Unit
  entry := ()
  initial := ()
  code _ := .push k (fun _ => c) .halt

theorem pushSymbol_executes (k input output : Tapes R Q F) (c : Sym)
    (S : Tapes R Q F → List Sym) :
    (pushSymbol k c).Executes input output S (Function.update S k (c :: S k)) 1 :=
  ⟨1, le_rfl, rfl⟩

/-- Add the list delimiter, then copy the retained canonical register numeral. -/
abbrev push (L : Fin Q) (x : Fin R) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (pushSymbol (list L) .sep)
    (BlockCopy.block (reg x) (work 0) (list L))

theorem push_executes (L : Fin Q) (x : Fin R) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (push L x).Executes input output (tapes st frame)
      (tapes ((Stmt.push L x).run st).1 frame) (2 * Nat.size (st.regs x) + 6) := by
  let S := tapes st frame
  let T := Function.update S (list L) (.sep :: S (list L))
  have hp := pushSymbol_executes (list L) input output .sep S
  have hc := BlockCopy.executes (reg x) (work 0) (list L) input output
    (by simp [reg, work]) (by simp [reg, list]) (by simp [work, list]) T
    (by simp [T, S, work, list, MachineLayout.tapes])
  have h := Block.Executes.seq input output hp hc
  have ht : Function.update T (list L) (T (reg x) ++ T (list L)) =
      tapes ((Stmt.push L x).run st).1 frame := by
    rw [run_push_fst, tapes_setList]
    simp [T, S, reg, list, MachineLayout.tapes, stateTapes, encodeNats, natTape,
      List.append_assoc]
  rw [ht] at h
  simpa only [T, S, Function.update_of_ne (show reg x ≠ list L by simp [reg, list]),
    tapes_reg, natTape_length, Nat.add_assoc, Nat.one_add] using h

/-- Data-dependent aliases are resolved by the fixed syntax's decidable index equality. -/
def copy (L M : Fin Q) : Block (Tapes R Q F) (fun _ => Sym) :=
  if L = M then BlockCleanup.empty else
    BlockControl.sequence (BlockCleanup.one (list M))
      (BlockCopy.block (list L) (work 0) (list M))

theorem copy_executes (L M : Fin Q) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) :
    (copy L M).Executes input output (tapes st frame)
      (tapes ((Stmt.copy L M).run st).1 frame)
      (2 * listSize (st.lists L) + listSize (st.lists M) + 6) := by
  by_cases he : L = M
  · subst M
    rw [copy, ite_eq_left rfl]
    have ht : tapes ((Stmt.copy L L).run st).1 frame = tapes st frame := by
      rw [run_copy_fst, tapes_setList, ← tapes_list st frame L, Function.update_eq_self]
    rw [ht]
    exact (empty_executes input output (tapes st frame)).mono input output (by omega)
  · rw [copy, ite_eq_right he]
    let S := tapes st frame
    let T := Function.update S (list M) []
    have hp := clear_executes input output (list M) S
    have hc := BlockCopy.executes (list L) (work 0) (list M) input output
      (by simp [list, work]) (by simpa [list] using he) (by simp [work, list]) T
      (by simp [T, S, work, list, MachineLayout.tapes])
    have h := Block.Executes.seq input output hp hc
    have ht : Function.update T (list M) (T (list L) ++ T (list M)) =
        tapes ((Stmt.copy L M).run st).1 frame := by
      rw [run_copy_fst, tapes_setList]
      simp [T, S, list, he, MachineLayout.tapes, stateTapes]
    rw [ht] at h
    have hlm : (list L : Tapes R Q F) ≠ list M := by simpa [list] using he
    apply h.mono input output
    simp only [S, T, Function.update_of_ne hlm, tapes_list, listTape_length]
    omega

/-- Uniform compiler bound, including any previous destination contents. -/
theorem push_sized (L : Fin Q) (x : Fin R) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (B : ℕ) (hB : st.Sized B) :
    (push L x).Executes input output (tapes st frame)
      (tapes ((Stmt.push L x).run st).1 frame) (10 * (B + 1) ^ 2) := by
  apply (push_executes L x input output st frame).mono input output
  have h := hB.1 x
  nlinarith

/-- The equal-index case satisfies the same bound as distinct-index copying. -/
theorem copy_sized (L M : Fin Q) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (B : ℕ) (hB : st.Sized B) :
    (copy L M).Executes input output (tapes st frame)
      (tapes ((Stmt.copy L M).run st).1 frame) (10 * (B + 1) ^ 2) := by
  apply (copy_executes L M input output st frame).mono input output
  have hl := hB.2 L
  have hm := hB.2 M
  nlinarith

end PCP.Lang.ListBlocks
