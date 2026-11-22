import PCP.Complexity.LangBlockReframe
import PCP.Complexity.LangArithmeticBlocks
import PCP.Complexity.BlockWriteMachine

/-!
# Saved binary loop counters on private frame tapes

A counter captures a register once and subsequently decreases independently of
changes to source registers in the loop body. The scan restores scratch and
preserves all language data and every other saved counter.
-/

namespace PCP.Lang.MachineLayout

open Turing Turing.TM2 StateTransition PCP.Machine FiniteBlocks ArithmeticBlocks

variable {R Q : ℕ} {F : Type} [DecidableEq F] [Fintype F]

abbrev captureCounter (x : Fin R) (j : F) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockCopy.block (reg x) (work 4) (framePort j)

/-- Capturing an initially empty private counter retains the original register. -/
theorem captureCounter_executes (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (x : Fin R) (j : F) (hj : frame j = []) :
    (captureCounter x j).Executes input output (tapes st frame)
      (tapes st (Function.update frame j (natTape (st.regs x))))
      (2 * Nat.size (st.regs x) + 2) := by
  have h := BlockCopy.executes (reg x) (work 4) (framePort j) input output
    (by simp [reg, work]) (by simp [reg, framePort]) (by simp [work, framePort])
    (tapes st frame) (by rfl)
  simpa only [tapes_reg, tapes_frame, hj, List.append_nil, natTape_length,
    tapes_update_frame] using h

abbrev storeCounter (j : F) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (BlockCleanup.one (framePort j))
    (BlockControl.sequence (BlockCopy.block (work 3) (work 4) (framePort j))
      (BlockCleanup.one (work 3)))

/-- Only the designated frame tape changes when a computed counter value is stored. -/
theorem storeCounter_executes (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (j : F) (v : ℕ) :
    (storeCounter j).Executes input output
      (Function.update (tapes st frame) (work 3) (natTape v))
      (tapes st (Function.update frame j (natTape v)))
      ((frame j).length + 3 * Nat.size v + 10) := by
  let S := Function.update (tapes st frame) (work 3) (natTape v)
  let T := Function.update S (framePort j) []
  let U := Function.update T (framePort j) (natTape v)
  have hs : S (framePort j) = frame j := by simp [S, work, framePort, tapes]
  have ht3 : T (work 3) = natTape v := by simp [T, S, framePort, work]
  have ht4 : T (work 4) = [] := by simp [T, S, framePort, work, tapes]
  have htj : T (framePort j) = [] := by simp [T]
  have hu3 : U (work 3) = natTape v := by simp [U, T, S, framePort, work]
  have hfinal : Function.update U (work 3) [] =
      tapes st (Function.update frame j (natTape v)) := by
    rw [tapes_update_frame]
    funext k
    by_cases hj : k = framePort j
    · subst k; simp [U, T, S, framePort, work]
    · by_cases h3 : k = work 3
      · subst k; simp [U, T, S, framePort, work, tapes]
      · simp [U, T, S, Function.update_of_ne hj, Function.update_of_ne h3]
  have hc := clear_executes input output (framePort j) S
  have hp := BlockCopy.executes (work 3) (work 4) (framePort j) input output
    (by simp [work]) (by simp [work, framePort]) (by simp [work, framePort]) T ht4
  have hr := clear_executes input output (work 3) U
  simp only [ht3, htj, List.append_nil, natTape_length] at hp
  change (BlockCopy.block (work 3) (work 4) (framePort j)).Executes input output T U
    (2 * Nat.size v + 2) at hp
  rw [hu3, natTape_length, hfinal] at hr
  rw [hs] at hc
  have h := Block.Executes.seq input output hc (Block.Executes.seq input output hp hr)
  exact h.mono input output (by omega)

abbrev decreaseCounter (j : F) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (BlockCopy.block (framePort j) (work 4) (work 0))
    (BlockControl.sequence (BlockWrite.block (work 1) (natTape 1))
      (BlockControl.sequence (BasicOp.sub.placed arithmeticPorts) (storeCounter j)))

/-- Decrement a canonical binary saved counter, including its zero boundary. -/
theorem decreaseCounter_executes (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (j : F) (n : ℕ) (hj : frame j = natTape n) :
    (decreaseCounter j).Executes input output (tapes st frame)
      (tapes st (Function.update frame j (natTape (n - 1))))
      (32 * (Nat.size n + 1)) := by
  let T := Function.update (tapes st frame) (work 0) (natTape n)
  have hc := BlockCopy.executes (framePort j) (work 4) (work 0) input output
    (by simp [framePort, work]) (by simp [framePort, work]) (by simp [work])
    (tapes st frame) (by rfl)
  simp only [tapes_frame, hj, tapes_work, List.append_nil, natTape_length] at hc
  have hw := BlockWrite.executes (work 1) input output (natTape 1) T
  have ht1 : T (work 1) = [] := by simp [T, work, tapes]
  simp only [ht1, List.append_nil] at hw
  have ho := compute_basic_executes .sub input output st frame n 1
  have hs := storeCounter_executes input output st frame j (n - 1)
  have h := Block.Executes.seq input output hc
    (Block.Executes.seq input output hw (Block.Executes.seq input output ho hs))
  apply h.mono input output
  rw [hj, natTape_length]
  have hsize := Nat.size_le_size (Nat.sub_le n 1)
  have hmax : max (Nat.size n) (Nat.size 1) ≤ Nat.size n + 1 := by simp
  omega

end PCP.Lang.MachineLayout
