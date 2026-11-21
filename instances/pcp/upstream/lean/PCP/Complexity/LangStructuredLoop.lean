import PCP.Complexity.LangStructuredMachine
import PCP.Complexity.LangCompilerBudget
import PCP.Complexity.BlockLoopExecution

/-!
# Correct compilation of counted loops

The saved counter is captured once, independent of subsequent writes to the
source register. An invariant bounds every body state by the actual remaining
source charge. Actual decrement and body traces are composed through the checked
countdown controller; the resulting overhead is polynomial in that charge.
-/

namespace PCP.Lang.Compiler

open Turing PCP.Machine FiniteBlocks MachineLayout

variable {R Q : ℕ}

/-- Correctness of the particular finite machine built from this source statement. -/
def Correct (s : Stmt R Q) : Prop :=
  ∀ (F : Type) [DecidableEq F] [Fintype F] (input output : Tapes R Q (Counters s ⊕ F))
    (st : State R Q) (frame : F → List Sym) (B : ℕ), st.Sized B →
    (block s F).Executes input output (boundary s st frame)
      (boundary s (s.run st).1 frame) (coefficient s * (B + (s.run st).2 + 1) ^ degree s)

/-- A correct compiled body yields a correct concrete saved-counter loop. -/
theorem correct_loop (x : Fin R) (s : Stmt R Q) (hs : Correct s) : Correct (.loop x s) := by
  intro F _ _ input output st frame B hB
  let n := st.regs x
  let width := Nat.size n + 1
  let N := B + ((Stmt.loop x s).run st).2 + 1
  let counter : (Unit ⊕ Counters s) ⊕ F := .inl (.inl ())
  let body := reframe (block s (Unit ⊕ F)) (rightFrame Unit (Counters s) F)
  let S := fun (i : ℕ) (a : State R Q) => tapes a (loopFrame (C := Counters s) (natTape i) frame)
  let Inv := fun (i : ℕ) (a : State R Q) => ∃ b, a.Sized b ∧
    b + (iterate s.run width i a).2 + 1 ≤ N ∧ Nat.size i + 1 ≤ N
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNP : N ≤ N ^ degree s := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ degree s := Nat.pow_le_pow_right hN (by have := degree_ge_two s; omega)
  have hP : 1 ≤ N ^ degree s := one_le_pow₀ hN
  have hbody : ∀ i a, Inv (i + 1) a →
      body.Executes input output (S i a) (S i (s.run a).1)
        (coefficient s * N ^ degree s) := by
    intro i a hi
    obtain ⟨b, hb, hcost, _⟩ := hi
    let fr : Unit ⊕ F → List Sym := fun
      | .inl _ => natTape i
      | .inr j => frame j
    have hraw := hs (Unit ⊕ F) (work 0) (work 0) a fr b hb
    have hf : (fun j => loopFrame (C := Counters s) (natTape i) frame
        (rightFrame Unit (Counters s) F j)) = zeroFrame (C := Counters s) fr := by
      funext j
      rcases j with c | (u | j) <;> rfl
    have hplaced := reframe_executes (block s (Unit ⊕ F)) (rightFrame Unit (Counters s) F)
      input output a (s.run a).1 (loopFrame (C := Counters s) (natTape i) frame)
      (coefficient s * (b + (s.run a).2 + 1) ^ degree s) (by
        rw [hf]
        exact hraw)
    apply Block.Executes.mono input output hplaced
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp only [iterate] at hcost
    omega
  have hdec : ∀ i a, Inv (i + 1) a →
      (decreaseCounter counter).Executes input output (S (i + 1) a) (S i a)
        (32 * N ^ degree s) := by
    intro i a hi
    obtain ⟨_, _, _, hsize⟩ := hi
    have hd := decreaseCounter_executes input output a
      (loopFrame (C := Counters s) (natTape (i + 1)) frame) counter (i + 1) (by rfl)
    simp only [Nat.add_sub_cancel_right, counter, loopFrame_update] at hd
    exact Block.Executes.mono input output hd
      (Nat.mul_le_mul_left 32 (hsize.trans hNP))
  have hinv : ∀ i a, Inv (i + 1) a → Inv i (s.run a).1 := by
    intro i a hi
    obtain ⟨b, hb, hcost, hsize⟩ := hi
    refine ⟨b + (s.run a).2, s.run_sized a b hb, ?_, ?_⟩
    · dsimp only [iterate] at hcost
      omega
    · exact (Nat.add_le_add_right (Nat.size_le_size (Nat.le_succ i)) 1).trans hsize
  have hinit : Inv n st := by
    refine ⟨B, hB, ?_, ?_⟩
    · dsimp [N, Stmt.run, n, width]
      omega
    · dsimp [N, Stmt.run, n, width]
      omega
  have hlo := BlockLoop.executes body (decreaseCounter counter) (framePort counter)
    input output S (fun a => (s.run a).1) Inv (32 * N ^ degree s)
    (coefficient s * N ^ degree s)
    (by intro a _; rfl)
    (by
      intro i a _ hnil
      have h : natTape (i + 1) = natTape 0 := hnil
      have := natTape_injective h
      omega)
    hdec hbody hinv n st hinit
  have hcount : n ≤ N := by
    have h := iterations_le_cost s.run width (by dsimp [width]; omega) n st
    obtain ⟨b, _, hb, _⟩ := hinit
    omega
  have hwidth : width ≤ N := hinit.choose_spec.2.2
  have hloopbound : n * (32 * N ^ degree s + coefficient s * N ^ degree s + 2) + 1 ≤
      n * ((coefficient s + 34) * N ^ degree s) + 1 := by
    have hfactor : 32 * N ^ degree s + coefficient s * N ^ degree s + 2 ≤
        (coefficient s + 34) * N ^ degree s := by nlinarith
    exact Nat.add_le_add_right (Nat.mul_le_mul_left n hfactor) 1
  have hlo' := Block.Executes.mono input output hlo hloopbound
  have hs0 : S 0 ((fun a => (s.run a).1)^[n] st) =
      boundary (.loop x s) ((Stmt.loop x s).run st).1 frame := by
    dsimp only [S]
    rw [show natTape 0 = [] from rfl, loopFrame_empty, ← iterate_state s.run width]
    rfl
  rw [hs0] at hlo'
  have hc := captureCounter_executes input output st
    (zeroFrame (C := Unit ⊕ Counters s) frame) x counter (by rfl)
  have hcapture : Function.update (zeroFrame (C := Unit ⊕ Counters s) frame) counter
      (natTape (st.regs x)) = loopFrame (C := Counters s) (natTape n) frame := by
    rw [← loopFrame_empty, loopFrame_update]
  rw [hcapture] at hc
  have hall := Block.Executes.seq input output hc hlo'
  apply Block.Executes.mono input output hall
  change 2 * Nat.size (st.regs x) + 2 +
    (n * ((coefficient s + 34) * N ^ degree s) + 1) + 3 ≤
      (coefficient s + 128) * N ^ (degree s + 1)
  have hfinal := loop_budget (coefficient s) (degree s) N n width hN hcount hwidth
  convert hfinal using 1

end PCP.Lang.Compiler
