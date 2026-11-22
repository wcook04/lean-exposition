import PCP.Complexity.LangStructuredLoop
import PCP.Complexity.BlockConditionalExecution

/-!
# Correctness of every compiled structured statement

Structural induction combines the actual arithmetic/list machines, finite
sequencing and conditionals, and the proved saved-counter loop. The resulting
certificate covers the entire source language with polynomial charged overhead.
-/

namespace PCP.Lang.Compiler

open Turing PCP.Machine FiniteBlocks MachineLayout

variable {R Q : ℕ}

/-- Sequencing uses disjoint finite private counter sets on the same physical data tapes. -/
theorem correct_seq (s t : Stmt R Q) (hs : Correct s) (ht : Correct t) : Correct (.seq s t) := by
  intro F _ _ input output st frame B hB
  have hslocal := hs (Counters t ⊕ F) (work 0) (work 0) st (zeroFrame frame) B hB
  have hleft := reframe_executes (block s (Counters t ⊕ F))
    (leftFrame (Counters s) (Counters t) F) input output st (s.run st).1
    (zeroFrame (C := Counters s ⊕ Counters t) frame) _ (by
      simpa only [boundary, zeroFrame_left] using hslocal)
  have hmiddle := s.run_sized st B hB
  have htlocal := ht (Counters s ⊕ F) (work 0) (work 0) (s.run st).1
    (zeroFrame frame) (B + (s.run st).2) hmiddle
  have hright := reframe_executes (block t (Counters s ⊕ F))
    (rightFrame (Counters s) (Counters t) F) input output (s.run st).1 (t.run (s.run st).1).1
    (zeroFrame (C := Counters s ⊕ Counters t) frame) _ (by
      simpa only [boundary, zeroFrame_right] using htlocal)
  apply Block.Executes.mono input output (Block.Executes.seq input output hleft hright)
  exact sequence_budget (coefficient s) (coefficient t) (degree s) (degree t) B
    (s.run st).2 (t.run (s.run st).1).2

/-- Tape emptiness implements the source zero test without consuming the tested register. -/
theorem correct_ite (x : Fin R) (s t : Stmt R Q) (hs : Correct s) (ht : Correct t) :
    Correct (.ite x s t) := by
  intro F _ _ input output st frame B hB
  let left := reframe (block t (Counters s ⊕ F)) (rightFrame (Counters s) (Counters t) F)
  let right := reframe (block s (Counters t ⊕ F)) (leftFrame (Counters s) (Counters t) F)
  by_cases hx : st.regs x = 0
  · have hlocal := ht (Counters s ⊕ F) (work 0) (work 0) st (zeroFrame frame) B hB
    have hbranch := reframe_executes (block t (Counters s ⊕ F))
      (rightFrame (Counters s) (Counters t) F) input output st (t.run st).1
      (zeroFrame (C := Counters s ⊕ Counters t) frame) _ (by
        simpa only [boundary, zeroFrame_right] using hlocal)
    have htest : tapes st (zeroFrame (C := Counters s ⊕ Counters t) frame) (reg x) = [] := by
      rw [tapes_reg, hx]; rfl
    have hrun := Block.Executes.ifEmpty (right := right) input output htest hbranch
    simp only [Stmt.run, ite_eq_right (not_ne_iff.mpr hx)]
    apply Block.Executes.mono input output hrun
    have hb := branch_budget (coefficient t) (coefficient s) (degree t) (degree s)
      B (t.run st).2 (Nat.size (st.regs x) + 1) (by omega)
    simpa only [coefficient, degree, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.max_comm] using hb
  · have hlocal := hs (Counters t ⊕ F) (work 0) (work 0) st (zeroFrame frame) B hB
    have hbranch := reframe_executes (block s (Counters t ⊕ F))
      (leftFrame (Counters s) (Counters t) F) input output st (s.run st).1
      (zeroFrame (C := Counters s ⊕ Counters t) frame) _ (by
        simpa only [boundary, zeroFrame_left] using hlocal)
    have htest : tapes st (zeroFrame (C := Counters s ⊕ Counters t) frame) (reg x) ≠ [] := by
      intro he
      exact hx (natTape_injective he)
    have hrun := Block.Executes.ifNonempty (left := left) input output htest hbranch
    simp only [Stmt.run, ite_eq_left hx]
    apply Block.Executes.mono input output hrun
    simpa only [coefficient, degree, Nat.add_assoc] using
      branch_budget (coefficient s) (coefficient t) (degree s) (degree t)
        B (s.run st).2 (Nat.size (st.regs x) + 1) (by omega)

/-- Atomic materialized scans fit a single common compiler coefficient. -/
theorem atomic_budget (c B cost : ℕ) (hc : c ≤ 128) :
    c * (B + 1) ^ 2 ≤ 128 * (B + cost + 1) ^ 2 :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_left (by omega) 2)

/-- Every source statement has its actual finite-block correctness certificate. -/
theorem correct (s : Stmt R Q) : Correct s := by
  induction s with
  | skip =>
      intro F _ _ input output st frame B _
      apply Block.Executes.mono input output (empty_executes input output (boundary .skip st frame))
      change 1 ≤ 128 * (B + 1 + 1) ^ 2
      have hp : 1 ≤ (B + 1 + 1) ^ 2 := one_le_pow₀ (by omega)
      omega
  | assign z e =>
      intro F _ _ input output st frame B hB
      exact Block.Executes.mono input output
        (assignExpr_correct input output st (zeroFrame frame) z e B hB)
        (Nat.mul_le_mul_right _ (by decide : 82 ≤ 128))
  | push L x =>
      intro F _ _ input output st frame B hB
      exact Block.Executes.mono input output
        (ListBlocks.push_sized L x input output st (zeroFrame frame) B hB)
        (atomic_budget 10 B _ (by decide))
  | pop L x flag =>
      intro F _ _ input output st frame B hB
      exact Block.Executes.mono input output
        (ListBlocks.pop_sized L x flag input output st (zeroFrame frame) B hB)
        (atomic_budget 66 B _ (by decide))
  | len L x =>
      intro F _ _ input output st frame B hB
      exact Block.Executes.mono input output
        (ListBlocks.len_sized L x input output st (zeroFrame frame) B hB)
        (atomic_budget 32 B _ (by decide))
  | rev L =>
      intro F _ _ input output st frame B hB
      exact Block.Executes.mono input output
        (ListBlocks.rev_sized L input output st (zeroFrame frame) B hB)
        (atomic_budget 32 B _ (by decide))
  | copy L M =>
      intro F _ _ input output st frame B hB
      exact Block.Executes.mono input output
        (ListBlocks.copy_sized L M input output st (zeroFrame frame) B hB)
        (atomic_budget 10 B _ (by decide))
  | revApp L M =>
      intro F _ _ input output st frame B hB
      exact Block.Executes.mono input output
        (ListBlocks.revApp_sized L M input output st (zeroFrame frame) B hB)
        (atomic_budget 32 B _ (by decide))
  | seq s t hs ht => exact correct_seq s t hs ht
  | ite x s t hs ht => exact correct_ite x s t hs ht
  | loop x s hs => exact correct_loop x s hs

end PCP.Lang.Compiler
