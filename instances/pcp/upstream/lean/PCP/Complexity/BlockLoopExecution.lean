import PCP.Complexity.BlockLoopMachine
import PCP.Complexity.BlockExecution

/-!
# Invariant-based bounded execution of the concrete countdown controller

Each iteration uses the actual decrement and body traces. An abstract state
invariant tracks the remaining counter and the changing program data, while the
conclusion is a trace of the assembled finite machine on its physical tapes.
-/

namespace PCP.Machine.BlockLoop

open Turing Turing.TM2 StateTransition FiniteBlocks

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
  (body decrement : Block K Γ) (counter input output : K) [Fintype (Γ input)]
  {α : Type}

/-- Uniform bounds on actual callees compose over any decreasing-counter invariant. -/
theorem executes (S : ℕ → α → ∀ k, List (Γ k)) (next : α → α)
    (Inv : ℕ → α → Prop) (D B : ℕ)
    (hempty : ∀ a, Inv 0 a → S 0 a counter = [])
    (hnonempty : ∀ n a, Inv (n + 1) a → S (n + 1) a counter ≠ [])
    (hdec : ∀ n a, Inv (n + 1) a →
      decrement.Executes input output (S (n + 1) a) (S n a) D)
    (hbody : ∀ n a, Inv (n + 1) a →
      body.Executes input output (S n a) (S n (next a)) B)
    (hinv : ∀ n a, Inv (n + 1) a → Inv n (next a))
    (n : ℕ) (a : α) (ha : Inv n a) :
    (loop body decrement counter).Executes input output (S n a) (S 0 (next^[n] a))
      (n * (D + B + 2) + 1) := by
  induction n generalizing a with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      exact step_test_empty body decrement counter input output (S 0 a) (hempty a ha)
  | succ n ih =>
      obtain ⟨nd, hd, hdt⟩ := hdec n a ha
      obtain ⟨nb, hb, hbt⟩ := hbody n a ha
      obtain ⟨nr, hr, hrt⟩ := ih (next a) (hinv n a ha)
      refine ⟨nr + (nb + 1 + nd + 1), ?_, ?_⟩
      · rw [Nat.succ_mul]
        omega
      · change (flip Bind.bind ((loop body decrement counter).machine input output).step)^[
          nr + (nb + 1 + nd + 1)]
          (some (cfg body decrement counter input output (some (.inr false)) (S (n + 1) a))) = _
        rw [Function.iterate_add_apply,
          iteration body decrement counter input output (S (n + 1) a) (S n a)
            (S n (next a)) nd nb (hnonempty n a ha) hdt hbt]
        dsimp only [FinTM2.Cfg, Block.machine, loop, cfg] at hrt ⊢
        simpa only [Function.iterate_succ_apply] using hrt

end PCP.Machine.BlockLoop
