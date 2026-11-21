import PCP.Complexity.BlockExecution

/-!
# Bounded execution for a physical tape-emptiness branch

A branch peeks at one tape, runs the selected reset block, and returns with two
additional machine transitions. The selected callee sees all original contents.
-/

namespace PCP.Machine.FiniteBlocks

open Turing Turing.TM2 StateTransition

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
  (input output : K) [Fintype (Γ input)]

/-- Conditional execution includes its actual entry and return transitions. -/
theorem Block.Executes.conditional {left right : Block K Γ} {test : K}
    {S T : ∀ k, List (Γ k)} {n : ℕ}
    (h : (BlockControl.pair left right (!(S test).isEmpty)).Executes input output S T n) :
    (BlockControl.conditional left right test).Executes input output S T (n + 2) := by
  obtain ⟨steps, hs, ht⟩ := h
  exact ⟨steps + 2, by omega,
    BlockControl.conditional_trace left right input output test S T steps ht⟩

/-- An empty test tape selects the left callee without consuming a cell. -/
theorem Block.Executes.ifEmpty {left right : Block K Γ} {test : K}
    {S T : ∀ k, List (Γ k)} {n : ℕ} (hempty : S test = [])
    (h : left.Executes input output S T n) :
    (BlockControl.conditional left right test).Executes input output S T (n + 2) := by
  apply Block.Executes.conditional input output
  simpa only [hempty, List.isEmpty_nil, Bool.not_true, BlockControl.pair] using h

/-- A nonempty test tape selects the right callee without consuming a cell. -/
theorem Block.Executes.ifNonempty {left right : Block K Γ} {test : K}
    {S T : ∀ k, List (Γ k)} {n : ℕ} (hne : S test ≠ [])
    (h : right.Executes input output S T n) :
    (BlockControl.conditional left right test).Executes input output S T (n + 2) := by
  apply Block.Executes.conditional input output
  have he : (S test).isEmpty = false := by
    cases hs : S test with
    | nil => exact False.elim (hne hs)
    | cons c cs => rfl
  simpa only [he, Bool.not_false, BlockControl.pair] using h

end PCP.Machine.FiniteBlocks
