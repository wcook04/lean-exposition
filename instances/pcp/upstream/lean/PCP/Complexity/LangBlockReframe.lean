import PCP.Complexity.LangMachineState
import PCP.Complexity.BlockExecution
import PCP.Complexity.PlacedBlock

/-!
# Reframing compiled blocks for nested saved counters

Only the caller-frame indices are permuted. Data registers and the eight shared
scratch tapes keep their physical positions. Exact reset traces transfer across
the static permutation, so independently compiled substatements can share one
layout while treating each other's private saved counters as untouched frame.
-/

namespace PCP.Lang.MachineLayout

open Turing Turing.TM2 StateTransition PCP.Machine FiniteBlocks

variable {R Q : ℕ} {F G : Type} [DecidableEq F] [Fintype F]
  [DecidableEq G] [Fintype G]

/-- Extend a caller-frame permutation by identity on program data and scratch. -/
def frameEquiv (e : F ≃ G) : Tapes R Q F ≃ Tapes R Q G :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) e)

/-- The finite code is renamed by an executable static forward map. -/
def reframe (b : Block (Tapes R Q F) (fun _ => Sym)) (e : F ≃ G) :
    Block (Tapes R Q G) (fun _ => Sym) := b.rename (frameEquiv e)

omit [DecidableEq F] [Fintype F] [DecidableEq G] [Fintype G] in
/-- Reading a permuted boundary changes only the caller's frame function. -/
theorem tapes_frameEquiv (e : F ≃ G) (st : State R Q) (frame : G → List Sym) :
    (fun k => tapes st frame (frameEquiv e k)) = tapes st (fun j => frame (e j)) := by
  funext k
  rcases k with d | (i | j) <;> rfl

/-- Reset traces and their exact budgets survive frame reassociation or permutation. -/
theorem reframe_executes (b : Block (Tapes R Q F) (fun _ => Sym)) (e : F ≃ G)
    (input output : Tapes R Q G) (st finish : State R Q) (frame : G → List Sym) (budget : ℕ)
    (h : b.Executes (work 0) (work 0)
      (tapes st (fun j => frame (e j))) (tapes finish (fun j => frame (e j))) budget) :
    (reframe b e).Executes input output (tapes st frame) (tapes finish frame) budget := by
  obtain ⟨steps, hs, ht⟩ := h
  rw [← tapes_frameEquiv e st frame, ← tapes_frameEquiv e finish frame] at ht
  exact ⟨steps, hs, rename_trace b (work 0) (work 0) (frameEquiv e)
    input output (tapes st frame) (tapes finish frame) b.initial steps ht⟩

omit [Fintype F] [DecidableEq G] [Fintype G] in
/-- Updating a saved counter in the frame is exactly a physical tape replacement. -/
theorem tapes_update_frame (st : State R Q) (frame : F → List Sym) (j : F) (xs : List Sym) :
    tapes st (Function.update frame j xs) =
      Function.update (tapes st frame) (framePort j) xs := by
  funext k
  rcases k with d | (i | k)
  · simp [tapes, framePort]
  · simp [tapes, framePort]
  · by_cases h : k = j
    · subst k; simp [tapes, framePort]
    · simp [tapes, framePort, Function.update, h]

end PCP.Lang.MachineLayout
