import PCP.Complexity.BlockControlMachine
import PCP.Complexity.BlockCleanupMachine
import PCP.Complexity.BlockCopyMachine

/-!
# Compositional bounded execution of reset machine blocks

The relation below means an actual finite iteration of the concrete transition
function. Its sequencing rule includes the three real control transitions. Tape
copy and clearing rules expose physical updates on arbitrary global storage.
-/

namespace PCP.Machine.FiniteBlocks

open Turing Turing.TM2 StateTransition

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}

/-- Successful execution from canonical entry to canonical return within a budget. -/
def Block.Executes (b : Block K Γ) (input output : K) [Fintype (Γ input)]
    (S T : ∀ k, List (Γ k)) (budget : ℕ) : Prop :=
  ∃ steps ≤ budget, (flip Bind.bind (b.machine input output).step)^[steps]
    (some ⟨some b.entry, b.initial, S⟩) = some ⟨none, b.initial, T⟩

variable (input output : K) [Fintype (Γ input)]

/-- Increasing the allowance does not alter the actual trace. -/
theorem Block.Executes.mono {b : Block K Γ} {S T : ∀ k, List (Γ k)} {m n : ℕ}
    (h : b.Executes input output S T m) (hmn : m ≤ n) :
    b.Executes input output S T n := by
  obtain ⟨steps, hs, ht⟩ := h
  exact ⟨steps, hs.trans hmn, ht⟩

/-- The sequence block performs both certified computations on the same physical tapes. -/
theorem Block.Executes.seq {b c : Block K Γ} {S T U : ∀ k, List (Γ k)} {m n : ℕ}
    (hb : b.Executes input output S T m) (hc : c.Executes input output T U n) :
    (BlockControl.sequence b c).Executes input output S U (m + n + 3) := by
  obtain ⟨nb, hnb, htb⟩ := hb
  obtain ⟨nc, hnc, htc⟩ := hc
  exact ⟨nb + nc + 3, by omega,
    BlockControl.sequence_trace b c input output S T U nb nc htb htc⟩

/-- One tape can be drained without inspecting or modifying any other tape. -/
theorem clear_executes (k : K) (S : ∀ k, List (Γ k)) :
    (BlockCleanup.one k).Executes input output S (Function.update S k []) ((S k).length + 1) := by
  refine ⟨(S k).length + 1, le_rfl, ?_⟩
  simpa only [Function.update_eq_self] using BlockCleanup.one_trace input output k S (S k)

/-- The terminal no-op is one actual step. -/
theorem empty_executes (S : ∀ k, List (Γ k)) :
    BlockCleanup.empty.Executes input output S S 1 := ⟨1, le_rfl, rfl⟩

end PCP.Machine.FiniteBlocks

namespace PCP.Machine.BlockCopy

open Turing Turing.TM2 StateTransition FiniteBlocks

variable {K A : Type} [DecidableEq K] [Fintype K] [Fintype A] [Inhabited A]
  (source scratch dest input output : K)
  (hss : source ≠ scratch) (hsd : source ≠ dest) (htd : scratch ≠ dest)

include hss hsd htd

/-- With empty scratch, preserving copy changes only the destination tape. -/
theorem executes (S : K → List A) (hempty : S scratch = []) :
    (block source scratch dest).Executes input output S
      (Function.update S dest (S source ++ S dest)) (2 * (S source).length + 2) := by
  have hstart : tapes source scratch dest (S source) [] (S dest) S = S := by
    rw [← hempty]
    simp only [tapes, Function.update_eq_self]
  have hfinish : tapes source scratch dest (S source) [] (S source ++ S dest) S =
      Function.update S dest (S source ++ S dest) := by
    rw [← hempty]
    simp only [tapes, Function.update_eq_self]
  refine ⟨2 * (S source).length + 2, le_rfl, ?_⟩
  have h := trace source scratch dest input output hss hsd htd (S source) (S dest) S
  simpa only [cfg, hstart, hfinish] using h

end PCP.Machine.BlockCopy
