import PCP.Complexity.LangStructuredMachine
import PCP.Complexity.BlockCleanupMachine

/-!
# Input, output, and complete cleanup for compiled programs

The fixed cleanup list is enumerated directly from register indices and syntax,
without choosing an ordering of a finite set. It drains every physical tape
except the designated output. Both the compiler machine and its finite cleanup
code are ordinary executable definitions.
-/

namespace PCP.Lang.Compiler

open Turing PCP.Machine FiniteBlocks MachineLayout

variable {R Q : ℕ}

/-- Explicit executable enumeration of all private counter tapes. -/
def counterList : (s : Stmt R Q) → List (Counters s)
  | .seq s t | .ite _ s t => (counterList s).map Sum.inl ++ (counterList t).map Sum.inr
  | .loop _ s => .inl () :: (counterList s).map Sum.inr
  | .skip | .assign _ _ | .push _ _ | .pop _ _ _ | .len _ _ |
      .rev _ | .copy _ _ | .revApp _ _ => []

/-- Every syntactic private counter occurs in the static cleanup enumeration. -/
theorem mem_counterList (s : Stmt R Q) (j : Counters s) : j ∈ counterList s := by
  induction s with
  | seq s t hs ht | ite x s t hs ht =>
      cases j with
      | inl j => exact List.mem_append_left _ (List.mem_map.mpr ⟨j, hs j, rfl⟩)
      | inr j => exact List.mem_append_right _ (List.mem_map.mpr ⟨j, ht j, rfl⟩)
  | loop x s hs =>
      cases j with
      | inl j => cases j; exact List.mem_cons_self
      | inr j => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, hs j, rfl⟩)
  | _ => exact j.elim

/-- All physical tapes of a whole program, with no external caller frame. -/
abbrev ProgramTapes (P : Prog) := Tapes P.R P.Q (Counters P.body ⊕ Empty)

/-- The public input tape is source list zero. -/
def inputTape (P : Prog) : ProgramTapes P := list P.inL

/-- The public output tape is source list one. -/
def outputTape (P : Prog) : ProgramTapes P := list P.outL

/-- A constructive list of every physical tape index. -/
def allTapes (P : Prog) : List (ProgramTapes P) :=
  (List.finRange P.R).map reg ++ (List.finRange P.Q).map list ++
    (List.finRange 8).map work ++ (counterList P.body).map (fun j => framePort (.inl j))

/-- The enumeration covers all data, scratch, and private counter tapes. -/
theorem mem_allTapes (P : Prog) (k : ProgramTapes P) : k ∈ allTapes P := by
  rcases k with (x | L) | (i | (j | e))
  · simp [allTapes, reg, List.mem_finRange]
  · simp [allTapes, list, List.mem_finRange]
  · simp [allTapes, work, List.mem_finRange]
  · simp only [allTapes, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨j, mem_counterList P.body j, rfl⟩)
  · exact e.elim

/-- Output is preserved while every other tape is drained. -/
def cleanup (P : Prog) : List (ProgramTapes P) :=
  (allTapes P).filter (fun k => decide (k ≠ outputTape P))

/-- Cleanup's membership test is exactly inequality with the fixed output port. -/
theorem mem_cleanup (P : Prog) (k : ProgramTapes P) : k ∈ cleanup P ↔ k ≠ outputTape P := by
  simp only [cleanup, List.mem_filter, mem_allTapes P k, decide_eq_true_eq, true_and]

/-- Compile the body and then execute actual fixed-tape cleanup. -/
abbrev programBlock (P : Prog) : Block (ProgramTapes P) (fun _ => Sym) :=
  BlockControl.sequence (block P.body Empty) (BlockCleanup.block (cleanup P))

/-- A concrete finite machine whose input and output symbols are exactly `Sym`. -/
abbrev programMachine (P : Prog) : FinTM2 := (programBlock P).machine (inputTape P) (outputTape P)

/-- The polynomial coefficient includes every fixed cleanup tape and control transition. -/
def programCoefficient (P : Prog) : ℕ := coefficient P.body + 5 * (cleanup P).length + 4

/-- The machine initialization is precisely the source initial state with empty private storage. -/
theorem program_init (P : Prog) (xs : List ℕ) :
    initList (programMachine P) (encodeNats xs) =
      ⟨some (programBlock P).entry, (programBlock P).initial,
        boundary P.body (P.init xs) (fun _ : Empty => [])⟩ := by
  dsimp only [initList]
  congr 1
  funext k
  rcases k with (x | L) | (i | (j | e))
  · simp [inputTape, list, boundary, tapes, stateTapes, Prog.init]
    rfl
  · by_cases hL : L = P.inL
    · subst L
      simp [inputTape, list, boundary, tapes, stateTapes, Prog.init]
    · simp [inputTape, list, boundary, tapes, stateTapes, Prog.init, hL]
      rfl
  · simp [inputTape, list, boundary, tapes]
  · simp [inputTape, list, boundary, tapes, zeroFrame]
  · exact e.elim

/-- After cleanup, the complete configuration is the machine model's required `haltList`. -/
theorem program_halt (P : Prog) (st : State P.R P.Q) :
    haltList (programMachine P) (encodeNats (st.lists P.outL)) =
      ⟨none, (programBlock P).initial,
        BlockCleanup.clear (cleanup P) (boundary P.body st (fun _ : Empty => []))⟩ := by
  dsimp only [haltList]
  congr 1
  funext k
  by_cases hk : k = outputTape P
  · subst k
    simp [outputTape, list, BlockCleanup.clear, mem_cleanup,
      boundary, tapes, stateTapes]
  · simp [BlockCleanup.clear, mem_cleanup, hk]

/-- Every boundary tape is bounded by the source size invariant; private tapes are empty. -/
theorem boundary_length_le (P : Prog) (st : State P.R P.Q) (B : ℕ) (hB : st.Sized B)
    (k : ProgramTapes P) : (boundary P.body st (fun _ : Empty => []) k).length ≤ B := by
  rcases k with d | (i | (j | e))
  · exact stateTapes_length_le hB d
  · exact Nat.zero_le B
  · exact Nat.zero_le B
  · exact e.elim

/-- The entire cleanup cost is linear in the final source-space bound. -/
theorem cleanup_budget (P : Prog) (st : State P.R P.Q) (B : ℕ) (hB : st.Sized B) :
    ((cleanup P).map (fun k => (boundary P.body st (fun _ : Empty => []) k).length)).sum +
      4 * (cleanup P).length + 1 ≤ (cleanup P).length * B + 4 * (cleanup P).length + 1 := by
  have hsum :
      ((cleanup P).map (fun k => (boundary P.body st (fun _ : Empty => []) k).length)).sum ≤
      ((cleanup P).map (fun _ => B)).sum := by
    apply List.sum_le_sum
    intro k _
    exact boundary_length_le P st B hB k
  simpa using Nat.add_le_add_right (Nat.add_le_add_right hsum (4 * (cleanup P).length)) 1

end PCP.Lang.Compiler
