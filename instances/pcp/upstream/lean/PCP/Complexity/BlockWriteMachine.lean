import PCP.Complexity.BlockExecution

/-!
# Fixed words as finite push statements

A program constant is expanded into a fixed statement tree. Its cells are never
stored in unbounded control; each is a literal in a push instruction. The tree
executes in one TM2 transition and preserves every other tape.
-/

namespace PCP.Machine.BlockWrite

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition FiniteBlocks

variable {K A L V : Type}

/-- Expand a fixed word into pushes followed by the supplied continuation. -/
def pushWord (dest : K) : List A → Stmt (fun _ : K => A) L V → Stmt (fun _ : K => A) L V
  | [], q => q
  | a :: xs, q => pushWord dest xs (.push dest (fun _ => a) q)

variable [DecidableEq K]

/-- The reversed nesting of pushes produces the original order at the stack head. -/
theorem stepAux_pushWord (dest : K) (xs : List A) (q : Stmt (fun _ : K => A) L V)
    (v : V) (S : K → List A) :
    stepAux (pushWord dest xs q) v S =
      stepAux q v (Function.update S dest (xs ++ S dest)) := by
  induction xs generalizing q with
  | nil => simp [pushWord]
  | cons a xs ih =>
      rw [pushWord, ih]
      simp only [stepAux, Function.update_self, Function.update_idem, List.cons_append]

/-- A constant-length instruction tree with trivial reset control. -/
abbrev block (dest : K) (xs : List A) : Block K (fun _ => A) where
  Label := Unit
  Control := Unit
  entry := ()
  initial := ()
  code _ := pushWord dest xs .halt

variable [Fintype K] [Fintype A]

/-- Actual fixed-word output in one physical transition. -/
theorem executes (dest input output : K) (xs : List A) (S : K → List A) :
    (block dest xs).Executes input output S (Function.update S dest (xs ++ S dest)) 1 := by
  refine ⟨1, le_rfl, ?_⟩
  change some (stepAux (pushWord dest xs .halt) () S) = _
  rw [stepAux_pushWord]
  rfl

end PCP.Machine.BlockWrite
