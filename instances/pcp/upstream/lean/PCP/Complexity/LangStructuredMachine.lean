import PCP.Complexity.LangCompilerLayout
import PCP.Complexity.LangExprBlocks
import PCP.Complexity.LangListPopBlocks
import PCP.Complexity.LangListTransforms
import PCP.Complexity.LangCounterBlocks
import PCP.Complexity.BlockLoopMachine

/-!
# The concrete finite machine for every structured language statement

The program tree determines all control and private counter tapes before any
input is read. Atomic instructions are the checked materialized blocks. Static
sequencing and branching share the data tapes; a counted loop captures its entry
value once, decrements that saved tape, and calls its compiled body. No unbounded
program state or input-dependent arithmetic occurs in finite control.
-/

namespace PCP.Lang.Compiler

open Turing PCP.Machine FiniteBlocks MachineLayout

variable {R Q : ℕ}

/-- Recursive compilation builds only finite static call graphs and literal tape operations. -/
def block : (s : Stmt R Q) → (F : Type) → [DecidableEq F] → [Fintype F] →
    Block (Tapes R Q (Counters s ⊕ F)) (fun _ => Sym)
  | .skip, _, _, _ => BlockCleanup.empty
  | .assign z e, _, _, _ => assignExpr z e
  | .push L x, _, _, _ => ListBlocks.push L x
  | .pop L x flag, _, _, _ => ListBlocks.pop L x flag
  | .len L x, _, _, _ => ListBlocks.len L x
  | .rev L, _, _, _ => ListBlocks.rev L
  | .copy L M, _, _, _ => ListBlocks.copy L M
  | .revApp L M, _, _, _ => ListBlocks.revApp L M
  | .seq s t, F, _, _ =>
      BlockControl.sequence
        (reframe (block s (Counters t ⊕ F)) (leftFrame (Counters s) (Counters t) F))
        (reframe (block t (Counters s ⊕ F)) (rightFrame (Counters s) (Counters t) F))
  | .ite x s t, F, _, _ =>
      BlockControl.conditional
        (reframe (block t (Counters s ⊕ F)) (rightFrame (Counters s) (Counters t) F))
        (reframe (block s (Counters t ⊕ F)) (leftFrame (Counters s) (Counters t) F))
        (reg x)
  | .loop x s, F, _, _ =>
      let counter : (Unit ⊕ Counters s) ⊕ F := .inl (.inl ())
      let body := reframe (block s (Unit ⊕ F)) (rightFrame Unit (Counters s) F)
      BlockControl.sequence (captureCounter x counter)
        (BlockLoop.loop body (decreaseCounter counter) (framePort counter))

end PCP.Lang.Compiler
