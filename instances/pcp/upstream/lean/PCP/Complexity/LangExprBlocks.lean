import PCP.Complexity.LangRegisterBlocks
import PCP.Complexity.LangProductBlocks
import PCP.Complexity.LangDivisionBlocks

/-!
# Complete materialized compilation of language expressions

Every expression constructor selects actual finite tape code. The single theorem
below identifies the resulting assignment with the source semantics and proves
one uniform quadratic runtime bound, including arbitrary register aliases and
zero divisors. No expression operation is left as an assumed callback.
-/

namespace PCP.Lang.MachineLayout

open Turing PCP.Machine FiniteBlocks

variable {R Q : ℕ} {F : Type} [DecidableEq F] [Fintype F]

/-- Compile every source expression to physical operand scans and tape updates. -/
def assignExpr (z : Fin R) : Expr R → Block (Tapes R Q F) (fun _ => Sym)
  | .const n => assignConst z n
  | .var x => assignVar z x
  | .add x y => assignBasic .add z x y
  | .sub x y => assignBasic .sub z x y
  | .mul x y => assignMul z x y
  | .div x y => assignDiv true z x y
  | .mod x y => assignDiv false z x y
  | .eq x y => assignBasic .eq z x y
  | .lt x y => assignBasic .lt z x y

/-- Complete machine-level assignment correctness and uniform polynomial overhead. -/
theorem assignExpr_correct (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (z : Fin R) (e : Expr R) (B : ℕ) (hB : st.Sized B) :
    (assignExpr z e).Executes input output (tapes st frame)
      (tapes ((Stmt.assign z e).run st).1 frame)
      (82 * (B + ((Stmt.assign z e).run st).2 + 1) ^ 2) := by
  cases e with
  | const n =>
      exact Block.Executes.mono input output
        (assignConst_correct input output st frame z n B hB)
        (Nat.mul_le_mul_right _ (by decide : 8 ≤ 82))
  | var x =>
      exact Block.Executes.mono input output
        (assignVar_correct input output st frame z x B hB)
        (Nat.mul_le_mul_right _ (by decide : 8 ≤ 82))
  | add x y =>
      exact Block.Executes.mono input output
        (assignBasic_correct .add input output st frame z x y B hB)
        (Nat.mul_le_mul_right _ (by decide : 32 ≤ 82))
  | sub x y =>
      exact Block.Executes.mono input output
        (assignBasic_correct .sub input output st frame z x y B hB)
        (Nat.mul_le_mul_right _ (by decide : 32 ≤ 82))
  | mul x y =>
      exact Block.Executes.mono input output
        (assignMul_correct input output st frame z x y B hB)
        (Nat.mul_le_mul_right _ (by decide : 47 ≤ 82))
  | div x y => exact assignDiv_correct true input output st frame z x y B hB
  | mod x y => exact assignDiv_correct false input output st frame z x y B hB
  | eq x y =>
      exact Block.Executes.mono input output
        (assignBasic_correct .eq input output st frame z x y B hB)
        (Nat.mul_le_mul_right _ (by decide : 32 ≤ 82))
  | lt x y =>
      exact Block.Executes.mono input output
        (assignBasic_correct .lt input output st frame z x y B hB)
        (Nat.mul_le_mul_right _ (by decide : 32 ≤ 82))

end PCP.Lang.MachineLayout
