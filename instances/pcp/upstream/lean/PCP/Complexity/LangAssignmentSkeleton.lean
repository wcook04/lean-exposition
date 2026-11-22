import PCP.Complexity.LangArithmeticBlocks

/-!
# Operand loading and register write-back for compiled binary operations

This actual finite call graph is shared by multiplication, division and modulo.
Only the middle computation varies. Its hypothesis is an actual bounded trace
on materialized operands; the rest of the assignment is constructed and proved
here, with all register aliases handled by copying before target replacement.
-/

namespace PCP.Lang.MachineLayout

open Turing Turing.TM2 StateTransition PCP.Machine FiniteBlocks

variable {R Q : ℕ} {F : Type} [DecidableEq F] [Fintype F]

/-- An explicit copy, copy, compute, clear-and-copy call graph. -/
abbrev assignWith (computation : Block (Tapes R Q F) (fun _ => Sym)) (z x y : Fin R) :
    Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (loadReg x 0)
    (BlockControl.sequence (loadReg y 1) (BlockControl.sequence computation (storeReg z)))

/-- Compose the actual operation trace with physical operand loads and result write-back. -/
theorem assignWith_executes (computation : Block (Tapes R Q F) (fun _ => Sym))
    (input output : Tapes R Q F) (st : State R Q) (frame : F → List Sym)
    (z x y : Fin R) (v budget : ℕ)
    (ho : computation.Executes input output
      (Function.update (Function.update (tapes st frame) (work 0) (natTape (st.regs x)))
        (work 1) (natTape (st.regs y)))
      (Function.update (tapes st frame) (work 3) (natTape v)) budget) :
    (assignWith computation z x y).Executes input output (tapes st frame)
      (tapes (setReg st z v) frame)
      (2 * Nat.size (st.regs x) + 2 * Nat.size (st.regs y) + budget +
        Nat.size (st.regs z) + 3 * Nat.size v + 23) := by
  let S := tapes st frame
  let T := Function.update S (work 0) (natTape (st.regs x))
  have hx := BlockCopy.executes (reg x) (work 4) (work 0) input output
    (by simp [reg, work]) (by simp [reg, work]) (by simp [work]) S (by rfl)
  simp only [S, tapes_reg, tapes_work, List.append_nil, natTape_length] at hx
  have hy := BlockCopy.executes (reg y) (work 4) (work 1) input output
    (by simp [reg, work]) (by simp [reg, work]) (by simp [work]) T
    (by simp [T, S, work, tapes])
  have hty : T (reg y) = natTape (st.regs y) := by simp [T, S, reg, work, tapes, stateTapes]
  have ht1 : T (work 1) = [] := by simp [T, S, work, tapes]
  simp only [hty, ht1, List.append_nil, natTape_length] at hy
  have hs := storeReg_executes input output st frame z v
  have h := Block.Executes.seq input output hx
    (Block.Executes.seq input output hy (Block.Executes.seq input output ho hs))
  convert h using 1
  omega

/-- A quadratic operation bound gives a quadratic assignment bound in the language charge. -/
theorem assignment_budget_le (a b old result B C : ℕ) (hOld : old ≤ B) :
    2 * a + 2 * b + C * (a + b + 1) ^ 2 + old + 3 * result + 23 ≤
      (C + 32) * (B + (a + b + result + 1) + 1) ^ 2 := by
  let N := B + (a + b + result + 1) + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hsq : N ≤ N ^ 2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left N hN
  have hab : a + b + 1 ≤ N := by dsimp [N]; omega
  have hpow := Nat.pow_le_pow_left hab 2
  have hmul := Nat.mul_le_mul_left C hpow
  have hlin : 2 * a + 2 * b + old + 3 * result + 23 ≤ 32 * N := by dsimp [N]; omega
  change _ ≤ (C + 32) * N ^ 2
  nlinarith

end PCP.Lang.MachineLayout
