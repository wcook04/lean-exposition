import PCP.Complexity.LangArithmeticBlocks
import PCP.Complexity.BlockWriteMachine

/-!
# Constant and variable assignments on materialized register tapes

Constants are fixed push trees. A variable assignment first clears its distinct
target and performs a preserving copy; self-assignment is a one-step no-op.
Both implementations return with all scratch tapes empty and preserve the frame.
-/

namespace PCP.Lang.MachineLayout

open Turing Turing.TM2 StateTransition PCP.Machine FiniteBlocks

variable {R Q : ℕ} {F : Type} [DecidableEq F] [Fintype F]

/-- Literal digits are part of finite program code. -/
abbrev assignConst (z : Fin R) (n : ℕ) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (BlockCleanup.one (reg z)) (BlockWrite.block (reg z) (natTape n))

/-- Self assignment does not duplicate its operand. -/
def assignVar (z x : Fin R) : Block (Tapes R Q F) (fun _ => Sym) :=
  if z = x then BlockCleanup.empty else
    BlockControl.sequence (BlockCleanup.one (reg z)) (BlockCopy.block (reg x) (work 4) (reg z))

/-- The old target is drained and replaced by the fixed canonical numeral. -/
theorem assignConst_executes (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (z : Fin R) (n : ℕ) :
    (assignConst z n).Executes input output (tapes st frame) (tapes (setReg st z n) frame)
      (Nat.size (st.regs z) + 5) := by
  have hc := clear_executes input output (reg z) (tapes st frame)
  have hw := BlockWrite.executes (reg z) input output (natTape n)
    (Function.update (tapes st frame) (reg z) [])
  simp only [Function.update_self, List.append_nil, Function.update_idem] at hw
  simp only [tapes_reg, natTape_length] at hc
  have h := Block.Executes.seq input output hc hw
  rw [← tapes_setReg] at h
  convert h using 1

/-- Arbitrary target/source aliases are handled by the finite syntax branch. -/
theorem assignVar_executes (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (z x : Fin R) :
    (assignVar z x).Executes input output (tapes st frame)
      (tapes (setReg st z (st.regs x)) frame)
      (Nat.size (st.regs z) + 2 * Nat.size (st.regs x) + 6) := by
  by_cases hz : z = x
  · subst z
    rw [assignVar, ite_eq_left rfl, tapes_setReg, ← tapes_reg st frame x,
      Function.update_eq_self]
    exact Block.Executes.mono input output (empty_executes input output (tapes st frame))
      (by omega)
  · rw [assignVar, ite_eq_right hz]
    let T := Function.update (tapes st frame) (reg z) []
    have hc := clear_executes input output (reg z) (tapes st frame)
    have hp := BlockCopy.executes (reg x) (work 4) (reg z) input output
      (by simp [reg, work]) (by simpa [reg] using Ne.symm hz) (by simp [reg, work])
      T (by simp [T, reg, work, tapes])
    have htx : T (reg x) = natTape (st.regs x) := by
      simp [T, reg, tapes, stateTapes, Ne.symm hz]
    have htz : T (reg z) = [] := by simp [T]
    simp only [htx, htz, List.append_nil, natTape_length, T, Function.update_idem] at hp
    simp only [tapes_reg, natTape_length] at hc
    have h := Block.Executes.seq input output hc hp
    rw [← tapes_setReg] at h
    convert h using 1
    omega

/-- Uniform compiler bound for a constant assignment. -/
theorem assignConst_correct (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (z : Fin R) (n B : ℕ) (hB : st.Sized B) :
    (assignConst z n).Executes input output (tapes st frame)
      (tapes ((Stmt.assign z (.const n)).run st).1 frame)
      (8 * (B + ((Stmt.assign z (.const n)).run st).2 + 1) ^ 2) := by
  apply Block.Executes.mono input output (assignConst_executes input output st frame z n)
  have hz := hB.1 z
  simp only [Stmt.run, Expr.cost, Expr.eval, Expr.readSize]
  have hsq : B + Nat.size n + Nat.size n + 2 ≤
      (B + Nat.size n + Nat.size n + 2) ^ 2 := by
    have hN : 1 ≤ B + Nat.size n + Nat.size n + 2 := by omega
    simpa only [Nat.mul_one, pow_two] using
      Nat.mul_le_mul_left (B + Nat.size n + Nat.size n + 2) hN
  nlinarith

/-- Uniform compiler bound for a variable assignment, including self-assignment. -/
theorem assignVar_correct (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (z x : Fin R) (B : ℕ) (hB : st.Sized B) :
    (assignVar z x).Executes input output (tapes st frame)
      (tapes ((Stmt.assign z (.var x)).run st).1 frame)
      (8 * (B + ((Stmt.assign z (.var x)).run st).2 + 1) ^ 2) := by
  apply Block.Executes.mono input output (assignVar_executes input output st frame z x)
  have hz := hB.1 z
  simp only [Stmt.run, Expr.cost, Expr.eval, Expr.readSize]
  have hsq : B + Nat.size (st.regs x) + Nat.size (st.regs x) + 2 ≤
      (B + Nat.size (st.regs x) + Nat.size (st.regs x) + 2) ^ 2 := by
    have hN : 1 ≤ B + Nat.size (st.regs x) + Nat.size (st.regs x) + 2 := by omega
    simpa only [Nat.mul_one, pow_two] using
      Nat.mul_le_mul_left (B + Nat.size (st.regs x) + Nat.size (st.regs x) + 2) hN
  nlinarith

end PCP.Lang.MachineLayout
