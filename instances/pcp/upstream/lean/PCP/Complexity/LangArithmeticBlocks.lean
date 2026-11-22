import PCP.Complexity.ArithmeticBlocks
import PCP.Complexity.BlockExecution
import PCP.Complexity.LangMachineState

/-!
# Actual register assignments for the basic binary arithmetic operations

Both operands are copied to distinct work tapes before the destination is
cleared. Thus all source/destination aliases are supported. The computation and
write-back use physical scans, return with all scratch empty, and preserve every
list register and caller tape.
-/

namespace PCP.Lang.MachineLayout

open Turing Turing.TM2 StateTransition PCP.Machine FiniteBlocks ArithmeticBlocks

variable {R Q : ℕ} {F : Type} [DecidableEq F] [Fintype F]

/-- The binary arithmetic scan occupies scratch tapes zero through three. -/
def arithmeticPorts : BinaryZip.Slot → Tapes R Q F
  | .left => work 0
  | .right => work 1
  | .scratch => work 2
  | .dst => work 3

omit [DecidableEq F] [Fintype F] in
theorem arithmeticPorts_injective :
    Function.Injective (arithmeticPorts (R := R) (Q := Q) (F := F)) := by
  intro x y h
  cases x <;> cases y <;> first | rfl | simp [arithmeticPorts, work] at h

/-- Read one register without changing it; the result is prepended at a scratch port. -/
abbrev loadReg (x : Fin R) (i : Fin 8) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockCopy.block (reg x) (work 4) (work i)

/-- Clear the target, copy the result back, and drain its temporary tape. -/
abbrev storeReg (z : Fin R) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (BlockCleanup.one (reg z))
    (BlockControl.sequence (BlockCopy.block (work 3) (work 4) (reg z))
      (BlockCleanup.one (work 3)))

/-- Two preserved operand reads, actual arithmetic, then a materialized register update. -/
abbrev assignBasic (op : BasicOp) (z x y : Fin R) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (loadReg x 0)
    (BlockControl.sequence (loadReg y 1)
      (BlockControl.sequence (op.placed arithmeticPorts) (storeReg z)))

/-- The arithmetic block sees copied operands and leaves only its result tape populated. -/
theorem compute_basic_executes (op : BasicOp) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (n m : ℕ) :
    (op.placed arithmeticPorts).Executes input output
      (Function.update (Function.update (tapes st frame) (work 0) (natTape n))
        (work 1) (natTape m))
      (Function.update (tapes st frame) (work 3) (natTape (op.eval n m)))
      (2 * max (Nat.size n) (Nat.size m) + 3) := by
  apply op.placed_evals arithmeticPorts arithmeticPorts_injective input output n m
  · intro w
    cases w <;> simp [arithmeticPorts, workTapes, work, tapes, Function.update]
  · intro w
    cases w <;> simp [arithmeticPorts, workTapes, work, tapes, Function.update]
  · intro k
    have h0 := (k.property .left).symm
    have h1 := (k.property .right).symm
    have h3 := (k.property .dst).symm
    simp only [arithmeticPorts] at h0 h1 h3
    simp only [Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h3]

/-- The final three blocks replace exactly the destination register and clear the result. -/
theorem storeReg_executes (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (z : Fin R) (v : ℕ) :
    (storeReg z).Executes input output
      (Function.update (tapes st frame) (work 3) (natTape v))
      (tapes (setReg st z v) frame)
      (Nat.size (st.regs z) + 3 * Nat.size v + 10) := by
  let S := Function.update (tapes st frame) (work 3) (natTape v)
  let T := Function.update S (reg z) []
  let U := Function.update T (reg z) (natTape v)
  have hs : S (reg z) = natTape (st.regs z) := by simp [S, work, reg, tapes, stateTapes]
  have ht3 : T (work 3) = natTape v := by simp [T, S, reg, work]
  have ht4 : T (work 4) = [] := by simp [T, S, reg, work, tapes]
  have htz : T (reg z) = [] := by simp [T]
  have hu3 : U (work 3) = natTape v := by simp [U, T, S, reg, work]
  have hfinal : Function.update U (work 3) [] = tapes (setReg st z v) frame := by
    rw [tapes_setReg]
    funext k
    by_cases hz : k = reg z
    · subst k; simp [U, T, S, reg, work]
    · by_cases h3 : k = work 3
      · subst k; simp [U, T, S, reg, work, tapes]
      · simp [U, T, S, Function.update_of_ne hz, Function.update_of_ne h3]
  have hc := clear_executes input output (reg z) S
  have hp := BlockCopy.executes (work 3) (work 4) (reg z) input output
    (by simp [work]) (by simp [work, reg]) (by simp [work, reg]) T ht4
  have hr := clear_executes input output (work 3) U
  simp only [ht3, htz, List.append_nil, natTape_length] at hp
  change (BlockCopy.block (work 3) (work 4) (reg z)).Executes input output T U
    (2 * Nat.size v + 2) at hp
  rw [hu3, natTape_length, hfinal] at hr
  rw [hs, natTape_length] at hc
  have h := Block.Executes.seq input output hc (Block.Executes.seq input output hp hr)
  convert h using 1
  omega

/-- Real assignment trace with arbitrary register aliases and a linear bit-work bound. -/
theorem assignBasic_executes (op : BasicOp) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (z x y : Fin R) :
    (assignBasic op z x y).Executes input output (tapes st frame)
      (tapes (setReg st z (op.eval (st.regs x) (st.regs y))) frame)
      (2 * Nat.size (st.regs x) + 2 * Nat.size (st.regs y) +
        2 * max (Nat.size (st.regs x)) (Nat.size (st.regs y)) +
        Nat.size (st.regs z) + 3 * Nat.size (op.eval (st.regs x) (st.regs y)) + 26) := by
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
  have ho := compute_basic_executes op input output st frame (st.regs x) (st.regs y)
  have hs := storeReg_executes input output st frame z (op.eval (st.regs x) (st.regs y))
  have h := Block.Executes.seq input output hx
    (Block.Executes.seq input output hy (Block.Executes.seq input output ho hs))
  convert h using 1
  omega

/-- The exact source-language expression implemented by each basic arithmetic block. -/
def basicExpr (op : BasicOp) (x y : Fin R) : Expr R :=
  match op with
  | .add => .add x y
  | .sub => .sub x y
  | .eq => .eq x y
  | .lt => .lt x y

omit [DecidableEq F] [Fintype F] in
theorem basicExpr_eval (op : BasicOp) (r : Fin R → ℕ) (x y : Fin R) :
    (basicExpr op x y).eval r = op.eval (r x) (r y) := by cases op <;> rfl

omit [DecidableEq F] [Fintype F] in
theorem basicExpr_cost (op : BasicOp) (r : Fin R → ℕ) (x y : Fin R) :
    (basicExpr op x y).cost r =
      Nat.size (r x) + Nat.size (r y) + Nat.size (op.eval (r x) (r y)) + 1 := by
  cases op <;> rfl

/-- Compiler-facing source semantics and a uniform polynomial overhead bound. -/
theorem assignBasic_correct (op : BasicOp) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (z x y : Fin R) (B : ℕ) (hB : st.Sized B) :
    (assignBasic op z x y).Executes input output (tapes st frame)
      (tapes ((Stmt.assign z (basicExpr op x y)).run st).1 frame)
      (32 * (B + ((Stmt.assign z (basicExpr op x y)).run st).2 + 1) ^ 2) := by
  have h := assignBasic_executes op input output st frame z x y
  simp only [Stmt.run, basicExpr_eval, basicExpr_cost]
  apply Block.Executes.mono input output h
  have hz := hB.1 z
  have hm : max (Nat.size (st.regs x)) (Nat.size (st.regs y)) ≤
      Nat.size (st.regs x) + Nat.size (st.regs y) := by omega
  let N := B + (Nat.size (st.regs x) + Nat.size (st.regs y) +
    Nat.size (op.eval (st.regs x) (st.regs y)) + 1) + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hsq : N ≤ N ^ 2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left N hN
  change _ ≤ 32 * N ^ 2
  have hlin : 2 * Nat.size (st.regs x) + 2 * Nat.size (st.regs y) +
      2 * max (Nat.size (st.regs x)) (Nat.size (st.regs y)) + Nat.size (st.regs z) +
      3 * Nat.size (op.eval (st.regs x) (st.regs y)) + 26 ≤ 32 * N := by
    dsimp [N]
    omega
  exact hlin.trans (Nat.mul_le_mul_left 32 hsq)

end PCP.Lang.MachineLayout
