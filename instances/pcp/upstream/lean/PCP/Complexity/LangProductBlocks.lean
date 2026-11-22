import PCP.Complexity.LangAssignmentSkeleton
import PCP.Complexity.BinaryMultiplicationMachine

/-!
# Binary multiplication on the shared language workspace

The retained multiplicand and consumed multiplier are placed on compiler work
tapes. The product is materialized on the standard result tape. A final physical
clear removes the retained multiplicand, giving the same empty-scratch boundary
as the consuming basic arithmetic blocks.
-/

namespace PCP.Lang.MachineLayout

open Turing Turing.TM2 StateTransition PCP.Machine FiniteBlocks

variable {R Q : ℕ} {F : Type} [DecidableEq F] [Fintype F]

/-- Tapes outside the six multiplication work ports. -/
abbrev MultiplicationFrame (R Q : ℕ) (F : Type) := DataSlot R Q ⊕ (Bool ⊕ F)

/-- A fixed executable permutation from multiplication's layout to the compiler's layout. -/
def multiplicationPositions :
    BinaryMultiplication.Tapes (MultiplicationFrame R Q F) ≃ Tapes R Q F where
  toFun := fun
    | .inl .left => work 0
    | .inl .right => work 3
    | .inl .save => work 2
    | .inl .result => work 4
    | .inr (.inl false) => work 1
    | .inr (.inl true) => work 5
    | .inr (.inr (.inl d)) => .inl d
    | .inr (.inr (.inr (.inl false))) => work 6
    | .inr (.inr (.inr (.inl true))) => work 7
    | .inr (.inr (.inr (.inr j))) => framePort j
  invFun := fun
    | .inl d => .inr (.inr (.inl d))
    | .inr (.inl 0) => .inl .left
    | .inr (.inl 1) => .inr (.inl false)
    | .inr (.inl 2) => .inl .save
    | .inr (.inl 3) => .inl .right
    | .inr (.inl 4) => .inl .result
    | .inr (.inl 5) => .inr (.inl true)
    | .inr (.inl 6) => .inr (.inr (.inr (.inl false)))
    | .inr (.inl _) => .inr (.inr (.inr (.inl true)))
    | .inr (.inr j) => .inr (.inr (.inr (.inr j)))
  left_inv := by
    rintro ((_ | _ | _ | _) | ((_ | _) | (d | ((_ | _) | j)))) <;> rfl
  right_inv := by
    rintro (d | (i | j))
    · rfl
    · fin_cases i <;> rfl
    · rfl

/-- Caller data and the two unused scratch tapes form an untouched finite frame. -/
def multiplicationFrame (st : State R Q) (frame : F → List Sym) :
    MultiplicationFrame R Q F → List Sym
  | .inl d => stateTapes st d
  | .inr (.inl _) => []
  | .inr (.inr j) => frame j

/-- Observable tape contents during multiplication's framed trace. -/
def multiplicationTapes (st : State R Q) (frame : F → List Sym)
    (left right source bits : List Sym) : Tapes R Q F → List Sym
  | .inl d => stateTapes st d
  | .inr (.inl 0) => left
  | .inr (.inl 1) => source
  | .inr (.inl 3) => right
  | .inr (.inl 5) => bits
  | .inr (.inl _) => []
  | .inr (.inr j) => frame j

/-- The actual finite multiplication machine, with only a static tape permutation. -/
abbrev multiplicationRaw : Block (Tapes R Q F) (fun _ => Sym) :=
  relocatedBlock (BinaryMultiplication.machine (MultiplicationFrame R Q F))
    multiplicationPositions (fun _ => Equiv.refl Sym)

/-- All finite controls and physical contents survive the static permutation exactly. -/
theorem multiplication_cfg (st : State R Q) (frame : F → List Sym)
    (l : Option (BinaryMultiplication.Label (MultiplicationFrame R Q F)))
    (left right source bits : List Sym) :
    relocateCfg (BinaryMultiplication.machine (MultiplicationFrame R Q F))
      multiplicationPositions (fun _ => Equiv.refl Sym)
      (BinaryMultiplication.cfg (MultiplicationFrame R Q F) l left right source bits
        (multiplicationFrame st frame)) =
      ⟨l, (fun _ => (false, none, none), none, false),
        multiplicationTapes st frame left right source bits⟩ := by
  dsimp only [relocateCfg, BinaryMultiplication.cfg]
  congr 1
  funext k
  rcases k with d | (i | j)
  · change List.map id _ = _
    simp only [List.map_id]
    rfl
  · fin_cases i <;> change List.map id _ = _
    all_goals simp only [List.map_id]; rfl
  · change List.map id _ = _
    simp only [List.map_id]
    rfl

/-- Multiply copied operands, retaining the multiplicand until the cleanup block. -/
theorem multiplicationRaw_executes (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (n m : ℕ) :
    multiplicationRaw.Executes input output
      (multiplicationTapes st frame (natTape n) [] (natTape m) [])
      (multiplicationTapes st frame (natTape n) (natTape (n * m)) [] [])
      (10 * (Nat.size n + Nat.size m + 1) ^ 2) := by
  let h := BinaryMultiplication.evals n m (multiplicationFrame st frame)
  have ht := iterate_relocatedBlock
    (BinaryMultiplication.machine (MultiplicationFrame R Q F)) multiplicationPositions
    (fun _ => Equiv.refl Sym) input output h.steps h.evals_in_steps
  simp only [multiplication_cfg] at ht
  exact ⟨h.steps, h.steps_le_m, ht⟩

/-- Clearing the retained operand gives the common consuming arithmetic interface. -/
abbrev computeMul : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence multiplicationRaw (BlockCleanup.one (work 0))

/-- Concrete polynomial-time multiplication with all work tapes except the result empty. -/
theorem computeMul_executes (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (n m : ℕ) :
    computeMul.Executes input output
      (Function.update (Function.update (tapes st frame) (work 0) (natTape n))
        (work 1) (natTape m))
      (Function.update (tapes st frame) (work 3) (natTape (n * m)))
      (10 * (Nat.size n + Nat.size m + 1) ^ 2 + Nat.size n + 4) := by
  have hm := multiplicationRaw_executes input output st frame n m
  have hc := clear_executes input output (work 0)
    (multiplicationTapes st frame (natTape n) (natTape (n * m)) [] [])
  have hleft : multiplicationTapes st frame (natTape n) (natTape (n * m)) [] []
      (work 0) = natTape n := rfl
  rw [hleft, natTape_length] at hc
  have h := Block.Executes.seq input output hm hc
  have hstart : multiplicationTapes st frame (natTape n) [] (natTape m) [] =
      Function.update (Function.update (tapes st frame) (work 0) (natTape n))
        (work 1) (natTape m) := by
    funext k
    rcases k with d | (i | j)
    · simp [multiplicationTapes, tapes, work]
    · fin_cases i <;> simp [multiplicationTapes, tapes, work]
    · simp [multiplicationTapes, tapes, work]
  have hfinish : Function.update
      (multiplicationTapes st frame (natTape n) (natTape (n * m)) [] []) (work 0) [] =
      Function.update (tapes st frame) (work 3) (natTape (n * m)) := by
    funext k
    rcases k with d | (i | j)
    · simp [multiplicationTapes, tapes, work]
    · fin_cases i <;> simp [multiplicationTapes, tapes, work]
    · simp [multiplicationTapes, tapes, work]
  rw [hstart, hfinish] at h
  convert h using 1

/-- The complete alias-safe multiplication assignment uses the common call graph. -/
abbrev assignMul (z x y : Fin R) : Block (Tapes R Q F) (fun _ => Sym) :=
  assignWith computeMul z x y

/-- Actual multiplication assignment with the exact source-language semantics. -/
theorem assignMul_correct (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (z x y : Fin R) (B : ℕ) (hB : st.Sized B) :
    (assignMul z x y).Executes input output (tapes st frame)
      (tapes ((Stmt.assign z (.mul x y)).run st).1 frame)
      (47 * (B + ((Stmt.assign z (.mul x y)).run st).2 + 1) ^ 2) := by
  have hc := computeMul_executes input output st frame (st.regs x) (st.regs y)
  have hb : 10 * (Nat.size (st.regs x) + Nat.size (st.regs y) + 1) ^ 2 +
      Nat.size (st.regs x) + 4 ≤
      15 * (Nat.size (st.regs x) + Nat.size (st.regs y) + 1) ^ 2 := by
    let N := Nat.size (st.regs x) + Nat.size (st.regs y) + 1
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hsq : N ≤ N ^ 2 := by
      simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left N hN
    change 10 * N ^ 2 + Nat.size (st.regs x) + 4 ≤ 15 * N ^ 2
    have hx : Nat.size (st.regs x) ≤ N := by dsimp [N]; omega
    omega
  have h := assignWith_executes computeMul input output st frame z x y
    (st.regs x * st.regs y) _ (Block.Executes.mono input output hc hb)
  apply Block.Executes.mono input output h
  exact assignment_budget_le _ _ _ _ B 15 (hB.1 z)

end PCP.Lang.MachineLayout
