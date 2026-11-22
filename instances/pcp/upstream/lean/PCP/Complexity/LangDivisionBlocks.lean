import PCP.Complexity.LangAssignmentSkeleton
import PCP.Complexity.BinaryDivisionMachine

/-!
# Actual division and remainder assignments on shared register tapes

One static Boolean selects whether quotient or remainder is placed on the
standard result tape. The same materialized long-division machine computes both;
physical cleanup drains the divisor and unused answer. Source/destination
register aliases are handled by the shared operand-loading assignment graph.
-/

namespace PCP.Lang.MachineLayout

open Turing Turing.TM2 StateTransition PCP.Machine FiniteBlocks

variable {R Q : ℕ} {F : Type} [DecidableEq F] [Fintype F]

/-- Seven division work tapes leave one scratch tape and all caller data untouched. -/
abbrev DivisionFrame (R Q : ℕ) (F : Type) := DataSlot R Q ⊕ (Unit ⊕ F)

/-- Static answer selection changes tape placement, never runtime arithmetic. -/
def divisionPositions (quotient : Bool) :
    BinaryDivision.Tapes (DivisionFrame R Q F) ≃ Tapes R Q F where
  toFun := fun
    | .inl .left => work 1
    | .inl .right => if quotient then work 6 else work 3
    | .inl .save => work 2
    | .inl .result => work 4
    | .inr (.inl .source) => work 0
    | .inr (.inl .bits) => work 5
    | .inr (.inl .quotient) => if quotient then work 3 else work 6
    | .inr (.inr (.inl d)) => .inl d
    | .inr (.inr (.inr (.inl _))) => work 7
    | .inr (.inr (.inr (.inr j))) => framePort j
  invFun := fun
    | .inl d => .inr (.inr (.inl d))
    | .inr (.inl 0) => .inr (.inl .source)
    | .inr (.inl 1) => .inl .left
    | .inr (.inl 2) => .inl .save
    | .inr (.inl 3) => if quotient then .inr (.inl .quotient) else .inl .right
    | .inr (.inl 4) => .inl .result
    | .inr (.inl 5) => .inr (.inl .bits)
    | .inr (.inl 6) => if quotient then .inl .right else .inr (.inl .quotient)
    | .inr (.inl _) => .inr (.inr (.inr (.inl ())))
    | .inr (.inr j) => .inr (.inr (.inr (.inr j)))
  left_inv := by
    intro k
    rcases k with s | (i | (d | (u | j)))
    · cases s <;> cases quotient <;> rfl
    · cases i <;> cases quotient <;> rfl
    · rfl
    · cases u; rfl
    · rfl
  right_inv := by
    rintro (d | (i | j))
    · rfl
    · fin_cases i <;> cases quotient <;> rfl
    · rfl

/-- The preserved external frame includes the one unused scratch tape. -/
def divisionFrame (st : State R Q) (frame : F → List Sym) : DivisionFrame R Q F → List Sym
  | .inl d => stateTapes st d
  | .inr (.inl _) => []
  | .inr (.inr j) => frame j

/-- Explicit materialized division workspace at the caller boundaries. -/
def divisionTapes (quotient : Bool) (st : State R Q) (frame : F → List Sym)
    (divisor remainder source bits answer : List Sym) : Tapes R Q F → List Sym
  | .inl d => stateTapes st d
  | .inr (.inl 0) => source
  | .inr (.inl 1) => divisor
  | .inr (.inl 3) => if quotient then answer else remainder
  | .inr (.inl 5) => bits
  | .inr (.inl 6) => if quotient then remainder else answer
  | .inr (.inl _) => []
  | .inr (.inr j) => frame j

/-- Actual long division placed on fixed compiler tapes. -/
abbrev divisionRaw (quotient : Bool) : Block (Tapes R Q F) (fun _ => Sym) :=
  relocatedBlock (BinaryDivision.machine (DivisionFrame R Q F))
    (divisionPositions quotient) (fun _ => Equiv.refl Sym)

/-- The static permutation preserves the complete materialized configuration. -/
theorem division_cfg (quotient : Bool) (st : State R Q) (frame : F → List Sym)
    (l : Option (BinaryDivision.Label (DivisionFrame R Q F)))
    (divisor remainder source bits answer : List Sym) :
    relocateCfg (BinaryDivision.machine (DivisionFrame R Q F))
      (divisionPositions quotient) (fun _ => Equiv.refl Sym)
      (BinaryDivision.cfg (DivisionFrame R Q F) l divisor remainder source bits answer
        (divisionFrame st frame)) =
      ⟨l, BinaryDivision.initial (DivisionFrame R Q F),
        divisionTapes quotient st frame divisor remainder source bits answer⟩ := by
  dsimp only [relocateCfg, BinaryDivision.cfg]
  congr 1
  funext k
  rcases k with d | (i | j)
  · change List.map id _ = _
    simp only [List.map_id]
    rfl
  · fin_cases i <;> cases quotient <;> change List.map id _ = _
    all_goals simp only [List.map_id]; rfl
  · change List.map id _ = _
    simp only [List.map_id]
    rfl

/-- Both answers are canonical, including the convention when the divisor is zero. -/
theorem divisionRaw_executes (quotient : Bool) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (n m : ℕ) :
    (divisionRaw quotient).Executes input output
      (divisionTapes quotient st frame (natTape m) [] (natTape n) [] [])
      (divisionTapes quotient st frame (natTape m) (natTape (n % m)) [] [] (natTape (n / m)))
      (40 * (Nat.size m + Nat.size n + 1) ^ 2) := by
  let h := BinaryDivision.evals n m (divisionFrame st frame)
  have ht := iterate_relocatedBlock
    (BinaryDivision.machine (DivisionFrame R Q F)) (divisionPositions quotient)
    (fun _ => Equiv.refl Sym) input output h.steps h.evals_in_steps
  simp only [division_cfg] at ht
  have hi : BinaryDivision.initial (DivisionFrame R Q F) =
      (divisionRaw (R := R) (Q := Q) (F := F) quotient).initial := by
    change (BinaryDivision.states (DivisionFrame R Q F) .eq, none, false) =
      ((fun i => (BinaryDivision.blocks (DivisionFrame R Q F) i).initial), none, false)
    congr 1
    funext i
    cases i <;> rfl
  rw [hi] at ht
  exact ⟨h.steps, h.steps_le_m, ht⟩

/-- Drain the retained divisor and the unselected answer after division. -/
abbrev computeDiv (quotient : Bool) : Block (Tapes R Q F) (fun _ => Sym) :=
  BlockControl.sequence (divisionRaw quotient)
    (BlockControl.sequence (BlockCleanup.one (work 1)) (BlockCleanup.one (work 6)))

/-- The selected answer is the only occupied compiler work tape at return. -/
theorem computeDiv_executes (quotient : Bool) (input output : Tapes R Q F)
    (st : State R Q) (frame : F → List Sym) (n m : ℕ) :
    (computeDiv quotient).Executes input output
      (Function.update (Function.update (tapes st frame) (work 0) (natTape n))
        (work 1) (natTape m))
      (Function.update (tapes st frame) (work 3) (natTape (if quotient then n / m else n % m)))
      (40 * (Nat.size m + Nat.size n + 1) ^ 2 + Nat.size m +
        Nat.size (if quotient then n % m else n / m) + 8) := by
  let T := divisionTapes quotient st frame (natTape m) (natTape (n % m)) [] [] (natTape (n / m))
  have hm := divisionRaw_executes quotient input output st frame n m
  have h1 := clear_executes input output (work 1) T
  have h6 := clear_executes input output (work 6) (Function.update T (work 1) [])
  have hleft : T (work 1) = natTape m := rfl
  have hextra : (Function.update T (work 1) []) (work 6) =
      natTape (if quotient then n % m else n / m) := by
    cases quotient <;> simp [T, divisionTapes, work]
  rw [hleft, natTape_length] at h1
  rw [hextra, natTape_length] at h6
  have h := Block.Executes.seq input output hm (Block.Executes.seq input output h1 h6)
  have hstart : divisionTapes quotient st frame (natTape m) [] (natTape n) [] [] =
      Function.update (Function.update (tapes st frame) (work 0) (natTape n))
        (work 1) (natTape m) := by
    funext k
    rcases k with d | (i | j)
    · simp [divisionTapes, tapes, work]
    · fin_cases i <;> cases quotient <;> simp [divisionTapes, tapes, work]
    · simp [divisionTapes, tapes, work]
  have hfinish : Function.update (Function.update T (work 1) []) (work 6) [] =
      Function.update (tapes st frame) (work 3)
        (natTape (if quotient then n / m else n % m)) := by
    funext k
    rcases k with d | (i | j)
    · simp [T, divisionTapes, tapes, work]
    · fin_cases i <;> cases quotient <;> simp [T, divisionTapes, tapes, work]
    · simp [T, divisionTapes, tapes, work]
  rw [hstart, hfinish] at h
  convert h using 1
  omega

/-- Division and modulo use the same alias-safe register-assignment call graph. -/
abbrev assignDiv (quotient : Bool) (z x y : Fin R) : Block (Tapes R Q F) (fun _ => Sym) :=
  assignWith (computeDiv quotient) z x y

/-- The selected source expression is fixed by the finite program. -/
def divisionExpr (quotient : Bool) (x y : Fin R) : Expr R :=
  if quotient then .div x y else .mod x y

/-- Exact source-language division or remainder assignment with uniform quadratic overhead. -/
theorem assignDiv_correct (quotient : Bool) (input output : Tapes R Q F) (st : State R Q)
    (frame : F → List Sym) (z x y : Fin R) (B : ℕ) (hB : st.Sized B) :
    (assignDiv quotient z x y).Executes input output (tapes st frame)
      (tapes ((Stmt.assign z (divisionExpr quotient x y)).run st).1 frame)
      (82 * (B + ((Stmt.assign z (divisionExpr quotient x y)).run st).2 + 1) ^ 2) := by
  have hc := computeDiv_executes quotient input output st frame (st.regs x) (st.regs y)
  have he : Nat.size (if quotient then st.regs x % st.regs y else st.regs x / st.regs y) ≤
      Nat.size (st.regs x) := by
    apply Nat.size_le_size
    cases quotient
    · exact Nat.div_le_self _ _
    · exact Nat.mod_le _ _
  have hb : 40 * (Nat.size (st.regs y) + Nat.size (st.regs x) + 1) ^ 2 +
      Nat.size (st.regs y) +
      Nat.size (if quotient then st.regs x % st.regs y else st.regs x / st.regs y) + 8 ≤
      50 * (Nat.size (st.regs x) + Nat.size (st.regs y) + 1) ^ 2 := by
    rw [Nat.add_comm (Nat.size (st.regs y)) (Nat.size (st.regs x))]
    let N := Nat.size (st.regs x) + Nat.size (st.regs y) + 1
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hsq : N ≤ N ^ 2 := by
      simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left N hN
    change 40 * N ^ 2 + Nat.size (st.regs y) + _ + 8 ≤ 50 * N ^ 2
    have hxy : Nat.size (st.regs x) + Nat.size (st.regs y) ≤ N := by dsimp [N]; omega
    omega
  have h := assignWith_executes (computeDiv quotient) input output st frame z x y
    (if quotient then st.regs x / st.regs y else st.regs x % st.regs y) _
    (Block.Executes.mono input output hc hb)
  have hbound := assignment_budget_le (Nat.size (st.regs x)) (Nat.size (st.regs y))
    (Nat.size (st.regs z))
    (Nat.size (if quotient then st.regs x / st.regs y else st.regs x % st.regs y)) B 50 (hB.1 z)
  have h' := Block.Executes.mono input output h hbound
  cases quotient <;> exact h'

end PCP.Lang.MachineLayout
