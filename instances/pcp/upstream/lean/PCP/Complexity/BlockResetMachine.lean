import PCP.Complexity.FiniteBlockMachine

/-!
# Clearing finite block control at return

The reset is part of the halting statement tree, so it costs no extra TM2 step.
All tapes and active states are preserved. This makes block boundaries uniform
without placing any unbounded value in finite control.
-/

namespace PCP.Machine.FiniteBlocks

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} (b : Block K Γ)

/-- Replace a terminal instruction by a finite-control reset and halt. -/
def resetStmt : Stmt Γ b.Label b.Control → Stmt Γ b.Label b.Control
  | .push k f q => .push k f (resetStmt q)
  | .peek k f q => .peek k f (resetStmt q)
  | .pop k f q => .pop k f (resetStmt q)
  | .load f q => .load f (resetStmt q)
  | .branch g q₁ q₂ => .branch g (resetStmt q₁) (resetStmt q₂)
  | .goto g => .goto g
  | .halt => .load (fun _ => b.initial) .halt

/-- The same finite block, with normalized local control at every return. -/
abbrev Block.reset : Block K Γ where
  Label := b.Label
  Control := b.Control
  entry := b.entry
  initial := b.initial
  code l := resetStmt b (b.code l)

/-- Only terminal local control is changed. -/
def resetCfg (c : Cfg Γ b.Label b.Control) : Cfg Γ b.Label b.Control :=
  ⟨c.l, if c.l.isSome then c.var else b.initial, c.stk⟩

omit [Fintype K] in
/-- The reset modifies no physical tape. -/
theorem stepAux_resetStmt : ∀ (q : Stmt Γ b.Label b.Control) (v : b.Control)
    (S : ∀ k, List (Γ k)),
    stepAux (resetStmt b q) v S = resetCfg b (stepAux q v S)
  | .push k f q, v, S => by
      simpa only [resetStmt, stepAux] using stepAux_resetStmt q v _
  | .peek k f q, v, S => by
      simpa only [resetStmt, stepAux] using stepAux_resetStmt q _ S
  | .pop k f q, v, S => by
      simpa only [resetStmt, stepAux] using stepAux_resetStmt q _ _
  | .load f q, v, S => by
      simpa only [resetStmt, stepAux] using stepAux_resetStmt q _ S
  | .branch g q₁ q₂, v, S => by
      simp only [resetStmt, stepAux]
      cases g v
      · exact stepAux_resetStmt q₂ v S
      · exact stepAux_resetStmt q₁ v S
  | .goto g, v, S => rfl
  | .halt, v, S => rfl

variable (input output : K) [Fintype (Γ input)]

/-- One transition commutes with the terminal reset. -/
theorem step_reset (c : (b.machine input output).Cfg) :
    ((b.reset).machine input output).step (resetCfg b c) =
      ((b.machine input output).step c).map (resetCfg b) := by
  cases c with
  | mk l v S =>
      cases l with
      | none => rfl
      | some l => exact congrArg some (stepAux_resetStmt b (b.code l) v S)

/-- Every successful finite trace survives at exactly the same number of steps. -/
theorem iterate_reset : ∀ (n : ℕ) {start finish : (b.machine input output).Cfg},
    (flip Bind.bind (b.machine input output).step)^[n] (some start) = some finish →
      (flip Bind.bind ((b.reset).machine input output).step)^[n]
        (some (resetCfg b start)) = some (resetCfg b finish)
  | 0, start, finish, h => by
      rw [Function.iterate_zero_apply] at h ⊢
      exact congrArg (fun c => some (resetCfg b c)) (Option.some_inj.1 h)
  | n + 1, start, finish, h => by
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Bind.bind (b.machine input output).step)^[n]
        ((b.machine input output).step start) = _ at h
      change (flip Bind.bind ((b.reset).machine input output).step)^[n]
        (((b.reset).machine input output).step (resetCfg b start)) = _
      rw [step_reset]
      cases hs : (b.machine input output).step start with
      | none => rw [hs, iterate_bind_none] at h; exact absurd h (by simp)
      | some c =>
          rw [hs] at h
          exact iterate_reset n h

/-- A callee's final control may be arbitrary; resetting makes the return canonical. -/
theorem reset_trace (S T : ∀ k, List (Γ k)) (v : b.Control) (n : ℕ)
    (h : (flip Bind.bind (b.machine input output).step)^[n]
      (some ⟨some b.entry, b.initial, S⟩) = some ⟨none, v, T⟩) :
    (flip Bind.bind ((b.reset).machine input output).step)^[n]
      (some ⟨some b.entry, b.initial, S⟩) = some ⟨none, b.initial, T⟩ := by
  exact iterate_reset b input output n h

end PCP.Machine.FiniteBlocks
