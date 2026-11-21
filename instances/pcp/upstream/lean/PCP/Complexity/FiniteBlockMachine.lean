import PCP.Complexity.CallTrace

/-!
# Finite machine blocks sharing materialized tapes

A fixed finite family of blocks shares one tape layout. Each block has its own
finite local control; labels are tagged by the block index. Halting a block jumps
to its statically assigned caller continuation. Entry resets only that block's
finite control and costs one actual machine step. Successful traces transport at
their exact recorded length, without resetting tapes or running past the return
boundary. This supports a finite control-flow graph for structured programs.
-/

namespace PCP.Machine.FiniteBlocks

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-- A finite machine fragment on a common tape alphabet and index type. -/
structure Block (K : Type) (Γ : K → Type) where
  Label : Type
  [labelFintype : Fintype Label]
  Control : Type
  [controlFintype : Fintype Control]
  entry : Label
  initial : Control
  code : Label → Stmt Γ Label Control

attribute [instance] Block.labelFintype Block.controlFintype

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}

/-- Viewing a block as a standalone machine only adds the designated external ports. -/
abbrev Block.machine (b : Block K Γ) (input output : K) [Fintype (Γ input)] : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := Γ
  Γk₀Fin := inferInstance
  Λ := b.Label
  main := b.entry
  σ := b.Control
  initialState := b.initial
  m := b.code

section Assemble

variable {I : Type} [DecidableEq I] [Fintype I] (blocks : I → Block K Γ)
  {L τ : Type} [Fintype L] [Fintype τ]

/-- A finite product of all local controls. Unbounded values remain on shared tapes. -/
abbrev Controls := ∀ i, (blocks i).Control

/-- Labels distinguish callee instructions from caller control-flow nodes. -/
abbrev Labels := (Σ i, (blocks i).Label) ⊕ L

/-- Embed one local configuration and its statically assigned return point. -/
def embedCfg (ret : I → L) (i : I) (states : Controls blocks) (t : τ)
    (c : Cfg Γ (blocks i).Label (blocks i).Control) :
    Cfg Γ (Labels blocks (L := L)) (Controls blocks × τ) where
  l := match c.l with
    | some l => some (.inl ⟨i, l⟩)
    | none => some (.inr (ret i))
  var := (Function.update states i c.var, t)
  stk := c.stk

/-- Translate labels and focus callbacks on the selected block's finite control. -/
def lift (ret : I → L) (i : I) :
    Stmt Γ (blocks i).Label (blocks i).Control →
      Stmt Γ (Labels blocks (L := L)) (Controls blocks × τ)
  | .push k f q => .push k (fun v => f (v.1 i)) (lift ret i q)
  | .peek k f q => .peek k (fun v o => (Function.update v.1 i (f (v.1 i) o), v.2))
      (lift ret i q)
  | .pop k f q => .pop k (fun v o => (Function.update v.1 i (f (v.1 i) o), v.2))
      (lift ret i q)
  | .load f q => .load (fun v => (Function.update v.1 i (f (v.1 i)), v.2)) (lift ret i q)
  | .branch g q₁ q₂ => .branch (fun v => g (v.1 i)) (lift ret i q₁) (lift ret i q₂)
  | .goto g => .goto (fun v => .inl ⟨i, g (v.1 i)⟩)
  | .halt => .goto (fun _ => .inr (ret i))

omit [Fintype K] [Fintype I] [Fintype L] [Fintype τ] in
/-- Shared tape contents and every other block's finite control are preserved exactly. -/
theorem stepAux_lift (ret : I → L) (i : I) (states : Controls blocks) (t : τ) :
    ∀ (q : Stmt Γ (blocks i).Label (blocks i).Control) (v : (blocks i).Control)
      (S : ∀ k, List (Γ k)),
      stepAux (lift blocks ret i q) (Function.update states i v, t) S =
        embedCfg blocks ret i states t (stepAux q v S)
  | .push k f q, v, S => by
      simp only [lift, stepAux, Function.update_self]
      exact stepAux_lift ret i states t q v _
  | .peek k f q, v, S => by
      simp only [lift, stepAux, Function.update_self, Function.update_idem]
      exact stepAux_lift ret i states t q _ S
  | .pop k f q, v, S => by
      simp only [lift, stepAux, Function.update_self, Function.update_idem]
      exact stepAux_lift ret i states t q _ _
  | .load f q, v, S => by
      simp only [lift, stepAux, Function.update_self, Function.update_idem]
      exact stepAux_lift ret i states t q _ S
  | .branch g q₁ q₂, v, S => by
      simp only [lift, stepAux, Function.update_self]
      cases g v
      · simpa using stepAux_lift ret i states t q₂ v S
      · simpa using stepAux_lift ret i states t q₁ v S
  | .goto g, v, S => by simp [lift, stepAux, embedCfg]
  | .halt, v, S => rfl

variable (input output : K) [Fintype (Γ input)] (entry : L) (initial : τ)
  (ret : I → L)
  (caller : L → Stmt Γ (Labels blocks (L := L)) (Controls blocks × τ))

/-- The complete finite graph of blocks and caller continuations. -/
def machine : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := Γ
  Γk₀Fin := inferInstance
  Λ := Labels blocks (L := L)
  main := .inr entry
  σ := Controls blocks × τ
  initialState := ((fun i => (blocks i).initial), initial)
  m := fun
    | .inl ⟨i, l⟩ => lift blocks ret i ((blocks i).code l)
    | .inr l => caller l

/-- A call entry performs a finite-control reset and one jump; tapes are untouched. -/
def enter (i : I) : Stmt Γ (Labels blocks (L := L)) (Controls blocks × τ) :=
  .load (fun v => (Function.update v.1 i (blocks i).initial, v.2))
    (.goto (fun _ => .inl ⟨i, (blocks i).entry⟩))

/-- An active instruction in a selected block agrees with its standalone execution. -/
theorem step_embedCfg_of_active (i : I) (states : Controls blocks) (t : τ)
    {c : (Block.machine (blocks i) input output).Cfg} {l : (blocks i).Label}
    (h : c.l = some l) :
    (machine blocks input output entry initial ret caller).step
        (embedCfg blocks ret i states t c) =
      Option.map (embedCfg blocks ret i states t)
        ((Block.machine (blocks i) input output).step c) := by
  obtain ⟨l', v, S⟩ := c
  cases l' with
  | none => exact absurd h (by simp)
  | some l' =>
      change some (stepAux (lift blocks ret i ((blocks i).code l'))
        (Function.update states i v, t) S) = _
      exact congrArg some (stepAux_lift blocks ret i states t ((blocks i).code l') v S)

/-- Exact trace transport stops at the active return continuation. -/
theorem iterate_embedCfg (i : I) (states : Controls blocks) (t : τ) :
    ∀ (n : ℕ) {start finish : (Block.machine (blocks i) input output).Cfg},
      (flip Bind.bind (Block.machine (blocks i) input output).step)^[n] (some start) =
          some finish →
      (flip Bind.bind (machine blocks input output entry initial ret caller).step)^[n]
          (some (embedCfg blocks ret i states t start)) =
        some (embedCfg blocks ret i states t finish)
  | 0, start, finish, h => by
      rw [Function.iterate_zero_apply] at h ⊢
      exact congrArg (fun c => some (embedCfg blocks ret i states t c)) (Option.some_inj.1 h)
  | n + 1, start, finish, h => by
      rw [Function.iterate_succ_apply] at h ⊢
      cases hl : start.l with
      | none =>
          rw [show (flip Bind.bind (Block.machine (blocks i) input output).step) (some start) =
              none from step_eq_none_of_l_none hl, iterate_bind_none] at h
          exact absurd h (by simp)
      | some l =>
          have hstep : (flip Bind.bind (Block.machine (blocks i) input output).step) (some start) =
              (Block.machine (blocks i) input output).step start := rfl
          rw [hstep] at h
          cases hs : (Block.machine (blocks i) input output).step start with
          | none => rw [hs, iterate_bind_none] at h; exact absurd h (by simp)
          | some c' =>
              rw [hs] at h
              have hpar : (flip Bind.bind
                  (machine blocks input output entry initial ret caller).step)
                  (some (embedCfg blocks ret i states t start)) =
                    some (embedCfg blocks ret i states t c') := by
                change (machine blocks input output entry initial ret caller).step
                  (embedCfg blocks ret i states t start) = _
                rw [step_embedCfg_of_active blocks input output entry initial ret caller
                  i states t hl, hs]
                rfl
              rw [hpar]
              exact iterate_embedCfg i states t n h

/-- Entry costs exactly one step, including resetting the selected block's control. -/
theorem step_enter {l : L} (i : I) (h : caller l = enter blocks i)
    (states : Controls blocks) (t : τ) (S : ∀ k, List (Γ k)) :
    (machine blocks input output entry initial ret caller).step ⟨some (.inr l), (states, t), S⟩ =
      some (embedCfg blocks ret i states t
        ⟨some (blocks i).entry, (blocks i).initial, S⟩) := by
  change some (stepAux (caller l) (states, t) S) = _
  rw [h]
  rfl

/-- Package the unchanged callee runtime with the actual parent machine. -/
def embedEvals (i : I) (states : Controls blocks) (t : τ)
    {start finish : (Block.machine (blocks i) input output).Cfg} {budget : ℕ}
    (h : EvalsToInTime (Block.machine (blocks i) input output).step start (some finish) budget) :
    EvalsToInTime (machine blocks input output entry initial ret caller).step
      (embedCfg blocks ret i states t start) (some (embedCfg blocks ret i states t finish))
      budget where
  steps := h.steps
  evals_in_steps := iterate_embedCfg blocks input output entry initial ret caller
    i states t h.steps h.evals_in_steps
  steps_le_m := h.steps_le_m

end Assemble

end PCP.Machine.FiniteBlocks
