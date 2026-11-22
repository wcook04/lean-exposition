import PCP.Complexity.FiniteBlockMachine
import PCP.Complexity.Machine

/-!
# Relocating a machine fragment into a shared tape layout

A fixed equivalence renames tape indices, and fixed alphabet equivalences identify
their symbols with the compiler alphabet. Both are static finite layout data;
no input-dependent search is used. The complete configuration and exact step count
are preserved, so framed arithmetic machines can become shared-layout blocks.
-/

namespace PCP.Machine.FiniteBlocks

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

attribute [local instance] FinTM2.ΛFin FinTM2.σFin

variable (tm : FinTM2) {K : Type} [DecidableEq K] [Fintype K]
  (positions : tm.K ≃ K) (symbols : ∀ k, tm.Γ k ≃ Sym)

/-- The same physical contents at renamed positions and alphabet codes. -/
def relocatedStacks (S : ∀ k, List (tm.Γ k)) : K → List Sym :=
  fun k => (S (positions.symm k)).map (symbols (positions.symm k))

omit [DecidableEq K] [Fintype K] in
@[simp] lemma relocatedStacks_position (S : ∀ k, List (tm.Γ k)) (k : tm.K) :
    relocatedStacks tm positions symbols S (positions k) = (S k).map (symbols k) := by
  exact congrArg (fun j => (S j).map (symbols j)) (positions.symm_apply_apply k)

omit [Fintype K] in
lemma relocatedStacks_update (S : ∀ k, List (tm.Γ k)) (k : tm.K) (xs : List (tm.Γ k)) :
    relocatedStacks tm positions symbols (Function.update S k xs) =
      Function.update (relocatedStacks tm positions symbols S) (positions k)
        (xs.map (symbols k)) := by
  funext j
  obtain ⟨k', rfl⟩ := positions.surjective j
  by_cases h : k' = k
  · subst h
    simp
  · simp [h, positions.injective.ne h]

/-- Statement translation changes only finite static indices and alphabet codes. -/
def relocateStmt : Stmt tm.Γ tm.Λ tm.σ → Stmt (fun _ : K => Sym) tm.Λ tm.σ
  | .push k f q => .push (positions k) (fun v => symbols k (f v)) (relocateStmt q)
  | .peek k f q => .peek (positions k) (fun v o => f v (o.map (symbols k).symm))
      (relocateStmt q)
  | .pop k f q => .pop (positions k) (fun v o => f v (o.map (symbols k).symm))
      (relocateStmt q)
  | .load f q => .load f (relocateStmt q)
  | .branch g q₁ q₂ => .branch g (relocateStmt q₁) (relocateStmt q₂)
  | .goto g => .goto g
  | .halt => .halt

/-- Configuration transport preserves labels and local finite control. -/
def relocateCfg (c : tm.Cfg) : Cfg (fun _ : K => Sym) tm.Λ tm.σ where
  l := c.l
  var := c.var
  stk := relocatedStacks tm positions symbols c.stk

omit [Fintype K] in
/-- Complete statement-level correctness, including dependent alphabet updates. -/
theorem stepAux_relocateStmt : ∀ (q : Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ)
    (S : ∀ k, List (tm.Γ k)),
    stepAux (relocateStmt tm positions symbols q) v (relocatedStacks tm positions symbols S) =
      relocateCfg tm positions symbols (stepAux q v S)
  | .push k f q, v, S => by
      simp only [relocateStmt, stepAux, relocatedStacks_position]
      rw [show symbols k (f v) :: List.map (symbols k) (S k) =
        List.map (symbols k) (f v :: S k) from rfl, ← relocatedStacks_update]
      exact stepAux_relocateStmt q v _
  | .peek k f q, v, S => by
      simp only [relocateStmt, stepAux, relocatedStacks_position, List.head?_map, Option.map_map]
      have he : (symbols k).symm ∘ symbols k = id := (symbols k).symm_comp_self
      rw [he, Option.map_id]
      exact stepAux_relocateStmt q _ S
  | .pop k f q, v, S => by
      simp only [relocateStmt, stepAux, relocatedStacks_position, List.head?_map, Option.map_map,
        ← List.map_tail]
      have he : (symbols k).symm ∘ symbols k = id := (symbols k).symm_comp_self
      rw [he, Option.map_id, ← relocatedStacks_update]
      exact stepAux_relocateStmt q _ _
  | .load f q, v, S => by
      simp only [relocateStmt, stepAux]
      exact stepAux_relocateStmt q _ S
  | .branch g q₁ q₂, v, S => by
      simp only [relocateStmt, stepAux]
      cases g v
      · simpa using stepAux_relocateStmt q₂ v S
      · simpa using stepAux_relocateStmt q₁ v S
  | .goto g, v, S => rfl
  | .halt, v, S => rfl

/-- The translated code is a genuine finite block on the chosen common tape layout. -/
def relocatedBlock : Block K (fun _ => Sym) where
  Label := tm.Λ
  Control := tm.σ
  entry := tm.main
  initial := tm.initialState
  code l := relocateStmt tm positions symbols (tm.m l)

/-- One-step execution commutes with layout relocation, including terminal configurations. -/
theorem step_relocatedBlock (input output : K) (c : tm.Cfg) :
    ((relocatedBlock tm positions symbols).machine input output).step
        (relocateCfg tm positions symbols c) =
      (tm.step c).map (relocateCfg tm positions symbols) := by
  cases c with
  | mk l v S =>
      cases l with
      | none => rfl
      | some l => exact congrArg some (stepAux_relocateStmt tm positions symbols (tm.m l) v S)

/-- Exact successful traces survive tape relocation without extra runtime. -/
theorem iterate_relocatedBlock (input output : K) : ∀ (n : ℕ) {start finish : tm.Cfg},
    (flip Bind.bind tm.step)^[n] (some start) = some finish →
      (flip Bind.bind ((relocatedBlock tm positions symbols).machine input output).step)^[n]
        (some (relocateCfg tm positions symbols start)) =
          some (relocateCfg tm positions symbols finish)
  | 0, start, finish, h => by
      rw [Function.iterate_zero_apply] at h ⊢
      exact congrArg (fun c => some (relocateCfg tm positions symbols c)) (Option.some_inj.1 h)
  | n + 1, start, finish, h => by
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Bind.bind tm.step)^[n] (tm.step start) = some finish at h
      change (flip Bind.bind ((relocatedBlock tm positions symbols).machine input output).step)^[n]
        (((relocatedBlock tm positions symbols).machine input output).step
          (relocateCfg tm positions symbols start)) = _
      rw [step_relocatedBlock]
      cases hs : tm.step start with
      | none => rw [hs, iterate_bind_none] at h; exact absurd h (by simp)
      | some c =>
          rw [hs] at h
          simp only [Option.map_some]
          exact iterate_relocatedBlock input output n h

/-- Runtime certificates transport to the common-layout block at unchanged cost. -/
def relocateEvals (input output : K) {start finish : tm.Cfg} {budget : ℕ}
    (h : EvalsToInTime tm.step start (some finish) budget) :
    EvalsToInTime ((relocatedBlock tm positions symbols).machine input output).step
      (relocateCfg tm positions symbols start) (some (relocateCfg tm positions symbols finish))
      budget where
  steps := h.steps
  evals_in_steps :=
    iterate_relocatedBlock tm positions symbols input output h.steps h.evals_in_steps
  steps_le_m := h.steps_le_m

end PCP.Machine.FiniteBlocks
