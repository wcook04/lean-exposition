import PCP.Complexity.BlockResetMachine

/-!
# Sequential and conditional control for actual machine blocks

Static calls share physical tapes and retain finite local controls. Sequencing
and tape-emptiness branches have exact trace bounds and canonical return states.
No unbounded register is represented in the finite controller.
-/

namespace PCP.Machine.FiniteBlocks

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
  {I : Type} [DecidableEq I] [Fintype I] (blocks : I → Block K Γ)
  {L τ : Type} [Fintype L] [Fintype τ]

/-- Repackage a fixed finite call graph as a block on the same tapes. -/
abbrev assembled (entry : L) (initial : τ) (returns : I → L)
    (caller : L → Stmt Γ (Labels blocks (L := L)) (Controls blocks × τ)) : Block K Γ where
  Label := Labels blocks (L := L)
  Control := Controls blocks × τ
  entry := .inr entry
  initial := ((fun i => (blocks i).initial), initial)
  code := fun
    | .inl ⟨i, l⟩ => lift blocks returns i ((blocks i).code l)
    | .inr l => caller l

variable (entry : L) (initial : τ) (returns : I → L)
  (caller : L → Stmt Γ (Labels blocks (L := L)) (Controls blocks × τ))
  (input output : K) [Fintype (Γ input)]

/-- The block view and the existing assembler have identical transition functions. -/
theorem assembled_step :
    ((assembled blocks entry initial returns caller).machine input output).step =
      (machine blocks input output entry initial returns caller).step := by
  change TM2.step _ = TM2.step _
  congr 1

/-- Canonical boundaries have every callee's initial finite control. -/
def boundary (l : Option (Labels blocks (L := L))) (S : ∀ k, List (Γ k)) :
    ((assembled blocks entry initial returns caller).machine input output).Cfg :=
  ⟨l, ((fun i => (blocks i).initial), initial), S⟩

/-- Transport a reset callee's actual trace with zero extra call steps. -/
theorem assembled_trace (i : I) (S T : ∀ k, List (Γ k)) (n : ℕ)
    (h : (flip Bind.bind ((blocks i).machine input output).step)^[n]
      (some ⟨some (blocks i).entry, (blocks i).initial, S⟩) =
      some ⟨none, (blocks i).initial, T⟩) :
    (flip Bind.bind ((assembled blocks entry initial returns caller).machine input output).step)^[n]
      (some (boundary blocks entry initial returns caller input output
        (some (.inl ⟨i, (blocks i).entry⟩)) S)) =
      some (boundary blocks entry initial returns caller input output
        (some (.inr (returns i))) T) := by
  have hh := iterate_embedCfg blocks input output entry initial returns caller i
    (fun j => (blocks j).initial) initial n h
  rw [assembled_step]
  dsimp only [FinTM2.Cfg, machine, Block.machine, assembled] at hh ⊢
  simpa only [embedCfg, Function.update_eq_self, boundary] using hh

end PCP.Machine.FiniteBlocks

namespace PCP.Machine.BlockControl

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition FiniteBlocks

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
  (left right : Block K Γ)

abbrev pair : Bool → Block K Γ
  | false => left
  | true => right

/-- Three caller labels: start, enter the second block, and halt. -/
def seqCaller : Fin 3 → Stmt Γ (Labels (pair left right) (L := Fin 3))
    (Controls (pair left right) × Unit)
  | 0 => enter (pair left right) false
  | 1 => enter (pair left right) true
  | _ => .halt

def seqReturns : Bool → Fin 3
  | false => 1
  | true => 2

abbrev sequence : Block K Γ :=
  assembled (pair left right) (0 : Fin 3) () seqReturns (seqCaller left right)

variable (input output : K) [Fintype (Γ input)]

abbrev seqCfg (l : Option (Labels (pair left right) (L := Fin 3)))
    (S : ∀ k, List (Γ k)) : ((sequence left right).machine input output).Cfg :=
  boundary (pair left right) (0 : Fin 3) () seqReturns (seqCaller left right) input output l S

theorem seq_start (S : ∀ k, List (Γ k)) :
    ((sequence left right).machine input output).step
      (seqCfg left right input output (some (.inr 0)) S) =
      some (seqCfg left right input output (some (.inl ⟨false, left.entry⟩)) S) := by
  dsimp only [Block.machine, FinTM2.step, TM2.step, sequence, assembled, seqCfg,
    boundary, seqCaller, TM2.stepAux, enter]
  simp only [TM2.stepAux, Function.update_eq_self]
  rfl

theorem seq_middle (S : ∀ k, List (Γ k)) :
    ((sequence left right).machine input output).step
      (seqCfg left right input output (some (.inr 1)) S) =
      some (seqCfg left right input output (some (.inl ⟨true, right.entry⟩)) S) := by
  dsimp only [Block.machine, FinTM2.step, TM2.step, sequence, assembled, seqCfg,
    boundary, seqCaller, TM2.stepAux, enter]
  simp only [TM2.stepAux, Function.update_eq_self]
  rfl

theorem seq_halt (S : ∀ k, List (Γ k)) :
    ((sequence left right).machine input output).step
      (seqCfg left right input output (some (.inr 2)) S) =
      some (seqCfg left right input output none S) := by
  rfl

/-- Sequencing costs three control steps in addition to the two actual callees. -/
theorem sequence_trace (S T U : ∀ k, List (Γ k)) (nl nr : ℕ)
    (hl : (flip Bind.bind (left.machine input output).step)^[nl]
      (some ⟨some left.entry, left.initial, S⟩) = some ⟨none, left.initial, T⟩)
    (hr : (flip Bind.bind (right.machine input output).step)^[nr]
      (some ⟨some right.entry, right.initial, T⟩) = some ⟨none, right.initial, U⟩) :
    (flip Bind.bind ((sequence left right).machine input output).step)^[nl + nr + 3]
      (some (seqCfg left right input output (some (.inr 0)) S)) =
      some (seqCfg left right input output none U) := by
  have hleft := assembled_trace (pair left right) (0 : Fin 3) () seqReturns
    (seqCaller left right) input output false S T nl hl
  have hright := assembled_trace (pair left right) (0 : Fin 3) () seqReturns
    (seqCaller left right) input output true T U nr hr
  have he : nl + nr + 3 = 1 + nr + 1 + nl + 1 := by omega
  rw [he, Function.iterate_succ_apply]
  change (flip Bind.bind ((sequence left right).machine input output).step)^[1 + nr + 1 + nl]
    (((sequence left right).machine input output).step
      (seqCfg left right input output (some (.inr 0)) S)) = _
  rw [seq_start, Function.iterate_add_apply, hleft, Function.iterate_succ_apply]
  change (flip Bind.bind ((sequence left right).machine input output).step)^[1 + nr]
    (((sequence left right).machine input output).step
      (seqCfg left right input output (some (.inr 1)) T)) = _
  rw [seq_middle, Function.iterate_add_apply, hright]
  exact seq_halt left right input output U

variable (test : K)

/-- A nonempty test tape selects right; an empty tape selects left. -/
def branchCaller : Bool → Stmt Γ (Labels (pair left right) (L := Bool))
    (Controls (pair left right) × Bool)
  | false => .peek test (fun v o => (v.1, o.isSome))
      (.branch (fun v => v.2)
        (.load (fun v => (v.1, false)) (enter (pair left right) true))
        (.load (fun v => (v.1, false)) (enter (pair left right) false)))
  | true => .halt

abbrev conditional : Block K Γ :=
  assembled (pair left right) false false (fun _ => true) (branchCaller left right test)

abbrev branchCfg (l : Option (Labels (pair left right) (L := Bool)))
    (S : ∀ k, List (Γ k)) : ((conditional left right test).machine input output).Cfg :=
  boundary (pair left right) false false (fun _ => true)
    (branchCaller left right test) input output l S

theorem branch_start (S : ∀ k, List (Γ k)) :
    ((conditional left right test).machine input output).step
      (branchCfg left right input output test (some (.inr false)) S) =
      some (branchCfg left right input output test
        (some (.inl ⟨!(S test).isEmpty, (pair left right (!(S test).isEmpty)).entry⟩)) S) := by
  cases hs : S test with
  | nil =>
      dsimp only [Block.machine, FinTM2.step, TM2.step, conditional, assembled,
        branchCfg, boundary, branchCaller, TM2.stepAux, enter]
      rw [hs]
      simp only [List.head?_nil, Option.isSome, List.isEmpty_nil,
        Function.update_eq_self]
      rfl
  | cons c cs =>
      dsimp only [Block.machine, FinTM2.step, TM2.step, conditional, assembled,
        branchCfg, boundary, branchCaller, TM2.stepAux, enter]
      rw [hs]
      simp only [List.head?_cons, Option.isSome, List.isEmpty_cons,
        Function.update_eq_self]
      rfl

/-- The test is a peek: every physical tape is unchanged before the selected call. -/
theorem conditional_trace (S T : ∀ k, List (Γ k)) (n : ℕ)
    (h : (flip Bind.bind ((pair left right (!(S test).isEmpty)).machine input output).step)^[n]
      (some ⟨some (pair left right (!(S test).isEmpty)).entry,
        (pair left right (!(S test).isEmpty)).initial, S⟩) =
      some ⟨none, (pair left right (!(S test).isEmpty)).initial, T⟩) :
    (flip Bind.bind ((conditional left right test).machine input output).step)^[n + 2]
      (some (branchCfg left right input output test (some (.inr false)) S)) =
      some (branchCfg left right input output test none T) := by
  have hb := assembled_trace (pair left right) false false (fun _ => true)
    (branchCaller left right test) input output (!(S test).isEmpty) S T n h
  rw [show n + 2 = 1 + n + 1 by omega, Function.iterate_succ_apply]
  change (flip Bind.bind ((conditional left right test).machine input output).step)^[1 + n]
    (((conditional left right test).machine input output).step
      (branchCfg left right input output test (some (.inr false)) S)) = _
  rw [branch_start, Function.iterate_add_apply, hb]
  rfl

end PCP.Machine.BlockControl
