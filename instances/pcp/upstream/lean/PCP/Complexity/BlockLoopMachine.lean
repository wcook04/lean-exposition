import PCP.Complexity.FiniteBlockMachine

/-!
# A concrete countdown loop around shared-tape machine blocks

The controller tests whether a counter tape is empty. A nonempty counter enters
an actual decrement block, calls the body, then returns to the test. Its only
extra control bit records the emptiness test and is reset before every call.
The body and decrement are explicit finite blocks; their runtime certificates
are transported into this fixed finite control graph at exact step counts.
-/

namespace PCP.Machine.BlockLoop

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition FiniteBlocks


variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
  (body decrement : Block K Γ) (counter : K)

/-- Separate finite controls for the body and the countdown operation. -/
abbrev blocks : Bool → Block K Γ
  | false => body
  | true => decrement

/-- Body returns to the test; decrement returns to body entry. -/
def returns : Bool → Bool := id

/-- The test and body-entry nodes of the concrete loop controller. -/
def caller : Bool → Stmt Γ (Labels (blocks body decrement) (L := Bool))
    (Controls (blocks body decrement) × Bool)
  | false => .peek counter (fun v o => (v.1, o.isSome))
      (.branch (fun v => v.2)
        (.load (fun v => (v.1, false)) (enter (blocks body decrement) true))
        (.load (fun v => (v.1, false)) .halt))
  | true => enter (blocks body decrement) false

/-- The loop itself is a finite block on the same materialized tapes. -/
abbrev loop : Block K Γ where
  Label := Labels (blocks body decrement) (L := Bool)
  Control := Controls (blocks body decrement) × Bool
  entry := .inr false
  initial := ((fun i => (blocks body decrement i).initial), false)
  code := fun
    | .inl ⟨i, l⟩ => lift (blocks body decrement) returns i
        ((blocks body decrement i).code l)
    | .inr l => caller body decrement counter l

variable (input output : K) [Fintype (Γ input)]

/-- Boundary configurations reset all local finite controls. -/
def cfg (l : Option (Labels (blocks body decrement) (L := Bool))) (S : ∀ k, List (Γ k)) :
    ((loop body decrement counter).machine input output).Cfg :=
  ⟨l, ((fun i => (blocks body decrement i).initial), false), S⟩

/-- The block's machine is definitionally the finite-family assembler. -/
theorem machine_eq :
    (loop body decrement counter).machine input output =
      FiniteBlocks.machine (blocks body decrement) input output false false returns
        (caller body decrement counter) := by
  unfold Block.machine loop FiniteBlocks.machine
  congr
  funext l
  rcases l with ⟨i, l⟩ | l <;> rfl

/-- The transition functions share the same explicit configuration type. -/
theorem step_eq :
    ((loop body decrement counter).machine input output).step =
      (FiniteBlocks.machine (blocks body decrement) input output false false returns
        (caller body decrement counter)).step := by
  change TM2.step _ = TM2.step _
  congr 1
  funext l
  rcases l with ⟨i, l⟩ | l <;> rfl

/-- Nonempty counters enter the decrement block in one actual machine step. -/
theorem step_test_nonempty (S : ∀ k, List (Γ k)) (h : S counter ≠ []) :
    ((loop body decrement counter).machine input output).step
        (cfg body decrement counter input output (some (.inr false)) S) =
      some (cfg body decrement counter input output (some (.inl ⟨true, decrement.entry⟩)) S) := by
  cases hs : S counter with
  | nil => exact False.elim (h hs)
  | cons c cs =>
      dsimp only [Block.machine, FinTM2.step, TM2.step, loop, cfg, caller,
        TM2.stepAux, enter]
      rw [hs]
      simp only [List.head?_cons, Option.isSome, Function.update_eq_self]
      rfl

/-- A zero counter exits in one charged step with controls reset. -/
theorem step_test_empty (S : ∀ k, List (Γ k)) (h : S counter = []) :
    ((loop body decrement counter).machine input output).step
        (cfg body decrement counter input output (some (.inr false)) S) =
      some (cfg body decrement counter input output none S) := by
  dsimp only [Block.machine, FinTM2.step, TM2.step, loop, cfg, caller, TM2.stepAux]
  rw [h]
  rfl

/-- The post-decrement continuation enters the body in one actual step. -/
theorem step_body_entry (S : ∀ k, List (Γ k)) :
    ((loop body decrement counter).machine input output).step
        (cfg body decrement counter input output (some (.inr true)) S) =
      some (cfg body decrement counter input output (some (.inl ⟨false, body.entry⟩)) S) := by
  dsimp only [Block.machine, FinTM2.step, TM2.step, loop, cfg, caller, TM2.stepAux, enter]
  simp only [Function.update_eq_self]
  rfl

/-- A local block that resets its finite state returns to the selected controller node. -/
theorem run_block (i : Bool) (S T : ∀ k, List (Γ k)) (n : ℕ)
    (h : (flip Bind.bind ((blocks body decrement i).machine input output).step)^[n]
      (some ⟨some (blocks body decrement i).entry, (blocks body decrement i).initial, S⟩) =
      some ⟨none, (blocks body decrement i).initial, T⟩) :
    (flip Bind.bind ((loop body decrement counter).machine input output).step)^[n]
      (some (cfg body decrement counter input output
        (some (.inl ⟨i, (blocks body decrement i).entry⟩)) S)) =
      some (cfg body decrement counter input output (some (.inr i)) T) := by
  have hh := FiniteBlocks.iterate_embedCfg (blocks body decrement) input output false false
    returns (caller body decrement counter) i (fun j => (blocks body decrement j).initial) false n h
  rw [step_eq]
  dsimp only [FinTM2.Cfg, FiniteBlocks.machine, Block.machine, loop] at hh ⊢
  simpa only [FiniteBlocks.embedCfg, Function.update_eq_self, returns, id_eq, cfg] using hh

/-- One complete loop iteration counts the test, decrement, body entry, and body execution. -/
theorem iteration (S T U : ∀ k, List (Γ k)) (nd nb : ℕ) (hnonempty : S counter ≠ [])
    (hd : (flip Bind.bind (decrement.machine input output).step)^[nd]
      (some ⟨some decrement.entry, decrement.initial, S⟩) =
      some ⟨none, decrement.initial, T⟩)
    (hb : (flip Bind.bind (body.machine input output).step)^[nb]
      (some ⟨some body.entry, body.initial, T⟩) = some ⟨none, body.initial, U⟩) :
    (flip Bind.bind ((loop body decrement counter).machine input output).step)^[nb + 1 + nd + 1]
      (some (cfg body decrement counter input output (some (.inr false)) S)) =
      some (cfg body decrement counter input output (some (.inr false)) U) := by
  rw [Function.iterate_succ_apply]
  change (flip Bind.bind ((loop body decrement counter).machine input output).step)^[nb + 1 + nd]
    (((loop body decrement counter).machine input output).step
      (cfg body decrement counter input output (some (.inr false)) S)) = _
  rw [step_test_nonempty body decrement counter input output S hnonempty]
  exact (Function.iterate_add_apply _ (nb + 1) nd _).trans (by
    rw [run_block body decrement counter input output true S T nd hd]
    rw [Function.iterate_succ_apply]
    change (flip Bind.bind ((loop body decrement counter).machine input output).step)^[nb]
      (((loop body decrement counter).machine input output).step
        (cfg body decrement counter input output (some (.inr true)) T)) = _
    rw [step_body_entry, run_block body decrement counter input output false T U nb hb])
/-- Exact runtime: one final test, plus the two calls and their work per iteration. -/
def runtime (decrementTime bodyTime : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => runtime decrementTime bodyTime n + (bodyTime n + 1 + decrementTime n + 1)

/-- Concatenating actual block traces gives the whole countdown execution. -/
theorem trace (S D : ℕ → ∀ k, List (Γ k)) (decrementTime bodyTime : ℕ → ℕ) (n : ℕ)
    (hempty : S 0 counter = [])
    (hnonempty : ∀ i < n, S (i + 1) counter ≠ [])
    (hd : ∀ i < n, (flip Bind.bind (decrement.machine input output).step)^[decrementTime i]
      (some ⟨some decrement.entry, decrement.initial, S (i + 1)⟩) =
      some ⟨none, decrement.initial, D i⟩)
    (hb : ∀ i < n, (flip Bind.bind (body.machine input output).step)^[bodyTime i]
      (some ⟨some body.entry, body.initial, D i⟩) = some ⟨none, body.initial, S i⟩) :
    (flip Bind.bind ((loop body decrement counter).machine input output).step)^[
        runtime decrementTime bodyTime n]
      (some (cfg body decrement counter input output (some (.inr false)) (S n))) =
      some (cfg body decrement counter input output none (S 0)) := by
  induction n with
  | zero =>
      change ((loop body decrement counter).machine input output).step
        (cfg body decrement counter input output (some (.inr false)) (S 0)) = _
      exact step_test_empty body decrement counter input output (S 0) hempty
  | succ n ih =>
      rw [runtime, Function.iterate_add_apply]
      rw [iteration body decrement counter input output (S (n + 1)) (D n) (S n)
        (decrementTime n) (bodyTime n) (hnonempty n (Nat.lt_succ_self n))
        (hd n (Nat.lt_succ_self n)) (hb n (Nat.lt_succ_self n))]
      exact ih (fun i hi => hnonempty i (Nat.lt_succ_of_lt hi))
        (fun i hi => hd i (Nat.lt_succ_of_lt hi)) (fun i hi => hb i (Nat.lt_succ_of_lt hi))

/-- Uniform per-iteration work gives a linear bound in the number of iterations. -/
theorem runtime_le (decrementTime bodyTime : ℕ → ℕ) (n bound : ℕ)
    (h : ∀ i < n, decrementTime i + bodyTime i ≤ bound) :
    runtime decrementTime bodyTime n ≤ n * (bound + 2) + 1 := by
  induction n with
  | zero => simp [runtime]
  | succ n ih =>
      have ih' := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      have hn := h n (Nat.lt_succ_self n)
      simp only [runtime, Nat.succ_mul]
      omega

/-- The concrete loop certificate preserves every tape asserted by its block traces. -/
def evals (S D : ℕ → ∀ k, List (Γ k)) (decrementTime bodyTime : ℕ → ℕ) (n : ℕ)
    (hempty : S 0 counter = [])
    (hnonempty : ∀ i < n, S (i + 1) counter ≠ [])
    (hd : ∀ i < n, (flip Bind.bind (decrement.machine input output).step)^[decrementTime i]
      (some ⟨some decrement.entry, decrement.initial, S (i + 1)⟩) =
      some ⟨none, decrement.initial, D i⟩)
    (hb : ∀ i < n, (flip Bind.bind (body.machine input output).step)^[bodyTime i]
      (some ⟨some body.entry, body.initial, D i⟩) = some ⟨none, body.initial, S i⟩)
    (bound : ℕ) (hbound : ∀ i < n, decrementTime i + bodyTime i ≤ bound) :
    EvalsToInTime ((loop body decrement counter).machine input output).step
      (cfg body decrement counter input output (some (.inr false)) (S n))
      (some (cfg body decrement counter input output none (S 0))) (n * (bound + 2) + 1) where
  steps := runtime decrementTime bodyTime n
  evals_in_steps := trace body decrement counter input output S D decrementTime bodyTime n
    hempty hnonempty hd hb
  steps_le_m := runtime_le decrementTime bodyTime n bound hbound

end PCP.Machine.BlockLoop
