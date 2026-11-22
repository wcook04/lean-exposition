import Mathlib.Computability.TuringMachine.Computable

/-!
# Terminal-preserving bounded evaluation

## The problem this module solves

A TM2 certificate records a *successful* configuration:

```text
(flip Bind.bind tm.step)^[h.steps] (some (initList tm l)) = some (haltList tm o).
```

The next transition out of `haltList` is outer `none`, because a configuration with label `none`
has no successor.  So iterating the optional step function for the full time budget `m` — which is
what a simulator with a fixed polynomial bound must do, since it does not know `h.steps` — throws
the answer away whenever `h.steps < m`.  The outer `none` carries no configuration at all, so the
output stack is not recoverable from it.

The fix is a simulator convention, not a change to the machine: iterate the **total** step

```text
keepStep step c = (step c).getD c
```

which parks on a configuration once the machine has stopped.  A successful optional trace of `n`
steps is also a `keepStep` trace of `n` steps, and every further iteration is then idle.

## What is and is not claimed

`keepStep` does **not** redefine the counted steps of the source machine.  `TM2OutputsInTime` and
every count-preservation theorem in `PCP/Complexity/Recode.lean` continue to speak about
`tm.step`.  This module only says that a bounded evaluator may be run past a machine's halting
point without losing the result.

Nothing here is a computability claim.  `keepStep` is the single *total* step; `boundedEval`
iterates it with `Function.iterate`, which is the shape a later `Primrec` development needs
(`Primrec.nat_iterate`) — but no `Primrec` instance is asserted at this stage.

## This module is generic

Only mathlib is imported.  The generic section fixes an arbitrary optional transition `step`; the
`FinTM2` section specialises it.
-/

namespace PCP.Machine

open Turing

section Generic

variable {σ : Type*} (step : σ → Option σ)

/-- The **terminal-preserving** total step: follow `step` when it is defined, and stay put when it
is not.  Iterating this is the simulator convention described in the module header. -/
def keepStep (c : σ) : σ := (step c).getD c

variable {step}

@[simp] theorem keepStep_of_none {c : σ} (h : step c = none) : keepStep step c = c := by
  simp [keepStep, h]

@[simp] theorem keepStep_of_some {c c' : σ} (h : step c = some c') : keepStep step c = c' := by
  simp [keepStep, h]

/-- Outer `none` is absorbing: once the optional iteration has lost its configuration, no number of
further steps recovers one. -/
theorem iterate_bind_none : ∀ n : ℕ, (flip Bind.bind step)^[n] none = none
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply]; exact iterate_bind_none n

/-- A successful optional trace of `n` steps is a `keepStep` trace of the **same** `n` steps.

The two agree exactly as long as the machine is still running; they part company only after it
stops, which is the next lemma. -/
theorem keepStep_iterate_of_evalsTo :
    ∀ (n : ℕ) {start z : σ}, (flip Bind.bind step)^[n] (some start) = some z →
      (keepStep step)^[n] start = z
  | 0, _, _, h => Option.some_inj.1 h
  | n + 1, start, z, h => by
      rw [Function.iterate_succ_apply] at h ⊢
      cases hs : step start with
      | none =>
          rw [show (flip Bind.bind step) (some start) = none from hs, iterate_bind_none] at h
          exact absurd h (by simp)
      | some c' =>
          rw [show (flip Bind.bind step) (some start) = some c' from hs] at h
          rw [keepStep_of_some hs]
          exact keepStep_iterate_of_evalsTo n h

/-- Once the transition is undefined, every further iteration is idle. -/
theorem iterate_keepStep_terminal {z : σ} (hz : step z = none) :
    ∀ d : ℕ, (keepStep step)^[d] z = z
  | 0 => rfl
  | d + 1 => by
      rw [Function.iterate_succ_apply, keepStep_of_none hz]
      exact iterate_keepStep_terminal hz d

/-- **The terminal-preserving iteration theorem.**  A successful `n`-step optional trace ending at a
configuration with no successor is retained by `keepStep` for every budget `m ≥ n`.

This is the statement the bounded simulator needs: it may use the explicit polynomial budget `m`
without knowing the certificate's actual `n`. -/
theorem keepStep_iterate_of_terminal {n m : ℕ} {start z : σ}
    (h : (flip Bind.bind step)^[n] (some start) = some z) (hnm : n ≤ m) (hz : step z = none) :
    (keepStep step)^[m] start = z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [Nat.add_comm, Function.iterate_add_apply, keepStep_iterate_of_evalsTo n h,
    iterate_keepStep_terminal hz]

/-- The contrast that gives the previous theorem its content: run the **optional** iteration one
step past the terminal configuration and the configuration is gone, not merely unchanged. -/
theorem iterate_bind_eq_none_of_terminal {n m : ℕ} {start z : σ}
    (h : (flip Bind.bind step)^[n] (some start) = some z) (hz : step z = none) (hnm : n < m) :
    (flip Bind.bind step)^[m] (some start) = none := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hnm
  rw [show n + d + 1 = (d + 1) + n from by omega, Function.iterate_add_apply, h,
    Function.iterate_succ_apply, show (flip Bind.bind step) (some z) = none from hz,
    iterate_bind_none]

end Generic

section FinTM2

open Turing.TM2

/-- A halting configuration has no successor: this is what makes the optional iteration lose the
answer, and what discharges the `step z = none` hypothesis above for TM2 certificates. -/
@[simp] theorem step_haltList (tm : FinTM2) (o : List (tm.Γ tm.k₁)) :
    tm.step (haltList tm o) = none := rfl

/-- Run `tm` for exactly `budget` terminal-preserving steps. -/
def boundedEval (tm : FinTM2) (budget : ℕ) (c : tm.Cfg) : tm.Cfg :=
  (keepStep tm.step)^[budget] c

@[simp] theorem boundedEval_zero (tm : FinTM2) (c : tm.Cfg) : boundedEval tm 0 c = c := rfl

/-- An already-halted configuration is a fixed point of bounded evaluation, for every budget. -/
@[simp] theorem boundedEval_haltList (tm : FinTM2) (budget : ℕ) (o : List (tm.Γ tm.k₁)) :
    boundedEval tm budget (haltList tm o) = haltList tm o :=
  iterate_keepStep_terminal (step_haltList tm o) budget

/-- **Bounded evaluation recovers a certificate's output.**  Any budget at least the certificate's
declared bound — in particular the explicit time polynomial, evaluated without consulting the
certificate's actual step count — lands on the exact `haltList`, cleanup included. -/
theorem boundedEval_initList {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {o : List (tm.Γ tm.k₁)} {m : ℕ}
    (h : TM2OutputsInTime tm l (some o) m) {budget : ℕ} (hb : m ≤ budget) :
    boundedEval tm budget (initList tm l) = haltList tm o :=
  keepStep_iterate_of_terminal (n := h.steps) h.evals_in_steps (h.steps_le_m.trans hb)
    (step_haltList tm o)

/-- The output stack of the bounded evaluation is the certificate's output list. -/
theorem boundedEval_initList_stk {tm : FinTM2} {l : List (tm.Γ tm.k₀)} {o : List (tm.Γ tm.k₁)}
    {m : ℕ} (h : TM2OutputsInTime tm l (some o) m) {budget : ℕ} (hb : m ≤ budget) :
    (boundedEval tm budget (initList tm l)).stk tm.k₁ = o := by
  rw [boundedEval_initList h hb]
  change dite (tm.k₁ = tm.k₁) _ _ = o
  rw [dite_eq_left (rfl : tm.k₁ = tm.k₁)]
  exact rfl

/-! ## The polynomial-budget contract

These are the forms the computability bridge consumes.  The budget is `h.time.eval (ea a).length`:
a function of the **input length alone**.  It is never the certificate's own `steps`, and `f a` is
never evaluated to obtain it — the simulator may not consult either. -/

variable {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}

/-- Running a polynomial-time witness for its declared polynomial budget reaches the exact halting
configuration, cleanup included, for every input. -/
theorem boundedEval_polyTime (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    boundedEval h.tm (h.time.eval (ea a).length)
        (initList h.tm ((ea a).map h.inputAlphabet.invFun))
      = haltList h.tm ((eb (f a)).map h.outputAlphabet.invFun) :=
  boundedEval_initList (h.outputsFun a) (le_refl _)

/-- Its output stack is the encoded result, in the machine's own alphabet. -/
theorem boundedEval_polyTime_stk (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (boundedEval h.tm (h.time.eval (ea a).length)
        (initList h.tm ((ea a).map h.inputAlphabet.invFun))).stk h.tm.k₁
      = (eb (f a)).map h.outputAlphabet.invFun :=
  boundedEval_initList_stk (h.outputsFun a) (le_refl _)

/-- Reading that stack through the output-alphabet equivalence gives `eb (f a)` on the nose.  This
is the equation a simulator has to reproduce: input length in, encoded answer out. -/
theorem boundedEval_polyTime_output (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    ((boundedEval h.tm (h.time.eval (ea a).length)
        (initList h.tm ((ea a).map h.inputAlphabet.invFun))).stk h.tm.k₁).map h.outputAlphabet
      = eb (f a) := by
  rw [boundedEval_polyTime_stk h a, List.map_map]
  simp [Function.comp_def]

end FinTM2

end PCP.Machine
