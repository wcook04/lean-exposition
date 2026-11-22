import PCP.Complexity.CallEmbed
import PCP.Complexity.BoundedEval

/-!
# The parent machine, and transport of successful callee traces

`PCP/Complexity/CallEmbed.lean` proved the statement-level correspondence.  This module packages an
actual `FinTM2` around it and transports a callee's *successful finite* execution into the parent at
**exactly the same step count**.

## Only from an active source label

The step equation below is conditional on `c.l = some l`, and that is essential rather than
convenient.  At a terminal callee configuration `tm.step` is outer `none`, while the parent sits at
`some (inr ret)` — an active label with the caller's own continuation still to run.  An
unconditional semiconjugacy is therefore **false**, and `parentStep_embedCfg_of_active` is as strong
a step equation as exists.

The trace theorem works because a *successful* source trace cannot have passed through a terminal
label: the first step from one is outer `none`, which is absorbing.  So the induction consumes one
step at a time and only ever applies the equation where it holds, without a reachability or cleanup
hypothesis on the starting configuration.

## Stop at the boundary

Transport ends at the certificate's own recorded `steps`.  It is not iterated to the certificate's
upper bound `m`, which is carried along as a bound only.  Running the parent for a slack budget
would execute the caller's continuation, and B0's terminal-preserving iteration cannot freeze an
*active* return label — that convention parks on configurations with no successor, which is exactly
what the return label is not.

## What this does not pay for

The callee's step count is preserved, so nothing here charges call entry, input preparation,
copying, output transfer, or resetting storage for a second call.  Nor does the callee's push bound
bound the parent's: the parent's maximum must also cover the supplied `caller` program.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

section

variable (tm : FinTM2) (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)
  {τ L : Type} [Fintype τ] [Fintype L] (t₀ : τ) (ret : L)
  (caller : L → Stmt (embedΓ tm F Γf) (tm.Λ ⊕ L) (tm.σ × τ))

/-- The parent: the callee's translated program on the left labels, an **arbitrary** caller program
on the right.  Agreement during a call comes from the left-hand equations and the finite source
trace, never from assuming the caller is benign. -/
def parentTM : FinTM2 where
  K := tm.K ⊕ F
  kDecidableEq := inferInstanceAs (DecidableEq (tm.K ⊕ F))
  kFin := inferInstanceAs (Fintype (tm.K ⊕ F))
  k₀ := .inl tm.k₀
  k₁ := .inl tm.k₁
  Γ := embedΓ tm F Γf
  Γk₀Fin := tm.Γk₀Fin
  Λ := tm.Λ ⊕ L
  main := .inl tm.main
  ΛFin := inferInstanceAs (Fintype (tm.Λ ⊕ L))
  σ := tm.σ × τ
  initialState := (tm.initialState, t₀)
  σFin := inferInstanceAs (Fintype (tm.σ × τ))
  m := fun
    | .inl l => liftStmt ret (tm.m l)
    | .inr l => caller l

@[simp] theorem parentTM_m_inl (l : tm.Λ) :
    (parentTM tm F Γf t₀ ret caller).m (.inl l) = liftStmt ret (tm.m l) := rfl

@[simp] theorem parentTM_m_inr (l : L) :
    (parentTM tm F Γf t₀ ret caller).m (.inr l) = caller l := rfl

variable {tm F Γf}

/-- A configuration with no label has no successor. -/
theorem step_eq_none_of_l_none {c : tm.Cfg} (h : c.l = none) : tm.step c = none := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => rfl
  | some l => exact absurd h (by simp)

/-- **The step equation, at an active source label.**  Stated about the returned parent machine, so
a later change to its program is checked here. -/
theorem parentStep_embedCfg_of_active (t : τ) (frame : ∀ j : F, List (Γf j)) {c : tm.Cfg}
    {l : tm.Λ} (h : c.l = some l) :
    (parentTM tm F Γf t₀ ret caller).step (embedCfg ret t frame c)
      = Option.map (embedCfg ret t frame) (tm.step c) := by
  obtain ⟨l', v, S⟩ := c
  cases l' with
  | none => exact absurd h (by simp)
  | some l' =>
      change some (stepAux ((parentTM tm F Γf t₀ ret caller).m (.inl l')) (v, t)
          (embedStacks tm F Γf S frame))
        = Option.map (embedCfg ret t frame) (tm.step ⟨some l', v, S⟩)
      exact congrArg some (stepAux_liftStmt ret t frame (tm.m l') v S)

/-- **Trace transport at the exact recorded count.**  Arbitrary start and finish: the endpoint may
be an internal callee configuration or the return boundary, and no terminal-label, reachability or
cleanup hypothesis is imposed. -/
theorem iterate_embedCfg (t : τ) (frame : ∀ j : F, List (Γf j)) :
    ∀ (n : ℕ) {start finish : tm.Cfg},
      (flip Bind.bind tm.step)^[n] (some start) = some finish →
      (flip Bind.bind (parentTM tm F Γf t₀ ret caller).step)^[n]
          (some (embedCfg ret t frame start))
        = some (embedCfg ret t frame finish)
  | 0, start, finish, h => by
      rw [Function.iterate_zero_apply] at h ⊢
      exact congrArg (fun c => some (embedCfg ret t frame c)) (Option.some_inj.1 h)
  | n + 1, start, finish, h => by
      rw [Function.iterate_succ_apply] at h ⊢
      cases hl : start.l with
      | none =>
          rw [show (flip Bind.bind tm.step) (some start) = none from
            step_eq_none_of_l_none hl, iterate_bind_none] at h
          exact absurd h (by simp)
      | some l =>
          have hstep : (flip Bind.bind tm.step) (some start) = tm.step start := rfl
          rw [hstep] at h
          cases hs : tm.step start with
          | none => rw [hs, iterate_bind_none] at h; exact absurd h (by simp)
          | some c' =>
              rw [hs] at h
              have hpar : (flip Bind.bind (parentTM tm F Γf t₀ ret caller).step)
                  (some (embedCfg ret t frame start))
                    = some (embedCfg ret t frame c') := by
                change (parentTM tm F Γf t₀ ret caller).step (embedCfg ret t frame start) = _
                rw [parentStep_embedCfg_of_active t₀ ret caller t frame hl, hs, Option.map_some]
              rw [hpar]
              exact iterate_embedCfg t frame n h

/-- The transported certificate.  `steps` and `steps_le_m` are copied verbatim; the upper bound `m`
is retained as a bound and never used as the execution length. -/
def embedEvals (t : τ) (frame : ∀ j : F, List (Γf j)) {start finish : tm.Cfg} {m : ℕ}
    (h : EvalsToInTime tm.step start (some finish) m) :
    EvalsToInTime (parentTM tm F Γf t₀ ret caller).step (embedCfg ret t frame start)
      (some (embedCfg ret t frame finish)) m where
  steps := h.steps
  evals_in_steps := iterate_embedCfg t₀ ret caller t frame h.steps h.evals_in_steps
  steps_le_m := h.steps_le_m

@[simp] theorem embedEvals_steps (t : τ) (frame : ∀ j : F, List (Γf j)) {start finish : tm.Cfg}
    {m : ℕ} (h : EvalsToInTime tm.step start (some finish) m) :
    (embedEvals t₀ ret caller t frame h).steps = h.steps := rfl

end

end PCP.Machine
