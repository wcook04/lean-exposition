/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Combinators.Internal.SentinelStep

/-!
# What a space bound says about the tape, not just the head

⚠️ Unreviewed by Bolton

`Cfg.WithinDecisionSpace` bounds head *positions*. A caller that has to clear up after a
subroutine needs more: it needs to know that nothing was written past the window, so that a wipe
of that width suffices. That follows, since a step writes only under its head — but it has to be
carried along the run.

Bounding the same thing by the running time instead would be a disaster here: a space-bounded
machine may run for exponentially many steps, and a wipe of exponential width is not a wipe a
polynomial-space machine can afford.

## Main results

- `TM.work_cells_far_of_reachesIn` — a run whose heads stay inside `S` writes nothing past `S`
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **A run that stays inside a window writes nothing outside it.** Each step writes only under
its head, and every head along the run is inside the window, so a cell beyond it still holds what
it did at the start. -/
theorem work_cells_far_of_reachesIn {tm : TM n} (S : ℕ) :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      (∀ d, tm.reaches c d → ∀ i, (d.work i).head ≤ S) →
      (∀ i p, S < p → (c.work i).cells p = Γ.blank) →
      ∀ i p, S < p → (c'.work i).cells p = Γ.blank := by
  intro t
  induction t with
  | zero =>
      intro c c' hreach _ hblank
      cases hreach
      exact hblank
  | succ t ih =>
      intro c c' hreach hspace hblank
      cases hreach with
      | step hstep hrest =>
          rename_i cmid
          refine ih hrest (fun d hd i => hspace d (Relation.ReflTransGen.head hstep hd) i)
            (fun i p hp => ?_)
          have hhead : (c.work i).head ≤ S :=
            hspace c (Relation.ReflTransGen.refl) i
          rw [step_work_cells_ne tm hstep i p (by omega)]
          exact hblank i p hp

end TM

end Complexity
