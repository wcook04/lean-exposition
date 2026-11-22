/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Hoare.Defs
public import Complexitylib.Models.TuringMachine.Frame
public import Complexitylib.Models.TuringMachine.Internal

/-!
# Carrying the left-marker invariant through a contract

⚠️ Unreviewed by Bolton

Every subroutine that rewinds, parks, or wipes asks its tapes for `Tape.StartInvariant`: the left
marker at cell zero and nowhere else. A run cannot destroy it — `TM.reachesIn_startInvariant` —
but a contract that does not mention it cannot pass it on, and a stage assembled from such
contracts is stuck.

The rule below adds it: if a machine's precondition guarantees the invariant, its postcondition
may be strengthened by it, for free.

## Main results

- `TM.HoareTime.startInvariant` — a contract carries the left-marker invariant along
- `TM.HoareTime.headBound` — and a bound on how far its heads can have travelled
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **A contract carries the left-marker invariant.** No machine can put a marker anywhere but
cell zero, so a stage whose entry tapes are start-invariant leaves start-invariant tapes behind —
which is what the rewinds and wipes downstream ask for. -/
theorem HoareTime.startInvariant {tm : TM n} {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b)
    (hpre : ∀ inp work out, pre inp work out →
      Tape.StartInvariant inp ∧ (∀ i, Tape.StartInvariant (work i)) ∧ Tape.StartInvariant out) :
    tm.HoareTime pre
      (fun inp work out => post inp work out ∧
        Tape.StartInvariant inp ∧ (∀ i, Tape.StartInvariant (work i)) ∧ Tape.StartInvariant out)
      b := by
  intro inp work out hp
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h inp work out hp
  obtain ⟨hi, hw, ho⟩ := hpre inp work out hp
  exact ⟨c', t, ht, hreach, hhalt, hpost, reachesIn_startInvariant hreach hi hw ho⟩

/-- **A contract bounds where its heads end up.** A head moves at most one cell per step, so a
stage that starts inside `h₀` and runs for `b` steps ends inside `h₀ + b` — which is what the
rewinds downstream need in order to know how far to scan. -/
theorem HoareTime.headBound {tm : TM n} {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b) (h₀ : ℕ)
    (hpre : ∀ inp work out, pre inp work out →
      (∀ i, (work i).head ≤ h₀) ∧ inp.head ≤ h₀ ∧ out.head ≤ h₀) :
    tm.HoareTime pre
      (fun inp work out => post inp work out ∧
        (∀ i, (work i).head ≤ h₀ + b) ∧ inp.head ≤ h₀ + b ∧ out.head ≤ h₀ + b)
      b := by
  intro inp work out hp
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h inp work out hp
  obtain ⟨hw, hi, ho⟩ := hpre inp work out hp
  obtain ⟨hin, hout, hwork⟩ := head_le_start_add_of_reachesIn tm hreach
  dsimp only at hin hout hwork
  refine ⟨c', t, ht, hreach, hhalt, hpost, fun i => ?_, ?_, ?_⟩
  · have := hwork i
    have := hw i
    show (c'.work i).head ≤ h₀ + b
    omega
  · show c'.input.head ≤ h₀ + b
    omega
  · show c'.output.head ≤ h₀ + b
    omega

end TM

end Complexity
