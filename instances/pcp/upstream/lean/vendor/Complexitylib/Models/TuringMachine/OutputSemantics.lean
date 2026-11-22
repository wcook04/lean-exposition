/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.OutputSemantics.Internal

/-!
# Pointwise output semantics for deterministic Turing machines

This module exposes total bounded execution and machine-relative relations for
programs that produce complete binary strings. These definitions make no
universality assumption, so they can be reused both for arbitrary description
machines and for later universal-machine invariance theorems.

## Main results

- `TM.runCfg_reachesIn` -- bounded evaluation agrees with relational execution
- `TM.HaltsInTime.iff_runCfg` -- executable bounded halting
- `TM.ProducesInTime.iff_runCfg` -- an executable characterization
- `TM.ProducesInTime.take_time` -- unread program suffixes can be truncated
- `TM.ProducesInTime.mono` -- increasing the clock preserves production
- `Tape.HasOutput.eq` -- a tape has at most one exact binary-string output
- `TM.computes_iff_forall_produces` -- pointwise production uniformizes by length
- `TM.produces_iff_exists_producesInTime` -- bounded and unbounded agreement
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

@[simp] theorem runCfg_zero (tm : TM n) (c : Cfg n tm.Q) : tm.runCfg c 0 = c := rfl

@[simp] theorem runCfg_succ (tm : TM n) (c : Cfg n tm.Q) (steps : ℕ) :
    tm.runCfg c (steps + 1) =
      (tm.step (tm.runCfg c steps)).getD (tm.runCfg c steps) := rfl

/-- Bounded execution composes by addition of clocks. -/
theorem runCfg_add (tm : TM n) (c : Cfg n tm.Q) (first second : ℕ) :
    tm.runCfg c (first + second) = tm.runCfg (tm.runCfg c first) second :=
  runCfg_add_internal tm c first second

/-- Once a configuration is halted, bounded execution stands still. -/
theorem runCfg_of_halted (tm : TM n) {c : Cfg n tm.Q}
    (hhalt : tm.halted c) (steps : ℕ) : tm.runCfg c steps = c :=
  runCfg_of_halted_internal tm hhalt steps

/-- An exact relational run agrees with bounded execution at the same clock. -/
theorem runCfg_of_reachesIn (tm : TM n) {c c' : Cfg n tm.Q} {steps : ℕ}
    (hreach : tm.reachesIn steps c c') : tm.runCfg c steps = c' :=
  runCfg_of_reachesIn_internal tm hreach

/-- The bounded evaluator's endpoint is reachable within its clock. -/
theorem runCfg_reachesIn (tm : TM n) (c : Cfg n tm.Q) (time : ℕ) :
    ∃ steps, steps ≤ time ∧ tm.reachesIn steps c (tm.runCfg c time) :=
  runCfg_reachesIn_internal tm c time

/-- A halted exact-step endpoint remains the endpoint at every larger clock. -/
theorem runCfg_eq_of_reachesIn_halted (tm : TM n) {c c' : Cfg n tm.Q}
    {steps time : ℕ} (hreach : tm.reachesIn steps c c') (hhalt : tm.halted c')
    (hsteps : steps ≤ time) : tm.runCfg c time = c' :=
  runCfg_eq_of_reachesIn_halted_internal tm hreach hhalt hsteps

/-- Bounded halting is exactly the decidable property that the bounded evaluator
has reached the halt state. -/
theorem HaltsInTime.iff_runCfg (tm : TM n) (program : List Bool) (time : ℕ) :
    tm.HaltsInTime program time ↔ tm.halted (tm.runCfg (tm.initCfg program) time) :=
  haltsInTime_iff_runCfg_internal tm program time

/-- Bounded halting is decidable by executing the advertised clock. -/
instance instDecidableHaltsInTime (tm : TM n) (program : List Bool) (time : ℕ) :
    Decidable (tm.HaltsInTime program time) :=
  decidable_of_iff _ (HaltsInTime.iff_runCfg tm program time).symm

/-- Increasing the clock preserves bounded halting. -/
theorem HaltsInTime.mono {tm : TM n} {program : List Bool} {first second : ℕ}
    (hbound : first ≤ second) (hhalt : tm.HaltsInTime program first) :
    tm.HaltsInTime program second :=
  haltsInTime_mono_internal hbound hhalt

/-- Forgetting a clock turns bounded halting into eventual halting. -/
theorem halts_of_haltsInTime {tm : TM n} {program : List Bool} {time : ℕ}
    (hhalt : tm.HaltsInTime program time) : tm.Halts program :=
  halts_of_haltsInTime_internal hhalt

/-- Eventual halting is equivalent to halting under some finite clock. -/
theorem halts_iff_exists_haltsInTime (tm : TM n) (program : List Bool) :
    tm.Halts program ↔ ∃ time, tm.HaltsInTime program time :=
  halts_iff_exists_haltsInTime_internal tm program

/-- Pointwise bounded production is exactly the decidable property of the
bounded evaluator being halted with the requested output. -/
theorem ProducesInTime.iff_runCfg (tm : TM n) (program output : List Bool)
    (time : ℕ) :
    tm.ProducesInTime program output time ↔
      tm.halted (tm.runCfg (tm.initCfg program) time) ∧
        (tm.runCfg (tm.initCfg program) time).output.HasOutput output :=
  producesInTime_iff_runCfg_internal tm program output time

/-- Bounded runs on two inputs stay synchronized in state, work, and output
when the initialized input tapes agree on every cell reachable by the clock. -/
theorem runCfg_initCfg_congr_of_input_cells (tm : TM n)
    (first second : List Bool) (time : ℕ)
    (hinput : ∀ position, position ≤ time →
      (tm.initCfg first).input.cells position =
        (tm.initCfg second).input.cells position) :
    (tm.runCfg (tm.initCfg first) time).state =
        (tm.runCfg (tm.initCfg second) time).state ∧
      (tm.runCfg (tm.initCfg first) time).work =
        (tm.runCfg (tm.initCfg second) time).work ∧
      (tm.runCfg (tm.initCfg first) time).output =
        (tm.runCfg (tm.initCfg second) time).output :=
  runCfg_initCfg_congr_of_input_cells_internal tm first second time hinput

/-- Truncating an input to the clock preserves every initialized input cell
that can be reached within that clock. -/
theorem initCfg_take_input_cells_le (tm : TM n)
    (program : List Bool) (time position : ℕ) (hposition : position ≤ time) :
    (tm.initCfg program).input.cells position =
      (tm.initCfg (program.take time)).input.cells position :=
  initCfg_take_input_cells_le_internal tm program time position hposition

/-- Pointwise bounded production is decidable by running the machine for its
clock and checking the resulting finite output claim. -/
instance instDecidableProducesInTime (tm : TM n) (program output : List Bool)
    (time : ℕ) : Decidable (tm.ProducesInTime program output time) :=
  decidable_of_iff _ (ProducesInTime.iff_runCfg tm program output time).symm

/-- No bounded computation can inspect more than the first `time` program
bits: truncating there preserves exact production within the same clock. -/
theorem ProducesInTime.take_time {tm : TM n} {program output : List Bool}
    {time : ℕ} (hproduce : tm.ProducesInTime program output time) :
    tm.ProducesInTime (program.take time) output time :=
  producesInTime_take_internal hproduce

/-- Increasing the clock preserves pointwise production. -/
theorem ProducesInTime.mono {tm : TM n} {program output : List Bool}
    {first second : ℕ} (hbound : first ≤ second)
    (hproduce : tm.ProducesInTime program output first) :
    tm.ProducesInTime program output second :=
  producesInTime_mono_internal hbound hproduce

/-- Forgetting a clock turns bounded production into eventual production. -/
theorem produces_of_producesInTime {tm : TM n} {program output : List Bool}
    {time : ℕ} (hproduce : tm.ProducesInTime program output time) :
    tm.Produces program output :=
  produces_of_producesInTime_internal hproduce

/-- Producing an output within a clock entails halting within that clock. -/
theorem ProducesInTime.haltsInTime {tm : TM n} {program output : List Bool}
    {time : ℕ} (hproduce : tm.ProducesInTime program output time) :
    tm.HaltsInTime program time :=
  haltsInTime_of_producesInTime_internal hproduce

/-- Producing an output entails eventual halting. -/
theorem Produces.halts {tm : TM n} {program output : List Bool}
    (hproduce : tm.Produces program output) : tm.Halts program :=
  halts_of_produces_internal hproduce

/-- Eventual production is equivalent to production under some finite clock. -/
theorem produces_iff_exists_producesInTime (tm : TM n) (program output : List Bool) :
    tm.Produces program output ↔ ∃ time, tm.ProducesInTime program output time :=
  produces_iff_exists_producesInTime_internal tm program output

/-- Two exact output claims about the same tape have equal lengths. -/
theorem Tape.HasOutput.length_eq {tape : Tape} {left right : List Bool}
    (hleft : tape.HasOutput left) (hright : tape.HasOutput right) :
    left.length = right.length :=
  hasOutput_length_eq_internal hleft hright

/-- A tape has at most one exact binary-string output. -/
theorem Tape.HasOutput.eq {tape : Tape} {left right : List Bool}
    (hleft : tape.HasOutput left) (hright : tape.HasOutput right) : left = right :=
  hasOutput_eq_internal hleft hright

/-- A deterministic program cannot produce two different outputs, even when
the two production claims use different clocks. -/
theorem ProducesInTime.output_unique {tm : TM n} {program left right : List Bool}
    {leftTime rightTime : ℕ} (hleft : tm.ProducesInTime program left leftTime)
    (hright : tm.ProducesInTime program right rightTime) : left = right :=
  producesInTime_output_unique_internal hleft hright

/-- Eventual production by a deterministic program has a unique output. -/
theorem Produces.output_unique {tm : TM n} {program left right : List Bool}
    (hleft : tm.Produces program left) (hright : tm.Produces program right) : left = right :=
  produces_output_unique_internal hleft hright

/-- Whole-function bounded computation is exactly pointwise bounded production
under the same length-indexed clock. -/
theorem computesInTime_iff_forall_producesInTime (tm : TM n)
    (function : List Bool → List Bool) (time : ℕ → ℕ) :
    tm.ComputesInTime function time ↔
      ∀ input, tm.ProducesInTime input (function input) (time input.length) :=
  computesInTime_iff_forall_producesInTime_internal tm function time

/-- A bounded whole-function computation produces the requested output on a
particular input. -/
theorem ComputesInTime.producesInTime {tm : TM n}
    {function : List Bool → List Bool} {time : ℕ → ℕ}
    (hcompute : tm.ComputesInTime function time) (input : List Bool) :
    tm.ProducesInTime input (function input) (time input.length) :=
  (computesInTime_iff_forall_producesInTime tm function time).mp hcompute input

/-- Eventual whole-function computation is equivalent to eventual pointwise
production. The reverse implication uniformizes halting times over the finite
set of Boolean strings at each input length. -/
theorem computes_iff_forall_produces (tm : TM n) (function : List Bool → List Bool) :
    tm.Computes function ↔ ∀ input, tm.Produces input (function input) :=
  computes_iff_forall_produces_internal tm function

/-- A whole-function computation produces the requested output on a particular
input. -/
theorem Computes.produces {tm : TM n} {function : List Bool → List Bool}
    (hcompute : tm.Computes function) (input : List Bool) :
    tm.Produces input (function input) :=
  (computes_iff_forall_produces tm function).mp hcompute input

end TM

end Complexity
