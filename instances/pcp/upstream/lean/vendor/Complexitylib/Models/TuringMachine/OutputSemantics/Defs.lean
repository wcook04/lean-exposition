/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine

/-!
# Pointwise output semantics for deterministic Turing machines

This definitions layer treats the input string as a program and records the
complete binary string produced by a deterministic machine. The definitions
are machine-relative: no universality assumption is built into them.

`runCfg` is a total bounded evaluator on configurations. It performs the
requested number of transitions and stands still after reaching the halt state.
`ProducesInTime` nevertheless records the actual number of transitions before
halting, so its clock agrees with the exact-step semantics of `TM.reachesIn`.

## Main definitions

- `TM.runCfg` -- total bounded execution, frozen after halting
- `TM.Halts`, `TM.HaltsInTime` -- raw halting semantics for a program
- `TM.Produces` -- a program eventually halts with an exact string output
- `TM.ProducesInTime` -- the same relation with an explicit transition budget
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- The configuration after `steps` transitions, standing still once halted. -/
def runCfg (tm : TM n) (c : Cfg n tm.Q) : ℕ → Cfg n tm.Q
  | 0 => c
  | steps + 1 =>
      let current := runCfg tm c steps
      (tm.step current).getD current

/-- Machine `tm`, run on program `program`, eventually reaches its halt state. -/
def Halts (tm : TM n) (program : List Bool) : Prop :=
  ∃ c, tm.reaches (tm.initCfg program) c ∧ tm.halted c

/-- Machine `tm`, run on program `program`, reaches its halt state within
`time` transitions. The witness `steps` is the actual number of transitions. -/
def HaltsInTime (tm : TM n) (program : List Bool) (time : ℕ) : Prop :=
  ∃ c steps, steps ≤ time ∧ tm.reachesIn steps (tm.initCfg program) c ∧ tm.halted c

/-- Machine `tm`, run on program `program`, eventually halts with exact output `output`. -/
def Produces (tm : TM n) (program output : List Bool) : Prop :=
  ∃ c, tm.reaches (tm.initCfg program) c ∧ tm.halted c ∧ c.output.HasOutput output

/-- Machine `tm`, run on program `program`, halts within `time` transitions with
exact output `output`. The witness `steps` is the actual number of transitions. -/
def ProducesInTime (tm : TM n) (program output : List Bool) (time : ℕ) : Prop :=
  ∃ c steps, steps ≤ time ∧ tm.reachesIn steps (tm.initCfg program) c ∧
    tm.halted c ∧ c.output.HasOutput output

end TM

end Complexity
