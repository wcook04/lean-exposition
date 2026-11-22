/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine

/-!
# Deterministic Boolean-oracle Turing machines -- definitions

This module adds a dedicated query tape and a one-step Boolean-oracle query
mechanism to the library's deterministic Turing-machine model. Local steps
retain the named read-only input, read-write work, and output tapes. A query
state instead reads the binary prefix currently delimited by the query-tape
head, leaves every tape unchanged, and branches to one of two states according
to the oracle answer.

The query cost convention is explicit: one oracle lookup is one machine step,
while writing and positioning the query takes ordinary local steps. Query
strings use cells `1, ..., head - 1`; `1` is true and every other tape symbol is
false. Constructions that need a canonical binary query should establish that
those cells contain only `0` or `1`.
-/


@[expose] public section

namespace Complexity

/-- A Boolean oracle answers one bit for every finite binary query string. -/
abbrev BooleanOracle := List Bool → Bool

namespace BooleanOracle

/-- An oracle decides a language when its answer bit is its exact
characteristic function on every finite query string. -/
def Decides (oracle : BooleanOracle) (language : Language) : Prop :=
  ∀ query, oracle query = true ↔ query ∈ language

end BooleanOracle

namespace Tape

/-- Query string delimited by the query-tape head. Cells strictly between the
left marker and the head are read in increasing order. The convention is total:
only `1` maps to true; `0`, blank, and the left marker map to false. -/
def oracleQuery (tape : Tape) : List Bool :=
  List.ofFn fun index : Fin (tape.head - 1) =>
    match tape.cells (index.val + 1) with
    | Γ.one => true
    | _ => false

end Tape

/-- Configuration of an oracle TM with `n` ordinary work tapes and one
dedicated read-write query tape. -/
structure OracleCfg (n : ℕ) (Q : Type) where
  /-- Current finite-control state. -/
  state : Q
  /-- Read-only input tape. -/
  input : Tape
  /-- Dedicated query tape. -/
  query : Tape
  /-- Ordinary read-write work tapes. -/
  work : Fin n → Tape
  /-- Read-write output tape. -/
  output : Tape

namespace OracleCfg

/-- Initial oracle-machine configuration. -/
abbrev init (qstart : Q) (input : List Bool) : OracleCfg n Q :=
  { state := qstart
    input := Tape.init (input.map Γ.ofBool)
    query := Tape.init []
    work := fun _ => Tape.init []
    output := Tape.init [] }

/-- Forget the dedicated query tape. -/
def erase (cfg : OracleCfg n Q) : Cfg n Q :=
  { state := cfg.state
    input := cfg.input
    work := cfg.work
    output := cfg.output }

end OracleCfg

/-- One ordinary, non-query transition of an oracle TM. -/
structure OracleLocalTransition (n : ℕ) (Q : Type) where
  /-- Next finite-control state. -/
  nextState : Q
  /-- Symbol written on the query tape. -/
  queryWrite : Γw
  /-- Symbols written on the ordinary work tapes. -/
  workWrites : Fin n → Γw
  /-- Symbol written on the output tape. -/
  outputWrite : Γw
  /-- Input-head movement. -/
  inputDir : Dir3
  /-- Query-head movement. -/
  queryDir : Dir3
  /-- Ordinary work-head movements. -/
  workDirs : Fin n → Dir3
  /-- Output-head movement. -/
  outputDir : Dir3

/-- A deterministic oracle TM with one dedicated query tape.

If `queryTransition q = some (yesState, noState)`, state `q` performs an
oracle lookup rather than applying `localTransition`; a true answer enters
`yesState` and a false answer enters `noState`. -/
structure OracleTM (n : ℕ) where
  /-- Finite type of machine states. -/
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  /-- Designated start state. -/
  qstart : Q
  /-- Designated halt state. -/
  qhalt : Q
  /-- States that perform an oracle query and their true/false successors. -/
  queryTransition : Q → Option (Q × Q)
  /-- Transition used at every non-query, non-halted state. -/
  localTransition :
    Q → Γ → Γ → (Fin n → Γ) → Γ → OracleLocalTransition n Q
  /-- A local transition reading a left marker moves that head right. -/
  localTransition_right_of_start :
    ∀ (q : Q) (inputHead queryHead : Γ) (workHeads : Fin n → Γ)
      (outputHead : Γ),
      let transition :=
        localTransition q inputHead queryHead workHeads outputHead
      (inputHead = Γ.start → transition.inputDir = Dir3.right) ∧
      (queryHead = Γ.start → transition.queryDir = Dir3.right) ∧
      (∀ index, workHeads index = Γ.start →
        transition.workDirs index = Dir3.right) ∧
      (outputHead = Γ.start → transition.outputDir = Dir3.right)

attribute [instance] OracleTM.decEq OracleTM.finQ

namespace OracleTM

variable {n : ℕ}

/-- Execute one oracle-machine step. A query lookup costs exactly one step and
changes only the finite-control state. -/
def step (machine : OracleTM n) (oracle : BooleanOracle)
    (cfg : OracleCfg n machine.Q) : Option (OracleCfg n machine.Q) :=
  if cfg.state = machine.qhalt then none
  else
    match machine.queryTransition cfg.state with
    | some (yesState, noState) =>
        some { cfg with
          state := if oracle cfg.query.oracleQuery then yesState else noState }
    | none =>
        let transition := machine.localTransition cfg.state cfg.input.read
          cfg.query.read (fun index => (cfg.work index).read) cfg.output.read
        some
          { state := transition.nextState
            input := cfg.input.move transition.inputDir
            query := cfg.query.writeAndMove transition.queryWrite
              transition.queryDir
            work := fun index => (cfg.work index).writeAndMove
              (transition.workWrites index) (transition.workDirs index)
            output := cfg.output.writeAndMove transition.outputWrite
              transition.outputDir }

/-- Initial configuration for an oracle TM. -/
abbrev initCfg (machine : OracleTM n) (input : List Bool) :
    OracleCfg n machine.Q :=
  OracleCfg.init machine.qstart input

/-- An oracle configuration is halted in the designated halt state. -/
abbrev halted (machine : OracleTM n) (cfg : OracleCfg n machine.Q) : Prop :=
  cfg.state = machine.qhalt

/-- One-step oracle execution relation. -/
def stepRel (machine : OracleTM n) (oracle : BooleanOracle)
    (cfg next : OracleCfg n machine.Q) : Prop :=
  machine.step oracle cfg = some next

/-- Exact-time deterministic oracle execution. -/
inductive reachesIn (machine : OracleTM n) (oracle : BooleanOracle) :
    ℕ → OracleCfg n machine.Q → OracleCfg n machine.Q → Prop where
  | zero : reachesIn machine oracle 0 cfg cfg
  | step : machine.step oracle cfg = some middle →
      reachesIn machine oracle time middle result →
      reachesIn machine oracle (time + 1) cfg result

/-- Oracle-machine acceptance. -/
def Accepts (machine : OracleTM n) (oracle : BooleanOracle)
    (input : List Bool) : Prop :=
  ∃ cfg time, machine.reachesIn oracle time (machine.initCfg input) cfg ∧
    machine.halted cfg ∧ cfg.output.cells 1 = Γ.one

/-- Oracle-machine acceptance within a time budget. -/
def AcceptsInTime (machine : OracleTM n) (oracle : BooleanOracle)
    (input : List Bool) (timeBound : ℕ) : Prop :=
  ∃ cfg time, time ≤ timeBound ∧
    machine.reachesIn oracle time (machine.initCfg input) cfg ∧
    machine.halted cfg ∧ cfg.output.cells 1 = Γ.one

/-- An oracle TM decides a language within a length-dependent time bound. -/
def DecidesInTime (machine : OracleTM n) (oracle : BooleanOracle)
    (language : Language) (timeBound : ℕ → ℕ) : Prop :=
  ∀ input, ∃ cfg time, time ≤ timeBound input.length ∧
    machine.reachesIn oracle time (machine.initCfg input) cfg ∧
    machine.halted cfg ∧
    (input ∈ language → cfg.output.cells 1 = Γ.one) ∧
    (input ∉ language → cfg.output.cells 1 = Γ.zero)

end OracleTM

namespace TM

/-- Regard an ordinary TM as an oracle TM whose query-state map is everywhere
`none`. The extra query tape is operationally inert and never affects the
ordinary tapes. -/
def toOracleTM (machine : TM n) : OracleTM n where
  Q := machine.Q
  qstart := machine.qstart
  qhalt := machine.qhalt
  queryTransition := fun _ => none
  localTransition := fun state inputHead queryHead workHeads outputHead =>
    let (nextState, workWrites, outputWrite, inputDir, workDirs, outputDir) :=
      machine.δ state inputHead workHeads outputHead
    { nextState
      queryWrite := Γw.blank
      workWrites
      outputWrite
      inputDir
      queryDir := if queryHead = Γ.start then Dir3.right else Dir3.stay
      workDirs
      outputDir }
  localTransition_right_of_start := by
    intro state inputHead queryHead workHeads outputHead
    have hmachine := machine.δ_right_of_start
      state inputHead workHeads outputHead
    dsimp only
    generalize htransition : machine.δ state inputHead workHeads outputHead =
      transition at hmachine
    obtain ⟨nextState, workWrites, outputWrite, inputDir, workDirs,
      outputDir⟩ := transition
    simp only [htransition] at hmachine ⊢
    refine ⟨hmachine.1, ?_, hmachine.2.1, hmachine.2.2⟩
    intro hquery
    simp [hquery]

end TM

end Complexity
