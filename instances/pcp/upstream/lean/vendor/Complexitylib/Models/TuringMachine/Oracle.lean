/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Oracle.Defs
public import Complexitylib.Models.TuringMachine.Oracle.Internal

/-!
# Deterministic Boolean-oracle Turing machines

The oracle model has a dedicated query tape and charges one step per lookup.
Writing the query remains part of ordinary machine execution. Exact-time runs
are deterministic, and the ordinary-TM embedding has no query states, is
independent of the supplied oracle, and erases step-for-step to the source TM.

This first layer is deterministic. Nondeterministic oracle execution and
relativized complexity classes are deliberately left to subsequent modules.
-/


public section

namespace Complexity

namespace Tape

/-- A query contains exactly the cells strictly between the left marker and
the query-tape head. -/
@[simp] theorem length_oracleQuery (tape : Tape) :
    tape.oracleQuery.length = tape.head - 1 :=
  length_oracleQuery_internal tape

end Tape

namespace OracleCfg

/-- Erasing the query tape from an initial oracle configuration gives the
ordinary initial configuration. -/
@[simp] theorem erase_init (qstart : Q) (input : List Bool) :
    (OracleCfg.init (n := n) qstart input).erase = Cfg.init qstart input :=
  erase_init_internal qstart input

end OracleCfg

namespace OracleTM

variable {n : ℕ}

/-- An oracle step is absent exactly at the halt state. -/
theorem step_eq_none_iff_halted
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} :
    machine.step oracle cfg = none ↔ machine.halted cfg :=
  step_eq_none_iff_halted_internal

/-- Deterministic one-step oracle execution has at most one successor. -/
theorem stepRel_functional
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg first second : OracleCfg n machine.Q}
    (hfirst : machine.stepRel oracle cfg first)
    (hsecond : machine.stepRel oracle cfg second) : first = second :=
  stepRel_functional_internal hfirst hsecond

/-- An exact-time deterministic oracle run has a unique final configuration. -/
theorem reachesIn_functional
    {machine : OracleTM n} {oracle : BooleanOracle}
    {time : ℕ} {start first second : OracleCfg n machine.Q}
    (hfirst : machine.reachesIn oracle time start first)
    (hsecond : machine.reachesIn oracle time start second) : first = second :=
  reachesIn_functional_internal hfirst hsecond

/-- A step-preserving configuration map sends an exact-time oracle run to an
exact-time run of an ordinary target machine. -/
theorem reachesIn_map
    {machine : OracleTM n} {oracle : BooleanOracle} {workTapes : ℕ}
    {target : TM workTapes}
    (mapCfg : OracleCfg n machine.Q → Cfg workTapes target.Q)
    (hstep : ∀ {cfg next}, machine.step oracle cfg = some next →
      target.step (mapCfg cfg) = some (mapCfg next))
    {time : ℕ} {start result : OracleCfg n machine.Q}
    (hreach : machine.reachesIn oracle time start result) :
    target.reachesIn time (mapCfg start) (mapCfg result) :=
  reachesIn_map_internal mapCfg hstep hreach

/-- A true oracle answer enters the declared true-successor state and leaves
all tapes unchanged. -/
theorem step_query_true
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = true) :
    machine.step oracle cfg = some { cfg with state := yesState } :=
  step_query_true_internal hhalt hquery hanswer

/-- A false oracle answer enters the declared false-successor state and leaves
all tapes unchanged. -/
theorem step_query_false
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = false) :
    machine.step oracle cfg = some { cfg with state := noState } :=
  step_query_false_internal hhalt hquery hanswer

/-- A true oracle lookup is one exact execution step. -/
theorem reachesIn_one_query_true
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = true) :
    machine.reachesIn oracle 1 cfg { cfg with state := yesState } :=
  reachesIn_one_query_true_internal hhalt hquery hanswer

/-- A false oracle lookup is one exact execution step. -/
theorem reachesIn_one_query_false
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = false) :
    machine.reachesIn oracle 1 cfg { cfg with state := noState } :=
  reachesIn_one_query_false_internal hhalt hquery hanswer

end OracleTM

namespace TM

/-- The ordinary-machine embedding has no query states. -/
@[simp] theorem toOracleTM_queryTransition (machine : TM n) (state : machine.Q) :
    machine.toOracleTM.queryTransition state = none :=
  toOracleTM_queryTransition_internal machine state

/-- Every step of an embedded ordinary machine is independent of the oracle. -/
theorem toOracleTM_step_oracle_independent
    (machine : TM n) (first second : BooleanOracle)
    (cfg : OracleCfg n machine.Q) :
    machine.toOracleTM.step first cfg = machine.toOracleTM.step second cfg :=
  toOracleTM_step_oracle_independent_internal machine first second cfg

/-- Erasing the query tape after one embedded-machine step agrees exactly with
one step of the source ordinary TM. -/
theorem erase_toOracleTM_step
    (machine : TM n) (oracle : BooleanOracle)
    (cfg : OracleCfg n machine.Q) :
    Option.map OracleCfg.erase (machine.toOracleTM.step oracle cfg) =
      machine.step cfg.erase :=
  erase_toOracleTM_step_internal machine oracle cfg

/-- Erasing the query tape sends every exact-time embedded-machine run to the
source ordinary-machine run with the same number of steps. -/
theorem erase_toOracleTM_reachesIn
    (machine : TM n) (oracle : BooleanOracle)
    {time : ℕ} {start result : OracleCfg n machine.Q}
    (hreach : machine.toOracleTM.reachesIn oracle time start result) :
    machine.reachesIn time start.erase result.erase :=
  erase_toOracleTM_reachesIn_internal machine oracle hreach

/-- Every source-machine step lifts to an embedded oracle-machine step from
any configuration with the required erased ordinary state. -/
theorem exists_toOracleTM_step_of_step_erase
    (machine : TM n) (oracle : BooleanOracle)
    {cfg : OracleCfg n machine.Q} {next : Cfg n machine.Q}
    (hstep : machine.step cfg.erase = some next) :
    ∃ oracleNext, machine.toOracleTM.step oracle cfg = some oracleNext ∧
      oracleNext.erase = next :=
  exists_toOracleTM_step_of_step_erase_internal machine oracle hstep

/-- Every exact-time source run lifts to an exact-time embedded oracle run;
the final configuration erases to the source result. -/
theorem exists_toOracleTM_reachesIn_of_reachesIn_erase
    (machine : TM n) (oracle : BooleanOracle)
    {time : ℕ} (start : OracleCfg n machine.Q) {result : Cfg n machine.Q}
    (hreach : machine.reachesIn time start.erase result) :
    ∃ oracleResult,
      machine.toOracleTM.reachesIn oracle time start oracleResult ∧
        oracleResult.erase = result :=
  exists_toOracleTM_reachesIn_of_reachesIn_erase_internal
    machine oracle start hreach

/-- The ordinary-machine embedding decides exactly the same timed languages,
for every supplied oracle. -/
theorem toOracleTM_decidesInTime_iff
    (machine : TM n) (oracle : BooleanOracle)
    (language : Language) (timeBound : ℕ → ℕ) :
    machine.toOracleTM.DecidesInTime oracle language timeBound ↔
      machine.DecidesInTime language timeBound :=
  toOracleTM_decidesInTime_iff_internal machine oracle language timeBound

end TM

end Complexity
