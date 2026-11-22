/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ComputationTableau
import PCP.Complexity.TM2Locality

/-!
# The finite prefix transition table of a concrete machine

For each fixed `FinTM2`, the prefix transition has finite input and output types
whose dimensions depend only on the machine. `localStep` evaluates this finite
function. `reconstruct` proves that its result, together with the unchanged input
suffixes, is the exact tableau transition. Thus no lookup table exponential in
the input-dependent space budget is needed.
-/

namespace PCP.Machine.FiniteTransitionTable

open Turing ComputationTableau TM2Locality

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

theorem decodeRow_supported {tm : FinTM2} {B : ℕ} (r : Row tm B) :
    StackSupported tm (decodeRow r).stk := by
  intro k c hc
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hc
  rw [← hi]
  exact ((r.2.2 k).2 i).property

theorem decodeRow_stack_length_le {tm : FinTM2} {B : ℕ} (r : Row tm B) (k : tm.K) :
    ((decodeRow r).stk k).length ≤ B := by
  change (List.ofFn _).length ≤ B
  rw [List.length_ofFn]
  exact Nat.le_of_lt_succ (r.2.2 k).1.isLt

theorem mass_decodeRow_le {tm : FinTM2} {B : ℕ} (r : Row tm B) :
    mass (decodeRow r).stk ≤ Fintype.card tm.K * B := by
  calc
    _ ≤ ∑ _k : tm.K, B := Finset.sum_le_sum (fun k _ => decodeRow_stack_length_le r k)
    _ = _ := by simp

/-- A fixed bound on the output prefixes, independent of the input and time budgets. -/
def outputBound (tm : FinTM2) : ℕ :=
  Fintype.card tm.K * machineWindow tm + Finset.univ.sup (fun l : tm.Λ => pushBound (tm.m l))

/-- The machine's finite prefix transition function, including its idle halting case. -/
def localStep (tm : FinTM2) (r : Row tm (machineWindow tm)) : Row tm (outputBound tm) :=
  encodeRow (keepStep tm.step (decodeRow r)) (by
    have hs := decodeRow_supported r
    cases h : tm.step (decodeRow r) with
    | none => rw [keepStep_of_none h]; exact hs
    | some c' => rw [keepStep_of_some h]; exact stackSupported_step tm h hs) (fun k => by
    have hm := mass_keepStep_le tm (decodeRow r)
    have hb := mass_decodeRow_le r
    exact (stack_length_le_mass tm _ k).trans (by
      change mass (keepStep tm.step (decodeRow r)).stk ≤
        Fintype.card tm.K * machineWindow tm + machinePushBound tm
      omega))

@[simp] theorem decode_localStep (tm : FinTM2) (r : Row tm (machineWindow tm)) :
    decodeRow (localStep tm r) = keepStep tm.step (decodeRow r) := by
  apply decode_encodeRow

/-- The inspected prefixes of any supported source configuration form one finite table input. -/
def prefixRow (tm : FinTM2) (c : tm.Cfg) (hs : StackSupported tm c.stk) :
    Row tm (machineWindow tm) :=
  encodeRow (prefixCfg tm (machineWindow tm) c) (by
    intro k a ha
    exact hs k a (List.mem_of_mem_take ha)) (fun k => by
      change ((c.stk k).take (machineWindow tm)).length ≤ machineWindow tm
      exact List.length_take_le ..)

@[simp] theorem decode_prefixRow (tm : FinTM2) (c : tm.Cfg) (hs : StackSupported tm c.stk) :
    decodeRow (prefixRow tm c hs) = prefixCfg tm (machineWindow tm) c := by
  apply decode_encodeRow

/-- Finite prefix lookup plus suffix consistency is exactly the real machine transition. -/
theorem reconstruct (tm : FinTM2) (c : tm.Cfg) (hs : StackSupported tm c.stk) :
    keepStep tm.step c =
      appendCfg (decodeRow (localStep tm (prefixRow tm c hs)))
        (fun k => (c.stk k).drop (machineWindow tm)) := by
  rw [decode_localStep, decode_prefixRow]
  exact keepStep_split tm c

/-- Both ends of the local lookup are finite, at machine-fixed dimensions. -/
theorem table_finite (tm : FinTM2) :
    Finite (Row tm (machineWindow tm) × Row tm (outputBound tm)) := by
  infer_instance

end PCP.Machine.FiniteTransitionTable
