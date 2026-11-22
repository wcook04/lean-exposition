/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BoundedEval
import PCP.Complexity.Bounds
import PCP.Complexity.Support
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option

/-!
# Polynomial-size tableaux for the concrete witness-checking machine

Rows contain the actual label, state, and supported stack symbols of a `FinTM2`.
Adjacent rows obey its terminal-preserving transition exactly. All row types are
finite, even though `FinTM2` permits infinite auxiliary alphabets: only the proved
finite symbol support is used. `NPTableau` derives uniform space and time budgets
from a concrete polynomial-time checker certificate and its witness bound.

This is the computation-tableau step of a Cook--Levin construction. The transition
constraint still compares whole rows. No bounded-arity Boolean formula, graph
reduction, or machine-time certificate for constructing such a reduction is
asserted here.
-/

namespace PCP.Machine.ComputationTableau

open Turing

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- The alphabet actually available on one stack, independent of input and running time. -/
abbrev Symbol (tm : FinTM2) (k : tm.K) := {c : tm.Γ k // Supported tm k c}

instance symbolFinite (tm : FinTM2) (k : tm.K) : Finite (Symbol tm k) :=
  (supported_finite tm k).to_subtype

/-- A supported stack of length at most the prescribed space budget. -/
abbrev Stack (tm : FinTM2) (B : ℕ) (k : tm.K) :=
  (n : Fin (B + 1)) × (Fin n.val → Symbol tm k)

/-- One finite row: control label, internal state, and all bounded supported stacks. -/
abbrev Row (tm : FinTM2) (B : ℕ) :=
  Option tm.Λ × tm.σ × ((k : tm.K) → Stack tm B k)

instance rowFinite (tm : FinTM2) (B : ℕ) : Finite (Row tm B) := by
  classical
  let (k : tm.K) : Fintype (Symbol tm k) := Fintype.ofFinite _
  exact Finite.of_fintype _

/-- Interpret a finite row as the source machine's exact configuration. -/
def decodeRow {tm : FinTM2} {B : ℕ} (r : Row tm B) : tm.Cfg :=
  ⟨r.1, r.2.1, fun k => List.ofFn (fun i => ((r.2.2 k).2 i).val)⟩

/-- Pack a supported, space-bounded source configuration into a finite row. -/
def encodeRow {tm : FinTM2} {B : ℕ} (c : tm.Cfg)
    (hs : StackSupported tm c.stk) (hb : ∀ k, (c.stk k).length ≤ B) : Row tm B :=
  ⟨c.l, c.var, fun k => ⟨⟨(c.stk k).length, Nat.lt_succ_of_le (hb k)⟩,
    fun i => ⟨(c.stk k).get i, hs k _ (List.get_mem _ _)⟩⟩⟩

@[simp] theorem decode_encodeRow {tm : FinTM2} {B : ℕ} (c : tm.Cfg)
    (hs : StackSupported tm c.stk) (hb : ∀ k, (c.stk k).length ≤ B) :
    decodeRow (encodeRow c hs hb) = c := by
  cases c
  simp [decodeRow, encodeRow]
  rfl

/-- Each row stores two control symbols and one delimiter per stack. -/
def rowSize {tm : FinTM2} {B : ℕ} (r : Row tm B) : ℕ :=
  2 + ∑ k, ((r.2.2 k).1.val + 1)

theorem rowSize_le {tm : FinTM2} {B : ℕ} (r : Row tm B) :
    rowSize r ≤ 2 + Fintype.card tm.K * (B + 1) := by
  unfold rowSize
  apply Nat.add_le_add_left
  calc
    ∑ k, ((r.2.2 k).1.val + 1) ≤ ∑ _k : tm.K, (B + 1) := by
      apply Finset.sum_le_sum
      intro k _
      have := (r.2.2 k).1.isLt
      omega
    _ = _ := by simp

theorem mass_keepStep_le (tm : FinTM2) (c : tm.Cfg) :
    mass (keepStep tm.step c).stk ≤ mass c.stk + machinePushBound tm := by
  cases h : tm.step c with
  | none => rw [keepStep_of_none h]; exact Nat.le_add_right ..
  | some c' => rw [keepStep_of_some h]; exact mass_step_le tm h

theorem mass_boundedEval_le (tm : FinTM2) (n : ℕ) (c : tm.Cfg) :
    mass (boundedEval tm n c).stk ≤ mass c.stk + machinePushBound tm * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := mass_keepStep_le tm (boundedEval tm n c)
      rw [boundedEval, Function.iterate_succ_apply']
      change mass (keepStep tm.step (boundedEval tm n c)).stk ≤ _
      calc
        _ ≤ mass (boundedEval tm n c).stk + machinePushBound tm := h
        _ ≤ (mass c.stk + machinePushBound tm * n) + machinePushBound tm := by omega
        _ = _ := by ring

theorem supported_boundedEval (tm : FinTM2) (n : ℕ) (c : tm.Cfg)
    (hs : StackSupported tm c.stk) : StackSupported tm (boundedEval tm n c).stk := by
  induction n with
  | zero => exact hs
  | succ n ih =>
      rw [boundedEval, Function.iterate_succ_apply']
      change StackSupported tm (keepStep tm.step (boundedEval tm n c)).stk
      cases h : tm.step (boundedEval tm n c) with
      | none => rw [keepStep_of_none h]; exact ih
      | some c' => rw [keepStep_of_some h]; exact stackSupported_step tm h ih

theorem stack_length_le_mass (tm : FinTM2) (c : tm.Cfg) (k : tm.K) :
    (c.stk k).length ≤ mass c.stk := by
  change (c.stk k).length ≤ ∑ j, (c.stk j).length
  exact Finset.single_le_sum (f := fun j => (c.stk j).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

/-- The finite tableau checks the initial row, every adjacent transition, and the final row. -/
def Satisfies (tm : FinTM2) (T B : ℕ) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (rows : Fin (T + 1) → Row tm B) : Prop :=
  decodeRow (rows 0) = initList tm input ∧
    (∀ i : Fin T, decodeRow (rows i.succ) = keepStep tm.step (decodeRow (rows i.castSucc))) ∧
    decodeRow (rows (Fin.last T)) = haltList tm output

/-- Adjacent transition equations determine every row of the actual computation. -/
theorem row_eq_boundedEval {tm : FinTM2} {T B : ℕ}
    {input : List (tm.Γ tm.k₀)} {output : List (tm.Γ tm.k₁)}
    {rows : Fin (T + 1) → Row tm B} (h : Satisfies tm T B input output rows)
    (i : Fin (T + 1)) : decodeRow (rows i) = boundedEval tm i.val (initList tm input) := by
  obtain ⟨j, hj⟩ := i
  induction j with
  | zero => exact h.1
  | succ j ih =>
      have hnext := h.2.1 ⟨j, by omega⟩
      have hprev := ih (by omega)
      change decodeRow (rows ⟨j + 1, hj⟩) =
        keepStep tm.step (decodeRow (rows ⟨j, by omega⟩)) at hnext
      rw [hnext, hprev]
      exact (Function.iterate_succ_apply' ..).symm

theorem satisfies_boundedEval {tm : FinTM2} {T B : ℕ}
    {input : List (tm.Γ tm.k₀)} {output : List (tm.Γ tm.k₁)}
    {rows : Fin (T + 1) → Row tm B} (h : Satisfies tm T B input output rows) :
    boundedEval tm T (initList tm input) = haltList tm output :=
  (row_eq_boundedEval h (Fin.last T)).symm.trans h.2.2

/-- The real run supplies finite rows whenever the stated space budget covers its growth. -/
def canonicalRows (tm : FinTM2) (T B : ℕ) (input : List (tm.Γ tm.k₀))
    (hb : input.length + machinePushBound tm * T ≤ B) : Fin (T + 1) → Row tm B :=
  fun i => encodeRow (boundedEval tm i.val (initList tm input))
    (supported_boundedEval tm _ _ (stackSupported_initList tm input)) (fun k => by
      have hm := mass_boundedEval_le tm i.val (initList tm input)
      rw [mass_initList] at hm
      have hi := Nat.mul_le_mul_left (machinePushBound tm) (Nat.le_of_lt_succ i.isLt)
      exact (stack_length_le_mass tm _ k).trans (by omega))

/-- Exact acceptance equivalence for a finite source-machine tableau. -/
theorem exists_satisfies_iff (tm : FinTM2) (T B : ℕ) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (hb : input.length + machinePushBound tm * T ≤ B) :
    (∃ rows, Satisfies tm T B input output rows) ↔
      boundedEval tm T (initList tm input) = haltList tm output := by
  constructor
  · rintro ⟨rows, h⟩
    exact satisfies_boundedEval h
  · intro h
    refine ⟨canonicalRows tm T B input hb, ?_, ?_, ?_⟩
    · simp [canonicalRows]
    · intro i
      simp only [canonicalRows, decode_encodeRow, Fin.val_succ, Fin.val_castSucc]
      exact Function.iterate_succ_apply' ..
    · simpa only [canonicalRows, decode_encodeRow, Fin.val_last] using h

/-- Total stored symbols, including the control symbols and stack delimiters in every row. -/
def tableauSize {tm : FinTM2} {T B : ℕ} (rows : Fin (T + 1) → Row tm B) : ℕ :=
  ∑ i, rowSize (rows i)

theorem tableauSize_le {tm : FinTM2} {T B : ℕ} (rows : Fin (T + 1) → Row tm B) :
    tableauSize rows ≤ (T + 1) * (2 + Fintype.card tm.K * (B + 1)) := by
  calc
    _ ≤ ∑ _i : Fin (T + 1), (2 + Fintype.card tm.K * (B + 1)) :=
      Finset.sum_le_sum (fun i _ => rowSize_le (rows i))
    _ = _ := by simp

end PCP.Machine.ComputationTableau
