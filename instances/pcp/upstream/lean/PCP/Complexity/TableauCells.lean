/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.FiniteTransitionTable

/-!
# Bounded-window constraints on individual tableau cells

A row stores a machine-fixed prefix value and one optional supported symbol at
each stack position. A transition cell reads the old prefix, its new cell, and
one candidate old cell for each possible output-prefix length. Consequently the
number of values inspected is fixed by the machine, independently of the space
and time budgets. The exact source-machine growth bound prevents truncation from
creating a spurious accepting computation.
-/

namespace PCP.Machine.TableauCells

open Turing ComputationTableau TM2Locality FiniteTransitionTable

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

abbrev Prefix (tm : FinTM2) := Row tm (machineWindow tm)

/-- Padded, individually addressable stack cells; no whole stack is a variable. -/
abbrev Cells (tm : FinTM2) (B : ℕ) := (k : tm.K) → Fin B → Option (Symbol tm k)

instance cellsFinite (tm : FinTM2) (B : ℕ) : Finite (Cells tm B) := by
  classical
  let (k : tm.K) : Fintype (Symbol tm k) := Fintype.ofFinite _
  exact Finite.of_fintype _

/-- Outside the declared space bound every cell is the fixed blank value. -/
def readCell {tm : FinTM2} {B : ℕ} (s : Cells tm B) (k : tm.K) (j : ℕ) :
    Option (tm.Γ k) :=
  if h : j < B then (s k ⟨j, h⟩).map Subtype.val else none

@[simp] theorem readCell_of_lt {tm : FinTM2} {B : ℕ} (s : Cells tm B)
    (k : tm.K) (j : Fin B) :
    readCell s k j.val = (s k j).map Subtype.val := by
  simp [readCell]

@[simp] theorem readCell_of_ge {tm : FinTM2} {B : ℕ} (s : Cells tm B)
    (k : tm.K) (j : ℕ) (h : B ≤ j) : readCell s k j = none := by
  simp [readCell, Nat.not_lt.mpr h]

/-- Pack the actual supported symbols, filling unused positions by `none`. -/
def encodeCells {tm : FinTM2} (B : ℕ) (c : tm.Cfg)
    (hs : StackSupported tm c.stk) : Cells tm B :=
  fun k j => if h : j.val < (c.stk k).length then
    some ⟨(c.stk k)[j.val], hs k _ (List.getElem_mem h)⟩ else none

@[simp] theorem read_encodeCells {tm : FinTM2} {B : ℕ} (c : tm.Cfg)
    (hs : StackSupported tm c.stk) (hb : ∀ k, (c.stk k).length ≤ B)
    (k : tm.K) (j : ℕ) : readCell (encodeCells B c hs) k j = (c.stk k)[j]? := by
  by_cases hj : j < B
  · by_cases hc : j < (c.stk k).length
    · simp [readCell, encodeCells, hj, hc]
    · rw [List.getElem?_eq_none (Nat.le_of_not_gt hc)]
      simp [readCell, encodeCells, hj, hc]
  · rw [List.getElem?_eq_none ((hb k).trans (Nat.le_of_not_gt hj))]
    simp [readCell, hj]

/-- The semantic interpretation used only in the correctness proof. -/
def Represents {tm : FinTM2} {B : ℕ} (p : Prefix tm) (s : Cells tm B)
    (c : tm.Cfg) : Prop :=
  (decodeRow p).l = c.l ∧ (decodeRow p).var = c.var ∧
    ∀ k j, readCell s k j = (c.stk k)[j]?

/-- A boundary check reads the control value and each single cell. -/
def Boundary {tm : FinTM2} {B : ℕ} (p : Prefix tm) (s : Cells tm B)
    (c : tm.Cfg) : Prop :=
  (decodeRow p).l = c.l ∧ (decodeRow p).var = c.var ∧
    ∀ k (j : Fin B), readCell s k j.val = (c.stk k)[j.val]?

theorem represents_boundary {tm : FinTM2} {B : ℕ} {p : Prefix tm} {s : Cells tm B}
    {c : tm.Cfg} (h : Represents p s c) : Boundary p s c :=
  ⟨h.1, h.2.1, fun k j => h.2.2 k j.val⟩

theorem boundary_represents {tm : FinTM2} {B : ℕ} {p : Prefix tm} {s : Cells tm B}
    {c : tm.Cfg} (h : Boundary p s c) (hb : ∀ k, (c.stk k).length ≤ B) :
    Represents p s c := by
  refine ⟨h.1, h.2.1, fun k j => ?_⟩
  by_cases hj : j < B
  · exact h.2.2 k ⟨j, hj⟩
  · rw [readCell_of_ge s k j (by omega), List.getElem?_eq_none (by have := hb k; omega)]

/-- Each prefix position is linked to its corresponding individual stack cell. -/
def Linked {tm : FinTM2} {B : ℕ} (p : Prefix tm) (s : Cells tm B) : Prop :=
  ∀ k (i : Fin (machineWindow tm)), ((decodeRow p).stk k)[i.val]? = readCell s k i.val

private theorem cfg_ext {tm : FinTM2} {c d : tm.Cfg}
    (hl : c.l = d.l) (hv : c.var = d.var) (hs : c.stk = d.stk) : c = d := by
  cases c
  cases d
  cases hl
  cases hv
  cases hs
  rfl

theorem linked_prefix {tm : FinTM2} {B : ℕ} {p : Prefix tm} {s : Cells tm B}
    {c : tm.Cfg} (hr : Represents p s c) (hl : Linked p s) :
    decodeRow p = prefixCfg tm (machineWindow tm) c := by
  apply cfg_ext (d := prefixCfg tm (machineWindow tm) c) hr.1 hr.2.1
  funext k
  apply List.ext_getElem?
  intro j
  change ((decodeRow p).stk k)[j]? = ((c.stk k).take (machineWindow tm))[j]?
  rw [List.getElem?_take]
  by_cases hj : j < machineWindow tm
  · rw [ite_eq_left hj, hl k ⟨j, hj⟩, hr.2.2]
  · rw [ite_eq_right hj]
    exact List.getElem?_eq_none (by have := decodeRow_stack_length_le p k; omega)

/-- All possible old suffix addresses of one new cell, one per output-prefix length. -/
def candidates {tm : FinTM2} {B : ℕ} (s : Cells tm B) (k : tm.K) (j : ℕ) :
    Fin (outputBound tm + 1) → Option (tm.Γ k) :=
  fun n => readCell s k (machineWindow tm + (j - n.val))

/-- The finite transition table chooses one of the machine-fixed suffix candidates. -/
def predictedCell {tm : FinTM2} (p : Prefix tm) (k : tm.K) (j : ℕ)
    (old : Fin (outputBound tm + 1) → Option (tm.Γ k)) : Option (tm.Γ k) :=
  let r := localStep tm p
  if j < (r.2.2 k).1.val then ((decodeRow r).stk k)[j]? else old (r.2.2 k).1

theorem predictedCell_eq {tm : FinTM2} {B : ℕ} (p : Prefix tm) (s : Cells tm B)
    (k : tm.K) (j : ℕ) :
    predictedCell p k j (candidates s k j) =
      if j < ((decodeRow (localStep tm p)).stk k).length then
        ((decodeRow (localStep tm p)).stk k)[j]? else
        readCell s k (machineWindow tm + (j - ((decodeRow (localStep tm p)).stk k).length)) := by
  simp [predictedCell, candidates, decodeRow]

/-- One adjacency check has separate control checks and one bounded-width check per cell. -/
def Step {tm : FinTM2} {B : ℕ} (p p' : Prefix tm) (s s' : Cells tm B) : Prop :=
  (decodeRow p').l = (decodeRow (localStep tm p)).l ∧
    (decodeRow p').var = (decodeRow (localStep tm p)).var ∧
    ∀ k (j : Fin B), readCell s' k j.val = predictedCell p k j.val (candidates s k j.val)

theorem predictedCell_step {tm : FinTM2} {B : ℕ} {p : Prefix tm} {s : Cells tm B}
    {c : tm.Cfg} (hr : Represents p s c) (hl : Linked p s) (k : tm.K) (j : ℕ) :
    predictedCell p k j (candidates s k j) = ((keepStep tm.step c).stk k)[j]? := by
  rw [predictedCell_eq]
  have hp := linked_prefix hr hl
  have hd : decodeRow (localStep tm p) = keepStep tm.step (prefixCfg tm (machineWindow tm) c) := by
    rw [decode_localStep, hp]
  rw [keepStep_split tm c]
  change _ = ((keepStep tm.step (prefixCfg tm (machineWindow tm) c)).stk k ++
    (c.stk k).drop (machineWindow tm))[j]?
  rw [List.getElem?_append, List.getElem?_drop, hd, hr.2.2]

/-- A satisfying local transition represents the exact source successor. -/
theorem step_represents {tm : FinTM2} {B : ℕ} {p p' : Prefix tm} {s s' : Cells tm B}
    {c : tm.Cfg} (hr : Represents p s c) (hl : Linked p s) (hst : Step p p' s s')
    (hb : ∀ k, ((keepStep tm.step c).stk k).length ≤ B) :
    Represents p' s' (keepStep tm.step c) := by
  have hp := linked_prefix hr hl
  have hd : decodeRow (localStep tm p) = keepStep tm.step (prefixCfg tm (machineWindow tm) c) := by
    rw [decode_localStep, hp]
  apply boundary_represents (hb := hb)
  refine ⟨?_, ?_, fun k j => ?_⟩
  · rw [hst.1, hd, keepStep_split tm c]
    rfl
  · rw [hst.2.1, hd, keepStep_split tm c]
    rfl
  · rw [hst.2.2, predictedCell_step hr hl]


/-- The same control value and all padded cells determine a represented configuration. -/
theorem represents_unique {tm : FinTM2} {B : ℕ} {p : Prefix tm} {s : Cells tm B}
    {c d : tm.Cfg} (hc : Represents p s c) (hd : Represents p s d) : c = d := by
  apply cfg_ext (hc.1.symm.trans hd.1) (hc.2.1.symm.trans hd.2.1)
  funext k
  apply List.ext_getElem?
  intro j
  exact (hc.2.2 k j).symm.trans (hd.2.2 k j)

theorem represents_encode {tm : FinTM2} {B : ℕ} (c : tm.Cfg)
    (hs : StackSupported tm c.stk) (hb : ∀ k, (c.stk k).length ≤ B) :
    Represents (prefixRow tm c hs) (encodeCells B c hs) c := by
  refine ⟨?_, ?_, read_encodeCells c hs hb⟩
  · simp
    rfl
  · simp
    rfl

theorem linked_encode {tm : FinTM2} {B : ℕ} (c : tm.Cfg)
    (hs : StackSupported tm c.stk) (hb : ∀ k, (c.stk k).length ≤ B) :
    Linked (prefixRow tm c hs) (encodeCells B c hs) := by
  intro k i
  rw [decode_prefixRow, read_encodeCells c hs hb]
  change ((c.stk k).take (machineWindow tm))[i.val]? = (c.stk k)[i.val]?
  rw [List.getElem?_take, ite_eq_left i.isLt]

theorem step_of_represents {tm : FinTM2} {B : ℕ} {p p' : Prefix tm} {s s' : Cells tm B}
    {c : tm.Cfg} (hr : Represents p s c) (hl : Linked p s)
    (hr' : Represents p' s' (keepStep tm.step c)) : Step p p' s s' := by
  have hp := linked_prefix hr hl
  have hd : decodeRow (localStep tm p) = keepStep tm.step (prefixCfg tm (machineWindow tm) c) := by
    rw [decode_localStep, hp]
  refine ⟨?_, ?_, fun k j => ?_⟩
  · rw [hr'.1, hd, keepStep_split tm c]
    rfl
  · rw [hr'.2.1, hd, keepStep_split tm c]
    rfl
  · rw [hr'.2.2, predictedCell_step hr hl]

/-- Only the prefix variable has a compound alphabet; its size depends solely on the machine. -/
abbrev Assignment (tm : FinTM2) (T B : ℕ) :=
  (Fin (T + 1) → Prefix tm) × (Fin (T + 1) → Cells tm B)

instance assignmentFinite (tm : FinTM2) (T B : ℕ) : Finite (Assignment tm T B) := by
  infer_instance

/-- All constraints are unary, binary, or the fixed-width individual transition checks. -/
def Satisfies (tm : FinTM2) (T B : ℕ) (initial final : tm.Cfg)
    (a : Assignment tm T B) : Prop :=
  Boundary (a.1 0) (a.2 0) initial ∧
    (∀ i, Linked (a.1 i) (a.2 i)) ∧
    (∀ i : Fin T, Step (a.1 i.castSucc) (a.1 i.succ) (a.2 i.castSucc) (a.2 i.succ)) ∧
    Boundary (a.1 (Fin.last T)) (a.2 (Fin.last T)) final

/-- The uniform space budget is derived from the proved source-machine growth bound. -/
theorem run_length_le {tm : FinTM2} {T B : ℕ} {initial : tm.Cfg}
    (hb : mass initial.stk + machinePushBound tm * T ≤ B)
    (i : Fin (T + 1)) (k : tm.K) :
    ((boundedEval tm i.val initial).stk k).length ≤ B := by
  have hm := mass_boundedEval_le tm i.val initial
  have hi := Nat.mul_le_mul_left (machinePushBound tm) (Nat.le_of_lt_succ i.isLt)
  exact (stack_length_le_mass tm _ k).trans (by omega)

/-- The local constraints force every cell and control value to equal the true computation. -/
theorem satisfies_represents {tm : FinTM2} {T B : ℕ} {initial final : tm.Cfg}
    {a : Assignment tm T B} (h : Satisfies tm T B initial final a)
    (hb : mass initial.stk + machinePushBound tm * T ≤ B) (i : Fin (T + 1)) :
    Represents (a.1 i) (a.2 i) (boundedEval tm i.val initial) := by
  obtain ⟨j, hj⟩ := i
  induction j with
  | zero =>
      apply boundary_represents h.1
      exact run_length_le hb 0
  | succ j ih =>
      have hprev := ih (by omega)
      have hnext := h.2.2.1 ⟨j, by omega⟩
      change Step (a.1 ⟨j, by omega⟩) (a.1 ⟨j + 1, hj⟩)
        (a.2 ⟨j, by omega⟩) (a.2 ⟨j + 1, hj⟩) at hnext
      have heq : boundedEval tm (j + 1) initial = keepStep tm.step (boundedEval tm j initial) :=
        Function.iterate_succ_apply' ..
      rw [heq]
      apply step_represents hprev (h.2.1 _) hnext
      rw [← heq]
      exact run_length_le hb ⟨j + 1, hj⟩

/-- No truncation can create acceptance: both real and required terminal stacks fit the budget. -/
theorem satisfies_boundedEval {tm : FinTM2} {T B : ℕ} {initial final : tm.Cfg}
    {a : Assignment tm T B} (h : Satisfies tm T B initial final a)
    (hb : mass initial.stk + machinePushBound tm * T ≤ B)
    (hf : ∀ k, (final.stk k).length ≤ B) : boundedEval tm T initial = final := by
  exact represents_unique (satisfies_represents h hb (Fin.last T))
    (boundary_represents h.2.2.2 hf)

/-- The actual execution supplies every prefix and every individual cell. -/
def canonicalAssignment (tm : FinTM2) (T B : ℕ) (initial : tm.Cfg)
    (hs : StackSupported tm initial.stk) : Assignment tm T B :=
  ⟨fun i => prefixRow tm (boundedEval tm i.val initial) (supported_boundedEval tm _ _ hs),
    fun i => encodeCells B (boundedEval tm i.val initial) (supported_boundedEval tm _ _ hs)⟩

theorem canonical_represents {tm : FinTM2} {T B : ℕ} (initial : tm.Cfg)
    (hs : StackSupported tm initial.stk)
    (hb : mass initial.stk + machinePushBound tm * T ≤ B) (i : Fin (T + 1)) :
    Represents ((canonicalAssignment tm T B initial hs).1 i)
      ((canonicalAssignment tm T B initial hs).2 i) (boundedEval tm i.val initial) :=
  represents_encode _ (supported_boundedEval tm _ _ hs) (run_length_le hb i)

theorem canonical_linked {tm : FinTM2} {T B : ℕ} (initial : tm.Cfg)
    (hs : StackSupported tm initial.stk)
    (hb : mass initial.stk + machinePushBound tm * T ≤ B) (i : Fin (T + 1)) :
    Linked ((canonicalAssignment tm T B initial hs).1 i)
      ((canonicalAssignment tm T B initial hs).2 i) :=
  linked_encode _ (supported_boundedEval tm _ _ hs) (run_length_le hb i)

/-- Exact finite-cell characterization of the concrete bounded source computation. -/
theorem exists_satisfies_iff (tm : FinTM2) (T B : ℕ) (initial final : tm.Cfg)
    (hs : StackSupported tm initial.stk)
    (hb : mass initial.stk + machinePushBound tm * T ≤ B)
    (hf : ∀ k, (final.stk k).length ≤ B) :
    (∃ a, Satisfies tm T B initial final a) ↔ boundedEval tm T initial = final := by
  constructor
  · rintro ⟨a, ha⟩
    exact satisfies_boundedEval ha hb hf
  · intro he
    refine ⟨canonicalAssignment tm T B initial hs, ?_, canonical_linked initial hs hb, ?_, ?_⟩
    · exact represents_boundary (canonical_represents initial hs hb 0)
    · intro i
      apply step_of_represents (canonical_represents initial hs hb i.castSucc)
        (canonical_linked initial hs hb i.castSucc)
      have h := canonical_represents initial hs hb i.succ
      change Represents _ _ (boundedEval tm (i.val + 1) initial) at h
      rw [show boundedEval tm (i.val + 1) initial =
        keepStep tm.step (boundedEval tm i.val initial) from Function.iterate_succ_apply' ..] at h
      exact h
    · have h := represents_boundary (canonical_represents initial hs hb (Fin.last T))
      simpa only [Fin.val_last, he] using h

/-- Number of actual finite-alphabet variables, including the fixed-size prefix variable. -/
def variableCount (tm : FinTM2) (T B : ℕ) : ℕ :=
  (T + 1) * (1 + Fintype.card tm.K * B)

/-- A transition cell reads one prefix, one new cell, and the finite candidate old cells. -/
def transitionWidth (tm : FinTM2) : ℕ := outputBound tm + 3

end PCP.Machine.TableauCells
