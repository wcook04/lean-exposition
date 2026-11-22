/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.NPCellConstraints
import PCP.Complexity.TableauNumericIndex
import PCP.Reduction.FiniteDomainSource

/-!
# Machine-fixed local truth tables for the NP tableau generator

Cell-step positions saturate at the fixed output-prefix bound. Accepting-boundary
positions saturate at one, since the fixed Boolean answer occupies one symbol.
The only relation-table selector that reads input data is an initial public bit.
-/

namespace PCP.Machine.NPTableauLocalTables

open Turing ComputationTableau TM2Locality FiniteTransitionTable TableauCells TableauConstraints

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {tm : FinTM2}

/-- Every position beyond a row's fixed capacity has the same blank value. -/
theorem rowCell_cap {B : ℕ} (r : Row tm B) (k : tm.K) (j : ℕ) :
    rowCell r k j = rowCell r k (min j B) := by
  by_cases hj : j ≤ B
  · rw [min_eq_left hj]
  · have hr := (r.2.2 k).1.isLt
    have hj' : ¬j < (r.2.2 k).1.val := by omega
    have hB : ¬B < (r.2.2 k).1.val := by omega
    simp only [min_eq_right (by omega : B ≤ j), rowCell, dite_eq_right hj', dite_eq_right hB]

/-- The suffix selector is independent of the position once all fixed output prefixes end. -/
theorem predicted_cap (r : Prefix tm) (k : tm.K) (j : ℕ)
    (old : Fin (outputBound tm + 1) → Option (Symbol tm k)) :
    predicted r k j old = predicted r k (min j (outputBound tm)) old := by
  by_cases hj : j ≤ outputBound tm
  · rw [min_eq_left hj]
  · have hr := ((localStep tm r).2.2 k).1.isLt
    have hj' : ¬j < ((localStep tm r).2.2 k).1.val := by omega
    have hB : ¬outputBound tm < ((localStep tm r).2.2 k).1.val := by omega
    simp only [min_eq_right (by omega : outputBound tm ≤ j), predicted, ite_eq_right hj', ite_eq_right hB]

/-- Five fixed predicates distinguish the two public bits, separator, free bit, and blank. -/
def InputTest (kind : ℕ) (v : Option Sym) : Prop :=
  if kind = 0 then v = some (.bit false) else
  if kind = 1 then v = some (.bit true) else
  if kind = 2 then v = some .sep else
  if kind = 3 then WitnessInputCells.IsBit v else v = none

instance inputTestDecidable (kind : ℕ) (v : Option Sym) : Decidable (InputTest kind v) := by
  unfold InputTest
  split_ifs <;> infer_instance

/-- Only the public-prefix branch reads a bit of the actual input. -/
def inputKind (x : List Bool) (W j : ℕ) : ℕ :=
  if j < x.length then (x.getD j false).toNat else
  if j = x.length then 2 else if j < x.length + 1 + W then 3 else 4

theorem inputKind_lt (x : List Bool) (W j : ℕ) : inputKind x W j < 5 := by
  unfold inputKind
  split_ifs <;> try decide
  cases x.getD j false <;> decide

/-- The input-dependent initial cell predicate is selected from those five fixed cases. -/
theorem inputTest_kind (x : List Bool) (W j : ℕ) (v : Option Sym) :
    InputTest (inputKind x W j) v ↔ WitnessInputCells.Cell x W j v := by
  by_cases hj : j < x.length
  · simp only [inputKind, ite_eq_left hj, WitnessInputCells.Cell, dite_eq_left hj]
    rw [List.getD_eq_getElem _ _ hj]
    cases x[j] <;> rfl
  · simp only [inputKind, ite_eq_right hj, WitnessInputCells.Cell, dite_eq_right hj]
    by_cases he : j = x.length
    · simp only [ite_eq_left he]
      rfl
    · simp only [ite_eq_right he]
      by_cases hw : j < x.length + 1 + W
      · simp only [ite_eq_left hw]
        rfl
      · simp only [ite_eq_right hw]
        rfl

variable {R : List Bool → List Bool → Bool} (h : NPTableau.Checker R)

theorem accepting_length_one (k : h.tm.K) :
    ((haltList h.tm (NPTableau.output h true)).stk k).length ≤ 1 := by
  simp only [haltList]
  split_ifs with hk
  · subst k
    simp [NPTableau.output, encodeBool]
  · simp

/-- One machine-fixed accepting row supplies every terminal table entry. -/
def finalOne (hs : StackSupported h.tm (haltList h.tm (NPTableau.output h true)).stk) :
    Row h.tm 1 := NPCellConstraints.finalRow h 1 hs (accepting_length_one h)

/-- The growing tableau's accepting boundary is exactly that fixed row, with capped positions. -/
theorem finalCell_cap (hs : StackSupported h.tm (haltList h.tm (NPTableau.output h true)).stk)
    {B : ℕ} (hb : ∀ k, ((haltList h.tm (NPTableau.output h true)).stk k).length ≤ B)
    (k : h.tm.K) (j : ℕ) :
    rowCell (NPCellConstraints.finalRow h B hs hb) k j = rowCell (finalOne h hs) k (min j 1) := by
  have heq : rowCell (NPCellConstraints.finalRow h B hs hb) k j = rowCell (finalOne h hs) k j := by
    apply (Option.map_injective Subtype.val_injective)
    rw [map_rowCell, map_rowCell]
    simp only [finalOne, NPCellConstraints.decode_finalRow]
  exact heq.trans (rowCell_cap (finalOne h hs) k j)

end PCP.Machine.NPTableauLocalTables
