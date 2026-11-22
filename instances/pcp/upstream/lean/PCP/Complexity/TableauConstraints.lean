/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.TableauCells

/-!
# Fixed-arity finite-alphabet constraints for concrete machine tableaux

Every variable has one common finite alphabet depending only on the machine.
A cell variable uses just one of its optional-symbol components. The extra
components let all scopes have the same alphabet without partial casts. Variable
and constraint indices are explicit sums and products of time, stack, and
position indices; there is no input-sized chosen enumeration.
-/

namespace PCP.Machine.TableauConstraints

open Turing ComputationTableau TM2Locality FiniteTransitionTable TableauCells

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- A common, machine-fixed alphabet for both control-prefix and individual cell variables. -/
abbrev Alphabet (tm : FinTM2) := Prefix tm × ((k : tm.K) → Option (Symbol tm k))

instance alphabetFinite (tm : FinTM2) : Finite (Alphabet tm) := by
  classical
  let (k : tm.K) : Fintype (Symbol tm k) := Fintype.ofFinite _
  exact Finite.of_fintype _

abbrev Site (tm : FinTM2) (B : ℕ) := Unit ⊕ (tm.K × Fin B)

/-- The final summand is one blank variable used for out-of-range stack addresses. -/
abbrev Variable (tm : FinTM2) (T B : ℕ) := (Fin (T + 1) × Site tm B) ⊕ Unit

/-- Blank, prefix links, control steps, cell steps, and the two boundaries. -/
abbrev Constraint (tm : FinTM2) (T B : ℕ) := Unit ⊕
  ((Fin (T + 1) × tm.K × Fin (machineWindow tm)) ⊕
  (Fin T ⊕ ((Fin T × tm.K × Fin B) ⊕ (Bool × Site tm B))))

/-- This arity is constant for every input of a fixed machine. -/
abbrev arity (tm : FinTM2) := transitionWidth tm

def prefixVariable {tm : FinTM2} {T B : ℕ} (t : Fin (T + 1)) : Variable tm T B :=
  .inl (t, .inl ())

def cellVariable {tm : FinTM2} {T B : ℕ} (t : Fin (T + 1)) (k : tm.K) (j : ℕ) :
    Variable tm T B :=
  if h : j < B then .inl (t, .inr (k, ⟨j, h⟩)) else .inr ()

def boundaryTime {T : ℕ} (b : Bool) : Fin (T + 1) := if b then Fin.last T else 0

def candidateSlot {tm : FinTM2} (n : Fin (outputBound tm + 1)) : Fin (arity tm) :=
  ⟨n.val + 2, by have := n.isLt; simp only [arity, transitionWidth]; omega⟩

def firstSlot (tm : FinTM2) : Fin (arity tm) := ⟨0, by simp [arity, transitionWidth]⟩

def secondSlot (tm : FinTM2) : Fin (arity tm) := ⟨1, by simp [arity, transitionWidth]⟩

/-- Read one optional supported symbol from a finite row. -/
def rowCell {tm : FinTM2} {B : ℕ} (r : Row tm B) (k : tm.K) (j : ℕ) :
    Option (Symbol tm k) :=
  if h : j < (r.2.2 k).1.val then some ((r.2.2 k).2 ⟨j, h⟩) else none

@[simp] theorem map_rowCell {tm : FinTM2} {B : ℕ} (r : Row tm B) (k : tm.K) (j : ℕ) :
    (rowCell r k j).map Subtype.val = ((decodeRow r).stk k)[j]? := by
  simp only [rowCell, decodeRow, List.getElem?_ofFn]
  split <;> simp

/-- Supported-symbol version of the machine's finite prefix/suffix selector. -/
def predicted {tm : FinTM2} (p : Prefix tm) (k : tm.K) (j : ℕ)
    (old : Fin (outputBound tm + 1) → Option (Symbol tm k)) : Option (Symbol tm k) :=
  let r := localStep tm p
  if j < (r.2.2 k).1.val then rowCell r k j else old (r.2.2 k).1

@[simp] theorem map_predicted {tm : FinTM2} (p : Prefix tm) (k : tm.K) (j : ℕ)
    (old : Fin (outputBound tm + 1) → Option (Symbol tm k)) :
    (predicted p k j old).map Subtype.val =
      predictedCell p k j (fun n => (old n).map Subtype.val) := by
  simp only [predicted, predictedCell]
  split
  · exact map_rowCell _ _ _
  · rfl

/-- The scope gives every local test its actual variables, padding unused slots by blank. -/
def scope {tm : FinTM2} {T B : ℕ} : Constraint tm T B → Fin (arity tm) → Variable tm T B
  | .inl _, _ => .inr ()
  | .inr (.inl (t, k, j)), i =>
      if i.val = 0 then prefixVariable t else cellVariable t k j.val
  | .inr (.inr (.inl t)), i =>
      if i.val = 0 then prefixVariable t.castSucc else prefixVariable t.succ
  | .inr (.inr (.inr (.inl (t, k, j)))), i =>
      if i.val = 0 then prefixVariable t.castSucc else
      if i.val = 1 then cellVariable t.succ k j.val else
      cellVariable t.castSucc k (machineWindow tm + (j.val - (i.val - 2)))
  | .inr (.inr (.inr (.inr (b, .inl _)))), _ => prefixVariable (boundaryTime b)
  | .inr (.inr (.inr (.inr (b, .inr (k, j))))), _ =>
      cellVariable (boundaryTime b) k j.val

/-- The fixed-width predicate assigned to each arithmetic constraint index. -/
def Relation {tm : FinTM2} {T B : ℕ} (initial final : Row tm B) :
    Constraint tm T B → (Fin (arity tm) → Alphabet tm) → Prop
  | .inl _, v => ∀ k, (v (firstSlot tm)).2 k = none
  | .inr (.inl (_, k, j)), v =>
      rowCell (v (firstSlot tm)).1 k j.val = (v (secondSlot tm)).2 k
  | .inr (.inr (.inl _)), v =>
      (v (secondSlot tm)).1.1 = (localStep tm (v (firstSlot tm)).1).1 ∧
      (v (secondSlot tm)).1.2.1 = (localStep tm (v (firstSlot tm)).1).2.1
  | .inr (.inr (.inr (.inl (_, k, j)))), v =>
      (v (secondSlot tm)).2 k =
        predicted (v (firstSlot tm)).1 k j.val (fun n => (v (candidateSlot n)).2 k)
  | .inr (.inr (.inr (.inr (b, .inl _)))), v =>
      (v (firstSlot tm)).1.1 = (if b then final else initial).1 ∧
      (v (firstSlot tm)).1.2.1 = (if b then final else initial).2.1
  | .inr (.inr (.inr (.inr (b, .inr (k, j))))), v =>
      (v (firstSlot tm)).2 k = rowCell (if b then final else initial) k j.val

/-- Actual satisfaction of all fixed-width scopes. -/
def Holds {tm : FinTM2} {T B : ℕ} (initial final : Row tm B)
    (x : Variable tm T B → Alphabet tm) : Prop :=
  ∀ e, Relation initial final e (fun i => x (scope e i))

/-- Recover the intended prefix and one optional symbol from each variable. -/
def decodeAssignment {tm : FinTM2} {T B : ℕ} (x : Variable tm T B → Alphabet tm) :
    Assignment tm T B :=
  ⟨fun t => (x (prefixVariable t)).1,
    fun t k j => (x (.inl (t, .inr (k, j)))).2 k⟩

/-- Unused alphabet components are filled from the row's prefix or padded by blank. -/
def encodeAssignment {tm : FinTM2} {T B : ℕ} (a : Assignment tm T B) :
    Variable tm T B → Alphabet tm
  | .inl (t, .inl _) => (a.1 t, fun _ => none)
  | .inl (t, .inr (_, j)) => (a.1 t, fun k => a.2 t k j)
  | .inr _ => (a.1 0, fun _ => none)

@[simp] theorem decode_encodeAssignment {tm : FinTM2} {T B : ℕ} (a : Assignment tm T B) :
    decodeAssignment (encodeAssignment a) = a := by
  cases a
  rfl

@[simp] theorem map_cellVariable {tm : FinTM2} {T B : ℕ}
    (x : Variable tm T B → Alphabet tm) (h : ∀ k, (x (.inr ())).2 k = none)
    (t : Fin (T + 1)) (k : tm.K) (j : ℕ) :
    ((x (cellVariable t k j)).2 k).map Subtype.val =
      readCell ((decodeAssignment x).2 t) k j := by
  by_cases hj : j < B
  · simp [cellVariable, readCell, hj, decodeAssignment]
  · simp [cellVariable, readCell, hj, h]

@[simp] theorem map_encoded_cellVariable {tm : FinTM2} {T B : ℕ}
    (a : Assignment tm T B) (t : Fin (T + 1)) (k : tm.K) (j : ℕ) :
    (((encodeAssignment a) (cellVariable t k j)).2 k).map Subtype.val =
      readCell (a.2 t) k j := by
  simpa using map_cellVariable (encodeAssignment a) (fun _ => rfl) t k j


private theorem symbol_eq_iff {tm : FinTM2} {k : tm.K} (u v : Option (Symbol tm k)) :
    u = v ↔ u.map Subtype.val = v.map Subtype.val :=
  ⟨congrArg _, fun h => (Option.map_injective Subtype.val_injective) h⟩

@[simp] theorem scope_candidate {tm : FinTM2} {T B : ℕ} (t : Fin T) (k : tm.K)
    (j : Fin B) (n : Fin (outputBound tm + 1)) :
    scope (.inr (.inr (.inr (.inl (t, k, j)))) : Constraint tm T B) (candidateSlot n) =
      cellVariable t.castSucc k (machineWindow tm + (j.val - n.val)) := by
  simp [scope, candidateSlot, show n.val + 2 ≠ 1 by omega]

theorem relation_link_iff {tm : FinTM2} {T B : ℕ} (initial final : Row tm B)
    (x : Variable tm T B → Alphabet tm) (h : ∀ k, (x (.inr ())).2 k = none)
    (t : Fin (T + 1)) (k : tm.K) (j : Fin (machineWindow tm)) :
    Relation initial final (.inr (.inl (t, k, j))) (fun i => x (scope (.inr (.inl (t, k, j))) i)) ↔
      (((decodeRow ((decodeAssignment x).1 t)).stk k)[j.val]? =
        readCell ((decodeAssignment x).2 t) k j.val) := by
  change rowCell (x (prefixVariable t)).1 k j.val = (x (cellVariable t k j.val)).2 k ↔ _
  rw [symbol_eq_iff, map_rowCell, map_cellVariable x h]
  rfl

theorem relation_control_iff {tm : FinTM2} {T B : ℕ} (initial final : Row tm B)
    (x : Variable tm T B → Alphabet tm) (t : Fin T) :
    Relation initial final (.inr (.inr (.inl t)))
      (fun i => x (scope (.inr (.inr (.inl t))) i)) ↔
      ((decodeRow ((decodeAssignment x).1 t.succ)).l =
        (decodeRow (localStep tm ((decodeAssignment x).1 t.castSucc))).l ∧
      (decodeRow ((decodeAssignment x).1 t.succ)).var =
        (decodeRow (localStep tm ((decodeAssignment x).1 t.castSucc))).var) := Iff.rfl

theorem relation_step_iff {tm : FinTM2} {T B : ℕ} (initial final : Row tm B)
    (x : Variable tm T B → Alphabet tm) (h : ∀ k, (x (.inr ())).2 k = none)
    (t : Fin T) (k : tm.K) (j : Fin B) :
    Relation initial final (.inr (.inr (.inr (.inl (t, k, j)))))
      (fun i => x (scope (.inr (.inr (.inr (.inl (t, k, j))))) i)) ↔
      (readCell ((decodeAssignment x).2 t.succ) k j.val =
        predictedCell ((decodeAssignment x).1 t.castSucc) k j.val
          (candidates ((decodeAssignment x).2 t.castSucc) k j.val)) := by
  change (x (cellVariable t.succ k j.val)).2 k =
    predicted (x (prefixVariable t.castSucc)).1 k j.val
      (fun n => (x (scope (.inr (.inr (.inr (.inl (t, k, j))))) (candidateSlot n))).2 k) ↔ _
  rw [symbol_eq_iff, map_predicted, map_cellVariable x h]
  simp only [scope_candidate, map_cellVariable x h]
  rfl

theorem relation_boundary_control_iff {tm : FinTM2} {T B : ℕ} (initial final : Row tm B)
    (x : Variable tm T B → Alphabet tm) (b : Bool) :
    Relation (T := T) initial final (.inr (.inr (.inr (.inr (b, .inl ())))))
      (fun i => x (scope (.inr (.inr (.inr (.inr (b, .inl ()))))) i)) ↔
      ((decodeRow ((decodeAssignment x).1 (boundaryTime b))).l =
        (decodeRow (if b then final else initial)).l ∧
      (decodeRow ((decodeAssignment x).1 (boundaryTime b))).var =
        (decodeRow (if b then final else initial)).var) := Iff.rfl

theorem relation_boundary_cell_iff {tm : FinTM2} {T B : ℕ} (initial final : Row tm B)
    (x : Variable tm T B → Alphabet tm) (h : ∀ k, (x (.inr ())).2 k = none)
    (b : Bool) (k : tm.K) (j : Fin B) :
    Relation (T := T) initial final (.inr (.inr (.inr (.inr (b, .inr (k, j))))))
      (fun i => x (scope (.inr (.inr (.inr (.inr (b, .inr (k, j)))))) i)) ↔
      (readCell ((decodeAssignment x).2 (boundaryTime b)) k j.val =
        ((decodeRow (if b then final else initial)).stk k)[j.val]?) := by
  change (x (cellVariable (boundaryTime b) k j.val)).2 k =
    rowCell (if b then final else initial) k j.val ↔ _
  rw [symbol_eq_iff, map_rowCell, map_cellVariable x h]

/-- The explicit scopes and local lookup predicates are exactly the cell tableau checks. -/
theorem holds_iff {tm : FinTM2} {T B : ℕ} (initial final : Row tm B)
    (x : Variable tm T B → Alphabet tm) :
    Holds initial final x ↔ (∀ k, (x (.inr ())).2 k = none) ∧
      TableauCells.Satisfies tm T B (decodeRow initial) (decodeRow final) (decodeAssignment x) := by
  constructor
  · intro hx
    have hz : ∀ k, (x (.inr ())).2 k = none := hx (.inl ())
    refine ⟨hz, ?_, ?_, ?_, ?_⟩
    · have hc := (relation_boundary_control_iff initial final x false).mp
        (hx (.inr (.inr (.inr (.inr (false, .inl ()))))))
      refine ⟨hc.1, hc.2, fun k j => ?_⟩
      exact (relation_boundary_cell_iff initial final x hz false k j).mp (hx _)
    · intro t k j
      exact (relation_link_iff initial final x hz t k j).mp (hx _)
    · intro t
      have hc := (relation_control_iff initial final x t).mp (hx _)
      refine ⟨hc.1, hc.2, fun k j => ?_⟩
      exact (relation_step_iff initial final x hz t k j).mp (hx _)
    · have hc := (relation_boundary_control_iff initial final x true).mp
        (hx (.inr (.inr (.inr (.inr (true, .inl ()))))))
      refine ⟨hc.1, hc.2, fun k j => ?_⟩
      exact (relation_boundary_cell_iff initial final x hz true k j).mp (hx _)
  · rintro ⟨hz, hi, hl, ht, hf⟩ e
    rcases e with _ | ⟨t, k, j⟩ | t | ⟨t, k, j⟩ | ⟨b, _ | ⟨k, j⟩⟩
    · exact hz
    · exact (relation_link_iff initial final x hz t k j).mpr (hl t k j)
    · exact (relation_control_iff initial final x t).mpr ⟨(ht t).1, (ht t).2.1⟩
    · exact (relation_step_iff initial final x hz t k j).mpr ((ht t).2.2 k j)
    · apply (relation_boundary_control_iff initial final x b).mpr
      cases b
      · exact ⟨hi.1, hi.2.1⟩
      · exact ⟨hf.1, hf.2.1⟩
    · apply (relation_boundary_cell_iff initial final x hz b k j).mpr
      cases b
      · exact hi.2.2 k j
      · exact hf.2.2 k j

/-- Satisfiability is preserved with a common machine-fixed finite alphabet. -/
theorem satisfiable_iff {tm : FinTM2} {T B : ℕ} (initial final : Row tm B) :
    (∃ x, Holds (T := T) initial final x) ↔
      ∃ a, TableauCells.Satisfies tm T B (decodeRow initial) (decodeRow final) a := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨decodeAssignment x, ((holds_iff initial final x).mp hx).2⟩
  · rintro ⟨a, ha⟩
    refine ⟨encodeAssignment a, (holds_iff initial final _).mpr ⟨fun _ => rfl, ?_⟩⟩
    simpa using ha

/-- Unconditional correctness for the concrete source machine under its proved growth bound. -/
theorem satisfiable_boundedEval_iff {tm : FinTM2} {T B : ℕ} (initial final : Row tm B)
    (hb : mass (decodeRow initial).stk + machinePushBound tm * T ≤ B) :
    (∃ x, Holds (T := T) initial final x) ↔
      boundedEval tm T (decodeRow initial) = decodeRow final := by
  rw [satisfiable_iff]
  exact TableauCells.exists_satisfies_iff tm T B _ _ (decodeRow_supported initial) hb
    (decodeRow_stack_length_le final)

theorem card_variable (tm : FinTM2) (T B : ℕ) :
    Fintype.card (Variable tm T B) = (T + 1) * (1 + Fintype.card tm.K * B) + 1 := by
  simp [Variable, Site]

theorem card_constraint (tm : FinTM2) (T B : ℕ) :
    Fintype.card (Constraint tm T B) = 1 + (T + 1) * (Fintype.card tm.K * machineWindow tm) +
      T + T * (Fintype.card tm.K * B) + 2 * (1 + Fintype.card tm.K * B) := by
  simp [Constraint, Site]
  ring


section Decidable

variable {tm : FinTM2} [DecidableEq tm.Λ] [DecidableEq tm.σ]
  [(k : tm.K) → DecidableEq (Symbol tm k)]

instance relationDecidable {T B : ℕ} (initial final : Row tm B)
    (e : Constraint tm T B) (v : Fin (arity tm) → Alphabet tm) :
    Decidable (Relation initial final e v) := by
  rcases e with _ | ⟨t, k, j⟩ | t | ⟨t, k, j⟩ | ⟨b, _ | ⟨k, j⟩⟩ <;>
    dsimp only [Relation] <;> infer_instance

/-- An ordinary finite Boolean lookup once the fixed machine's symbols have decidable equality. -/
def relation {T B : ℕ} (initial final : Row tm B) (e : Constraint tm T B)
    (v : Fin (arity tm) → Alphabet tm) : Bool := decide (Relation initial final e v)

@[simp] theorem relation_eq_true {T B : ℕ} (initial final : Row tm B)
    (e : Constraint tm T B) (v : Fin (arity tm) → Alphabet tm) :
    relation initial final e v = true ↔ Relation initial final e v := by
  simp [relation]

end Decidable

end PCP.Machine.TableauConstraints
