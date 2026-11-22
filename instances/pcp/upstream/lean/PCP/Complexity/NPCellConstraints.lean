/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.NPCellTableau
import PCP.Complexity.TableauConstraints

/-!
# Finite-alphabet lookup constraints for a concrete NP checker

The initial cell tests leave only bounded witness bits free. The additional
adjacent tests enforce trailing blanks. All remaining fixed-arity lookup scopes
are the concrete machine tableau scopes, with exact accepting-run semantics.
-/

namespace PCP.Machine.NPCellConstraints

open Turing ComputationTableau FiniteTransitionTable TableauCells TableauConstraints

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

abbrev Constraint (tm : FinTM2) (T B W : ℕ) := TableauConstraints.Constraint tm T B ⊕ Fin W

/-- The extra scopes inspect two consecutive possible witness cells in the initial row. -/
def scope {tm : FinTM2} {T B W : ℕ} (x : List Bool) :
    Constraint tm T B W → Fin (arity tm) → Variable tm T B
  | .inl c, i => TableauConstraints.scope c i
  | .inr j, i => if i.val = 0 then cellVariable 0 tm.k₀ (x.length + 1 + j.val)
      else cellVariable 0 tm.k₀ (x.length + 1 + (j.val + 1))

/-- The initial cell role is determined by its position and stack. -/
def InitialCell {tm : FinTM2} (e : tm.Γ tm.k₀ ≃ Sym) (x : List Bool) (W : ℕ)
    (k : tm.K) (j : ℕ) (v : Alphabet tm) : Prop :=
  if k = tm.k₀ then WitnessInputCells.Cell x W j ((v.2 tm.k₀).map (fun s => e s.val))
    else v.2 k = none

/-- Replace just the initial boundary; the machine's transition lookup is unchanged. -/
def Relation {tm : FinTM2} {T B W : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (final : Row tm B) :
    Constraint tm T B W → (Fin (arity tm) → Alphabet tm) → Prop
  | .inl (.inr (.inr (.inr (.inr (false, .inl _))))), v =>
      (v (firstSlot tm)).1.1 = some tm.main ∧ (v (firstSlot tm)).1.2.1 = tm.initialState
  | .inl (.inr (.inr (.inr (.inr (false, .inr (k, j)))))), v =>
      InitialCell e x W k j.val (v (firstSlot tm))
  | .inl c, v => TableauConstraints.Relation final final c v
  | .inr _, v => (v (firstSlot tm)).2 tm.k₀ = none → (v (secondSlot tm)).2 tm.k₀ = none

def Holds {tm : FinTM2} {T B W : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (final : Row tm B) (a : Variable tm T B → Alphabet tm) : Prop :=
  ∀ c : Constraint tm T B W, Relation e x final c (fun i => a (scope x c i))

theorem initial_cell_input_iff {tm : FinTM2} {T B W : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (a : Variable tm T B → Alphabet tm)
    (hz : ∀ k, (a (.inr ())).2 k = none) (j : Fin B) :
    InitialCell e x W tm.k₀ j.val (a (cellVariable 0 tm.k₀ j.val)) ↔
      WitnessInputCells.Cell x W j.val
        (NPCellTableau.inputView e ((decodeAssignment a).2 0) j) := by
  unfold InitialCell
  rw [ite_eq_left (show tm.k₀ = tm.k₀ from rfl)]
  simp only [NPCellTableau.inputView]
  rw [← map_cellVariable a hz 0 tm.k₀ j.val, Option.map_map]
  rfl

theorem initial_cell_other_iff {tm : FinTM2} {T B W : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (a : Variable tm T B → Alphabet tm)
    (hz : ∀ k, (a (.inr ())).2 k = none) (k : tm.K) (hk : k ≠ tm.k₀) (j : Fin B) :
    InitialCell e x W k j.val (a (cellVariable 0 k j.val)) ↔
      readCell ((decodeAssignment a).2 0) k j.val = none := by
  rw [← map_cellVariable a hz 0 k j.val, Option.map_eq_none_iff]
  simp only [InitialCell, ite_eq_right hk]

theorem adjacent_iff {tm : FinTM2} {T B W : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (final : Row tm B) (a : Variable tm T B → Alphabet tm)
    (hz : ∀ k, (a (.inr ())).2 k = none) (j : Fin W) :
    Relation (T := T) e x final (.inr j) (fun i => a (scope x (.inr j) i)) ↔
      (WitnessInputCells.read (NPCellTableau.inputView e ((decodeAssignment a).2 0))
        (x.length + 1 + j.val) = none →
      WitnessInputCells.read (NPCellTableau.inputView e ((decodeAssignment a).2 0))
        (x.length + 1 + (j.val + 1)) = none) := by
  simp only [NPCellTableau.read_inputView, Option.map_eq_none_iff]
  rw [← map_cellVariable a hz 0 tm.k₀ (x.length + 1 + j.val),
    ← map_cellVariable a hz 0 tm.k₀ (x.length + 1 + (j.val + 1))]
  simp only [Option.map_eq_none_iff]
  rfl

/-- Exact correspondence between the concrete lookup scopes and the NP cell tableau. -/
theorem holds_iff {tm : FinTM2} {T B W : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (final : Row tm B) (a : Variable tm T B → Alphabet tm) :
    Holds (W := W) e x final a ↔ (∀ k, (a (.inr ())).2 k = none) ∧
      NPCellTableau.Satisfies tm e T B W x (decodeRow final) (decodeAssignment a) := by
  constructor
  · intro h
    have hz : ∀ k, (a (.inr ())).2 k = none := h (.inl (.inl ()))
    have hc : (decodeRow ((decodeAssignment a).1 0)).l = some tm.main ∧
        (decodeRow ((decodeAssignment a).1 0)).var = tm.initialState :=
      h (.inl (.inr (.inr (.inr (.inr (false, .inl ()))))))
    refine ⟨hz, ⟨hc.1, hc.2, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro k hk j
      apply (initial_cell_other_iff e x a hz k hk j).mp
      exact h (.inl (.inr (.inr (.inr (.inr (false, .inr (k, j)))))))
    · intro j
      apply (initial_cell_input_iff e x a hz j).mp
      exact h (.inl (.inr (.inr (.inr (.inr (false, .inr (tm.k₀, j)))))))
    · intro j
      exact (adjacent_iff e x final a hz j).mp (h (.inr j))
    · intro t k j
      exact (relation_link_iff final final a hz t k j).mp (h (.inl (.inr (.inl (t, k, j)))))
    · intro t
      have hc := (relation_control_iff final final a t).mp (h (.inl (.inr (.inr (.inl t)))))
      refine ⟨hc.1, hc.2, fun k j => ?_⟩
      exact (relation_step_iff final final a hz t k j).mp
        (h (.inl (.inr (.inr (.inr (.inl (t, k, j)))))))
    · have hc := (relation_boundary_control_iff final final a true).mp
        (h (.inl (.inr (.inr (.inr (.inr (true, .inl ())))))))
      refine ⟨hc.1, hc.2, fun k j => ?_⟩
      exact (relation_boundary_cell_iff final final a hz true k j).mp
        (h (.inl (.inr (.inr (.inr (.inr (true, .inr (k, j))))))))
  · rintro ⟨hz, hi, hl, ht, hf⟩ c
    rcases c with c | j
    · rcases c with _ | ⟨t, k, j⟩ | t | ⟨t, k, j⟩ | ⟨b, _ | ⟨k, j⟩⟩
      · exact hz
      · exact (relation_link_iff final final a hz t k j).mpr (hl t k j)
      · exact (relation_control_iff final final a t).mpr ⟨(ht t).1, (ht t).2.1⟩
      · exact (relation_step_iff final final a hz t k j).mpr ((ht t).2.2 k j)
      · cases b
        · exact ⟨hi.1, hi.2.1⟩
        · exact (relation_boundary_control_iff final final a true).mpr ⟨hf.1, hf.2.1⟩
      · cases b
        · by_cases hk : k = tm.k₀
          · subst k
            exact (initial_cell_input_iff e x a hz j).mpr (hi.2.2.2.1 j)
          · exact (initial_cell_other_iff e x a hz k hk j).mpr (hi.2.2.1 k hk j)
        · exact (relation_boundary_cell_iff final final a hz true k j).mpr (hf.2.2 k j)
    · exact (adjacent_iff e x final a hz j).mpr (hi.2.2.2.2 j)

/-- The finite alphabet assignment and the cell tableau have identical satisfiability. -/
theorem satisfiable_iff {tm : FinTM2} {T B W : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (final : Row tm B) :
    (∃ a, Holds (T := T) (W := W) e x final a) ↔
      ∃ a, NPCellTableau.Satisfies tm e T B W x (decodeRow final) a := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨decodeAssignment a, ((holds_iff e x final a).mp ha).2⟩
  · rintro ⟨a, ha⟩
    refine ⟨encodeAssignment a, (holds_iff e x final _).mpr ⟨fun _ => rfl, ?_⟩⟩
    simpa using ha

/-- These lookup constraints describe the real checker's bounded accepting computation. -/
theorem satisfiable_boundedEval_iff {tm : FinTM2} {T B W : ℕ}
    (e : tm.Γ tm.k₀ ≃ Sym) (x : List Bool) (final : Row tm B)
    (hb : x.length + 1 + W + machinePushBound tm * T ≤ B) :
    (∃ a, Holds (T := T) (W := W) e x final a) ↔
      ∃ w : List Bool, w.length ≤ W ∧
        boundedEval tm T (initList tm ((encodePair (x, w)).map e.symm)) = decodeRow final := by
  rw [satisfiable_iff]
  exact NPCellTableau.exists_satisfies_iff tm e T B W x _ hb (decodeRow_stack_length_le final)

section Decidable

variable {tm : FinTM2} [DecidableEq tm.Λ] [DecidableEq tm.σ]
  [(k : tm.K) → DecidableEq (Symbol tm k)]

instance initialCellDecidable (e : tm.Γ tm.k₀ ≃ Sym) (x : List Bool) (W : ℕ)
    (k : tm.K) (j : ℕ) (v : Alphabet tm) : Decidable (InitialCell e x W k j v) := by
  unfold InitialCell
  split <;> infer_instance

instance relationDecidable {T B W : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (final : Row tm B) (c : Constraint tm T B W)
    (v : Fin (arity tm) → Alphabet tm) : Decidable (Relation e x final c v) := by
  rcases c with c | j
  · rcases c with _ | ⟨t, k, j⟩ | t | ⟨t, k, j⟩ | ⟨b, _ | ⟨k, j⟩⟩
    all_goals try { dsimp only [Relation]; infer_instance }
    all_goals cases b <;> dsimp only [Relation] <;> infer_instance
  · dsimp only [Relation]
    infer_instance

/-- Executable local predicates; all finite-symbol equality instances are machine-fixed. -/
def relation {T B W : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (final : Row tm B) (c : Constraint tm T B W)
    (v : Fin (arity tm) → Alphabet tm) : Bool := decide (Relation e x final c v)

@[simp] theorem relation_eq_true {T B W : ℕ} (e : tm.Γ tm.k₀ ≃ Sym)
    (x : List Bool) (final : Row tm B) (c : Constraint tm T B W)
    (v : Fin (arity tm) → Alphabet tm) :
    relation e x final c v = true ↔ Relation e x final c v := by simp [relation]

end Decidable


variable {R : List Bool → List Bool → Bool} (h : NPTableau.Checker R) (q : Polynomial ℕ)

/-- If acceptance is ever possible, its terminal symbols belong to the proved finite support. -/
theorem accepting_supported {x w : List Bool} (hR : R x w = true) :
    StackSupported h.tm (haltList h.tm (NPTableau.output h true)).stk := by
  have hout := boundedEval_initList (h.outputsFun (x, w)) (le_refl _)
  change boundedEval h.tm (h.time.eval (encodePair (x, w)).length)
    (initList h.tm (NPTableau.input h x w)) = haltList h.tm (NPTableau.output h (R x w)) at hout
  have hs := supported_boundedEval h.tm (h.time.eval (encodePair (x, w)).length)
    (initList h.tm (NPTableau.input h x w)) (stackSupported_initList h.tm _)
  rw [hout, hR] at hs
  exact hs

theorem accepting_length_le (x : List Bool) (k : h.tm.K) :
    ((haltList h.tm (NPTableau.output h true)).stk k).length ≤
      (NPTableau.spacePoly h q).eval x.length := by
  apply (stack_length_le_mass h.tm _ k).trans
  rw [mass_haltList]
  simp only [NPTableau.output, encodeBool, List.length_map, List.length_cons, List.length_nil]
  rw [NPTableau.spacePoly_eval]
  omega

/-- The accepting boundary is a finite row whenever its fixed symbols can occur. -/
def finalRow (B : ℕ)
    (hs : StackSupported h.tm (haltList h.tm (NPTableau.output h true)).stk)
    (hb : ∀ k, ((haltList h.tm (NPTableau.output h true)).stk k).length ≤ B) : Row h.tm B :=
  encodeRow (haltList h.tm (NPTableau.output h true)) hs hb

@[simp] theorem decode_finalRow (B : ℕ)
    (hs : StackSupported h.tm (haltList h.tm (NPTableau.output h true)).stk)
    (hb : ∀ k, ((haltList h.tm (NPTableau.output h true)).stk k).length ≤ B) :
    decodeRow (finalRow h B hs hb) = haltList h.tm (NPTableau.output h true) := by
  apply decode_encodeRow

/-- All actual checker premises are discharged; the remaining support case is machine-fixed. -/
theorem satisfiable_accepts_iff
    (hs : StackSupported h.tm (haltList h.tm (NPTableau.output h true)).stk) (x : List Bool) :
    (∃ a, Holds (T := (NPTableau.timePoly h q).eval x.length) (W := q.eval x.length)
      h.inputAlphabet x
      (finalRow h ((NPTableau.spacePoly h q).eval x.length) hs (accepting_length_le h q x)) a) ↔
      ∃ w : List Bool, w.length ≤ q.eval x.length ∧ R x w = true := by
  rw [satisfiable_iff, decode_finalRow]
  exact NPCellTableau.exists_accepts_iff h q x

/-- If its accepting symbol is unsupported, the concrete checker accepts no witness on any input. -/
theorem never_accepts_of_unsupported
    (hs : ¬StackSupported h.tm (haltList h.tm (NPTableau.output h true)).stk) :
    ∀ x w, R x w ≠ true := fun _ _ hR => hs (accepting_supported h hR)

end PCP.Machine.NPCellConstraints
