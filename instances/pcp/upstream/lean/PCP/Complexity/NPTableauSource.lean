/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.TableauSourceLang

/-!
# Exact machine-tableau source generation

For a fixed checker and fixed finite-alphabet codes, the operational source
emitter produces precisely its bounded computation constraints. Only the initial
four metadata values and public input bits vary with the source input.
-/

namespace PCP.Machine.NPTableauSource

open Turing ComputationTableau TableauConstraints TableauIndex

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {R : List Bool → List Bool → Bool} (h : NPTableau.Checker R)
  [DecidableEq h.tm.Λ] [DecidableEq h.tm.σ]
  [(k : h.tm.K) → DecidableEq (Symbol h.tm k)]
  (hs : StackSupported h.tm (haltList h.tm (NPTableau.output h true)).stk)
  {k a T B W : ℕ} (eK : h.tm.K ≃ Fin k) (eA : Alphabet h.tm ≃ Fin a)

/-- The program constants depend only on the fixed checker and its finite codes. -/
def parameters : TableauSourceLang.Parameters where
  stackCount := k
  window := TM2Locality.machineWindow h.tm
  output := FiniteTransitionTable.outputBound h.tm
  stack₀ := (eK h.tm.k₀).val
  radius := NPTableauRelationTable.radius h
  alphabet := a
  arity := arity h.tm
  table := NPTableauRelationTable.table h hs eK eA

/-- The four budget fields are computed separately by fixed polynomial programs. -/
def input (T B W : ℕ) (x : List Bool) : List ℕ :=
  T :: B :: W :: x.length :: x.map Bool.toNat

@[simp] theorem input_zero (x : List Bool) : (input T B W x).getD 0 0 = T := rfl
@[simp] theorem input_one (x : List Bool) : (input T B W x).getD 1 0 = B := rfl
@[simp] theorem input_two (x : List Bool) : (input T B W x).getD 2 0 = W := rfl
@[simp] theorem input_three (x : List Bool) : (input T B W x).getD 3 0 = x.length := rfl

@[simp] theorem input_bit (x : List Bool) (j : ℕ) :
    (input T B W x).getD (4 + j) 0 = (x.getD j false).toNat := by
  change (input T B W x).getD (4 + j) false.toNat = _
  rw [show 4 + j = j + 4 by omega]
  simpa only [input, List.getD_cons_succ] using List.getD_map (l := x) (d := false) Bool.toNat

def indexedRelation (x : List Bool)
    (hb : ∀ s, ((haltList h.tm (NPTableau.output h true)).stk s).length ≤ B) :
    Fin (TableauNumericIndex.constraints k (TM2Locality.machineWindow h.tm) T B + W) →
      (Fin (arity h.tm) → Fin a) → Bool :=
  fun e p => NPCellConstraints.relation h.inputAlphabet x (NPCellConstraints.finalRow h B hs hb)
    ((withWitnessCode eK T B W).symm e) (eA.symm ∘ p)

omit hs eA in
/-- Variable indices use only arithmetic sum/product codecs. -/
def indexedScope (x : List Bool) :
    Fin (TableauNumericIndex.constraints k (TM2Locality.machineWindow h.tm) T B + W) →
      Fin (arity h.tm) → Fin (TableauNumericIndex.variableCount k T B) :=
  fun e i => variableCode eK T B (NPCellConstraints.scope x ((withWitnessCode eK T B W).symm e) i)

/-- The operational fixed-table lookup equals each actual checker relation bit. -/
theorem relation_input (x : List Bool)
    (hb : ∀ s, ((haltList h.tm (NPTableau.output h true)).stk s).length ≤ B)
    (e : Fin (TableauNumericIndex.constraints k (TM2Locality.machineWindow h.tm) T B + W))
    (p : Fin (arity h.tm) → Fin a) :
    TableauSourceLang.relation (parameters h hs eK eA) (input T B W x) e.val
        (finFunctionFinEquiv p).val = (indexedRelation h hs eK eA x hb e p).toNat := by
  have he := TableauDescriptorArithmetic.lookup_select h eK hs eA x hb
    ((withWitnessCode eK T B W).symm e) p
  have hecode : ((withWitnessCode eK T B W) ((withWitnessCode eK T B W).symm e)).val =
      e.val := congrArg Fin.val ((withWitnessCode eK T B W).apply_symm_apply e)
  dsimp only at he
  rw [hecode] at he
  simpa only [TableauSourceLang.relation, TableauSourceLang.descriptor, parameters,
    input_zero, input_one, input_two, input_three, input_bit, NPTableauRelationTable.lookup,
    indexedRelation] using he

/-- The operational scope decoder equals every actual typed constraint scope. -/
theorem scope_input (x : List Bool)
    (e : Fin (TableauNumericIndex.constraints k (TM2Locality.machineWindow h.tm) T B + W))
    (i : Fin (arity h.tm)) :
    TableauSourceLang.scope (parameters h hs eK eA) (input T B W x) e.val i.val =
      (indexedScope h eK x e i).val := by
  have he := TableauNumericIndex.scope_correct eK x ((withWitnessCode eK T B W).symm e) i
  have hecode : ((withWitnessCode eK T B W) ((withWitnessCode eK T B W).symm e)).val =
      e.val := congrArg Fin.val ((withWitnessCode eK T B W).apply_symm_apply e)
  rw [hecode] at he
  simpa only [TableauSourceLang.scope, parameters, input_zero, input_one, input_three,
    indexedScope] using he

/-- The complete charged program produces the exact finite-domain tableau source. -/
theorem program_run (x : List Bool)
    (hb : ∀ s, ((haltList h.tm (NPTableau.output h true)).stk s).length ≤ B) :
    (TableauSourceLang.program (parameters h hs eK eA)).run (input T B W x) =
      PCP.Reduction.FiniteDomainSource.source (indexedRelation h hs eK eA (T := T) (W := W) x hb)
        (indexedScope h eK x) := by
  apply TableauSourceLang.program_run_source
  · rfl
  · rfl
  · exact relation_input h hs eK eA x hb
  · exact scope_input h hs eK eA x


/-- Arithmetic index and alphabet transport preserve the actual tableau satisfiability. -/
theorem indexed_satisfiable_iff (x : List Bool)
    (hb : ∀ s, ((haltList h.tm (NPTableau.output h true)).stk s).length ≤ B) :
    (∃ f, PCP.Reduction.FiniteDomainConstraints.Holds
      (indexedRelation h hs eK eA (T := T) (W := W) x hb) (indexedScope h eK x) f) ↔
    ∃ f, NPCellConstraints.Holds (T := T) (W := W) h.inputAlphabet x
      (NPCellConstraints.finalRow h B hs hb) f := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun v => eA.symm (f (variableCode eK T B v)), fun e => ?_⟩
    have hh := hf (withWitnessCode eK T B W e)
    change NPCellConstraints.relation h.inputAlphabet x (NPCellConstraints.finalRow h B hs hb)
      ((withWitnessCode eK T B W).symm (withWitnessCode eK T B W e))
      (fun i => eA.symm (f (variableCode eK T B (NPCellConstraints.scope x
        ((withWitnessCode eK T B W).symm (withWitnessCode eK T B W e)) i)))) = true at hh
    rw [(withWitnessCode eK T B W).symm_apply_apply] at hh
    exact (NPCellConstraints.relation_eq_true _ _ _ _ _).mp hh
  · rintro ⟨f, hf⟩
    refine ⟨fun v => eA (f ((variableCode eK T B).symm v)), fun e => ?_⟩
    change NPCellConstraints.relation h.inputAlphabet x (NPCellConstraints.finalRow h B hs hb)
      ((withWitnessCode eK T B W).symm e)
      (fun i => eA.symm (eA (f ((variableCode eK T B).symm
        (variableCode eK T B (NPCellConstraints.scope x
          ((withWitnessCode eK T B W).symm e) i)))))) = true
    simp only [(variableCode eK T B).symm_apply_apply, eA.symm_apply_apply]
    exact (NPCellConstraints.relation_eq_true _ _ _ _ _).mpr (hf _)

end PCP.Machine.NPTableauSource
