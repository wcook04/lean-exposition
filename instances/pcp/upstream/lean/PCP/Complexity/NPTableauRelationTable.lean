/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.NPTableauLocalTables

/-!
# One finite truth table for a fixed NP checker

Nine local predicate kinds, a fixed stack code, a bounded local position and
one tuple of finite alphabet values index the entire table. The table dimensions
are independent of input length, time, space, and witness budgets.
-/

namespace PCP.Machine.NPTableauRelationTable

open Turing ComputationTableau TM2Locality FiniteTransitionTable TableauCells TableauConstraints
  NPTableauLocalTables

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {R : List Bool → List Bool → Bool} (h : NPTableau.Checker R)
  (hs : StackSupported h.tm (haltList h.tm (NPTableau.output h true)).stk)

/-- Every position field fits one fixed range, including the five input-cell kinds. -/
def radius : ℕ := max (machineWindow h.tm) (max (outputBound h.tm + 1) 5)

theorem window_le_radius : machineWindow h.tm ≤ radius h := Nat.le_max_left ..
theorem output_le_radius : outputBound h.tm + 1 ≤ radius h :=
  (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
theorem five_le_radius : 5 ≤ radius h :=
  (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

/-- The finite local predicates, before Boolean evaluation. -/
def LocalTest (kind : ℕ) (stack : h.tm.K) (j : ℕ)
    (p : Fin (arity h.tm) → Alphabet h.tm) : Prop :=
  if kind = 0 then ∀ k, (p (firstSlot h.tm)).2 k = none else
  if kind = 1 then rowCell (p (firstSlot h.tm)).1 stack j = (p (secondSlot h.tm)).2 stack else
  if kind = 2 then
    (p (secondSlot h.tm)).1.1 = (localStep h.tm (p (firstSlot h.tm)).1).1 ∧
    (p (secondSlot h.tm)).1.2.1 = (localStep h.tm (p (firstSlot h.tm)).1).2.1 else
  if kind = 3 then (p (secondSlot h.tm)).2 stack = predicted (p (firstSlot h.tm)).1 stack j
    (fun n => (p (candidateSlot n)).2 stack) else
  if kind = 4 then (p (firstSlot h.tm)).1.1 = some h.tm.main ∧
    (p (firstSlot h.tm)).1.2.1 = h.tm.initialState else
  if kind = 5 then
    if stack = h.tm.k₀ then InputTest j
      (((p (firstSlot h.tm)).2 h.tm.k₀).map (fun s => h.inputAlphabet s.val))
    else (p (firstSlot h.tm)).2 stack = none else
  if kind = 6 then (p (firstSlot h.tm)).1.1 = none ∧
    (p (firstSlot h.tm)).1.2.1 = h.tm.initialState else
  if kind = 7 then (p (firstSlot h.tm)).2 stack = rowCell (finalOne h hs) stack j else
    (p (firstSlot h.tm)).2 h.tm.k₀ = none → (p (secondSlot h.tm)).2 h.tm.k₀ = none

variable [DecidableEq h.tm.Λ] [DecidableEq h.tm.σ]
  [(k : h.tm.K) → DecidableEq (Symbol h.tm k)]

instance localTestDecidable (kind : ℕ) (stack : h.tm.K) (j : ℕ)
    (p : Fin (arity h.tm) → Alphabet h.tm) : Decidable (LocalTest h hs kind stack j p) := by
  unfold LocalTest
  split_ifs <;> infer_instance

def localTest (kind : ℕ) (stack : h.tm.K) (j : ℕ)
    (p : Fin (arity h.tm) → Alphabet h.tm) : Bool := decide (LocalTest h hs kind stack j p)

variable {k a : ℕ} (eK : h.tm.K ≃ Fin k) (eA : Alphabet h.tm ≃ Fin a)

/-- Row-major fixed table; each tuple uses the same little-endian finite-function codec. -/
def table : List ℕ :=
  List.ofFn (fun j : Fin (9 * (k * (radius h * a ^ arity h.tm))) =>
    let kr := finProdFinEquiv.symm j
    let sr := finProdFinEquiv.symm kr.2
    let pr := finProdFinEquiv.symm sr.2
    (localTest h hs kr.1.val (eK.symm sr.1) pr.1.val
      (fun i => eA.symm ((finFunctionFinEquiv.symm pr.2) i))).toNat)

/-- Arithmetic address into the machine-fixed table. -/
def lookup (kind stack pos pattern : ℕ) : ℕ :=
  (table h hs eK eA).getD
    (((kind * k + stack) * radius h + pos) * a ^ arity h.tm + pattern) 0

theorem lookup_correct (kind : Fin 9) (stack : h.tm.K) (pos : Fin (radius h))
    (p : Fin (arity h.tm) → Fin a) :
    lookup h hs eK eA kind.val (eK stack).val pos.val (finFunctionFinEquiv p).val =
      (localTest h hs kind.val stack pos.val (eA.symm ∘ p)).toNat := by
  let j := finProdFinEquiv (kind,
    finProdFinEquiv (eK stack, finProdFinEquiv (pos, finFunctionFinEquiv p)))
  have hj : j.val = ((kind.val * k + (eK stack).val) * radius h + pos.val) *
      a ^ arity h.tm + (finFunctionFinEquiv p).val := by
    dsimp only [j, finProdFinEquiv, Equiv.coe_fn_mk, Prod.fst, Prod.snd]
    ring
  simp only [lookup, ← hj, table, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dite_eq_left j.isLt, Option.getD_some]
  change (localTest h hs (finProdFinEquiv.symm j).1.val
    (eK.symm (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1)
    (finProdFinEquiv.symm (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2).1.val
    (fun i => eA.symm ((finFunctionFinEquiv.symm
      (finProdFinEquiv.symm (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2).2) i))).toNat = _
  simp only [j, Equiv.symm_apply_apply]
  rfl

/-- The structural selector exposes only fixed finite local data. -/
def descriptor {T B W : ℕ} (x : List Bool) :
    NPCellConstraints.Constraint h.tm T B W → ℕ × h.tm.K × ℕ
  | .inl (.inl _ ) => (0, h.tm.k₀, 0)
  | .inl (.inr (.inl (_, stack, j))) => (1, stack, j.val)
  | .inl (.inr (.inr (.inl _))) => (2, h.tm.k₀, 0)
  | .inl (.inr (.inr (.inr (.inl (_, stack, j))))) =>
      (3, stack, min j.val (outputBound h.tm))
  | .inl (.inr (.inr (.inr (.inr (false, .inl _))))) => (4, h.tm.k₀, 0)
  | .inl (.inr (.inr (.inr (.inr (false, .inr (stack, j)))))) =>
      (5, stack, inputKind x W j.val)
  | .inl (.inr (.inr (.inr (.inr (true, .inl _))))) => (6, h.tm.k₀, 0)
  | .inl (.inr (.inr (.inr (.inr (true, .inr (stack, j)))))) => (7, stack, min j.val 1)
  | .inr _ => (8, h.tm.k₀, 0)

omit [DecidableEq h.tm.Λ] [DecidableEq h.tm.σ]
  [(k : h.tm.K) → DecidableEq (Symbol h.tm k)] in
theorem descriptor_kind_lt {T B W : ℕ} (x : List Bool)
    (e : NPCellConstraints.Constraint h.tm T B W) : (descriptor h x e).1 < 9 := by
  rcases e with c | j
  · rcases c with _ | ⟨t, s, j⟩ | t | ⟨t, s, j⟩ | ⟨b, _ | ⟨s, j⟩⟩
    · change 0 < 9; decide
    · change 1 < 9; decide
    · change 2 < 9; decide
    · change 3 < 9; decide
    · cases b <;> simp only [descriptor] <;> decide
    · cases b <;> simp only [descriptor] <;> decide
  · change 8 < 9; decide

omit [DecidableEq h.tm.Λ] [DecidableEq h.tm.σ]
  [(k : h.tm.K) → DecidableEq (Symbol h.tm k)] in
theorem descriptor_position_lt {T B W : ℕ} (x : List Bool)
    (e : NPCellConstraints.Constraint h.tm T B W) : (descriptor h x e).2.2 < radius h := by
  have h5 := five_le_radius h
  rcases e with c | j
  · rcases c with _ | ⟨t, s, j⟩ | t | ⟨t, s, j⟩ | ⟨b, _ | ⟨s, j⟩⟩
    · exact lt_of_lt_of_le (by decide : 0 < 5) h5
    · exact j.isLt.trans_le (window_le_radius h)
    · exact lt_of_lt_of_le (by decide : 0 < 5) h5
    · exact (Nat.lt_succ_of_le (min_le_right _ _)).trans_le (output_le_radius h)
    · cases b <;> exact lt_of_lt_of_le (by decide : 0 < 5) h5
    · cases b
      · exact (inputKind_lt x W j.val).trans_le h5
      · exact (lt_of_le_of_lt (min_le_right _ _) (by decide : 1 < 5)).trans_le h5
  · exact lt_of_lt_of_le (by decide : 0 < 5) h5

omit [DecidableEq h.tm.Λ] [DecidableEq h.tm.σ]
  [(k : h.tm.K) → DecidableEq (Symbol h.tm k)] in
/-- The selected fixed predicate is exactly the original NP tableau relation. -/
theorem localTest_descriptor {T B W : ℕ} (x : List Bool)
    (hb : ∀ k, ((haltList h.tm (NPTableau.output h true)).stk k).length ≤ B)
    (e : NPCellConstraints.Constraint h.tm T B W) (p : Fin (arity h.tm) → Alphabet h.tm) :
    LocalTest h hs (descriptor h x e).1 (descriptor h x e).2.1 (descriptor h x e).2.2 p ↔
      NPCellConstraints.Relation h.inputAlphabet x (NPCellConstraints.finalRow h B hs hb) e p := by
  rcases e with c | j
  · rcases c with _ | ⟨t, s, j⟩ | t | ⟨t, s, j⟩ | ⟨b, _ | ⟨s, j⟩⟩
    · rfl
    · rfl
    · rfl
    · change (p (secondSlot h.tm)).2 s = predicted (p (firstSlot h.tm)).1 s
        (min j.val (outputBound h.tm)) (fun n => (p (candidateSlot n)).2 s) ↔
          (p (secondSlot h.tm)).2 s = predicted (p (firstSlot h.tm)).1 s j.val
            (fun n => (p (candidateSlot n)).2 s)
      rw [predicted_cap _ _ j.val]
    · cases b <;> rfl
    · cases b
      · change (if s = h.tm.k₀ then InputTest (inputKind x W j.val)
          (((p (firstSlot h.tm)).2 h.tm.k₀).map (fun s => h.inputAlphabet s.val))
          else (p (firstSlot h.tm)).2 s = none) ↔
            (if s = h.tm.k₀ then WitnessInputCells.Cell x W j.val
              (((p (firstSlot h.tm)).2 h.tm.k₀).map (fun s => h.inputAlphabet s.val))
              else (p (firstSlot h.tm)).2 s = none)
        by_cases he : s = h.tm.k₀
        · simp only [ite_eq_left he]
          exact inputTest_kind x W j.val _
        · simp only [ite_eq_right he]
      · change (p (firstSlot h.tm)).2 s = rowCell (finalOne h hs) s (min j.val 1) ↔
          (p (firstSlot h.tm)).2 s = rowCell (NPCellConstraints.finalRow h B hs hb) s j.val
        rw [finalCell_cap h hs hb s j.val]
  · rfl

/-- Every actual local relation is obtained from the same fixed finite table. -/
theorem lookup_relation {T B W : ℕ} (x : List Bool)
    (hb : ∀ k, ((haltList h.tm (NPTableau.output h true)).stk k).length ≤ B)
    (e : NPCellConstraints.Constraint h.tm T B W) (p : Fin (arity h.tm) → Fin a) :
    lookup h hs eK eA (descriptor h x e).1 (eK (descriptor h x e).2.1).val
        (descriptor h x e).2.2 (finFunctionFinEquiv p).val =
      (NPCellConstraints.relation h.inputAlphabet x (NPCellConstraints.finalRow h B hs hb) e
        (eA.symm ∘ p)).toNat := by
  rw [lookup_correct h hs eK eA
    ⟨_, descriptor_kind_lt h x e⟩ _ ⟨_, descriptor_position_lt h x e⟩ p]
  apply congrArg Bool.toNat
  apply Bool.eq_iff_iff.mpr
  simp only [localTest, decide_eq_true_iff, NPCellConstraints.relation_eq_true]
  exact localTest_descriptor h hs x hb e (eA.symm ∘ p)

end PCP.Machine.NPTableauRelationTable
