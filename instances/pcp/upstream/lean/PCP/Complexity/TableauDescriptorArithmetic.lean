/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.NPTableauRelationTable

/-!
# Arithmetic selection of machine-fixed tableau truth-table entries

The arithmetic descriptor uses only metadata, constraint indices, comparisons,
division and remainder. Its sole data access is one public input-bit lookup.
-/

namespace PCP.Machine.TableauDescriptorArithmetic

open Turing TM2Locality TableauConstraints TableauIndex TableauNumericIndex

variable {k T B : ℕ}

def inputSelector (n W j bit : ℕ) : ℕ :=
  if j < n then bit else if j = n then 2 else if j < n + 1 + W then 3 else 4

/-- Kind, stack, and bounded local-position fields of the fixed lookup-table address. -/
def select (k window output stack₀ T B W n : ℕ) (bit : ℕ → ℕ) (e : ℕ) :
    ℕ × ℕ × ℕ :=
  if e = 0 then (0, stack₀, 0) else
  if e < 1 + links k window T then
    let z := e - 1
    (1, z % (k * window) / window, z % window)
  else if e < 1 + links k window T + T then (2, stack₀, 0)
  else if e < boundaryOffset k window T B then
    let z := e - (1 + links k window T + T)
    (3, z % (k * B) / B, min (z % B) output)
  else if e < constraints k window T B then
    let z := e - boundaryOffset k window T B
    let b := z / sites k B
    let s := z % sites k B
    if s = 0 then (if b = 0 then 4 else 6, stack₀, 0) else
      let stack := (s - 1) / B
      let j := (s - 1) % B
      if b = 0 then (5, stack, inputSelector n W j (bit j)) else (7, stack, min j 1)
  else (8, stack₀, 0)

private theorem pair_decode (base x y : ℕ) (hy : y < base) :
    (x * base + y) / base = x ∧ (x * base + y) % base = y := by
  have hb : 0 < base := by omega
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt hy, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]

private theorem triple_bound (bound width time stack j base : ℕ)
    (ht : time < bound) (hs : stack < width) (hj : j < base) :
    time * (width * base) + stack * base + j < bound * (width * base) := by
  have hs' := Nat.mul_le_mul_right base (Nat.succ_le_of_lt hs)
  have ht' := Nat.mul_le_mul_right (width * base) (Nat.succ_le_of_lt ht)
  nlinarith only [hs', ht', hj]

private theorem triple_decode (width time stack j base : ℕ) (hs : stack < width) (hj : j < base) :
    (time * (width * base) + stack * base + j) / (width * base) = time ∧
    (time * (width * base) + stack * base + j) % (width * base) / base = stack ∧
    (time * (width * base) + stack * base + j) % base = j := by
  have hs' := Nat.mul_le_mul_right base (Nat.succ_le_of_lt hs)
  have hr : stack * base + j < width * base := by nlinarith only [hs', hj]
  have hpair := pair_decode (width * base) time (stack * base + j) hr
  have hcell := pair_decode base stack j hj
  refine ⟨by simpa only [Nat.add_assoc] using hpair.1, ?_, ?_⟩
  · rw [Nat.add_assoc, hpair.2, hcell.1]
  · have heq : time * (width * base) + stack * base + j = (time * width + stack) * base + j :=
      by ring
    rw [heq]
    exact (pair_decode base (time * width + stack) j hj).2

theorem select_link (window output stack₀ W n : ℕ) (bit : ℕ → ℕ)
    (t : Fin (T + 1)) (stack : Fin k) (j : Fin window) :
    select k window output stack₀ T B W n bit
        (1 + t.val * (k * window) + stack.val * window + j.val) = (1, stack.val, j.val) := by
  have hb := triple_bound (T + 1) k t.val stack.val j.val window t.isLt stack.isLt j.isLt
  have hd := triple_decode k t.val stack.val j.val window stack.isLt j.isLt
  have h0 : 1 + t.val * (k * window) + stack.val * window + j.val ≠ 0 := by omega
  have hlt : 1 + t.val * (k * window) + stack.val * window + j.val <
      1 + links k window T := by dsimp [links]; omega
  simp only [select, ite_eq_right h0, ite_eq_left hlt]
  have heq : 1 + t.val * (k * window) + stack.val * window + j.val - 1 =
      t.val * (k * window) + stack.val * window + j.val := by omega
  rw [heq, hd.2.1, hd.2.2]

theorem select_control (window output stack₀ W n : ℕ) (bit : ℕ → ℕ) (t : Fin T) :
    select k window output stack₀ T B W n bit (1 + links k window T + t.val) = (2, stack₀, 0) := by
  have h0 : 1 + links k window T + t.val ≠ 0 := by omega
  have hlink : ¬1 + links k window T + t.val < 1 + links k window T := by omega
  have hlt : 1 + links k window T + t.val < 1 + links k window T + T := by omega
  simp only [select, ite_eq_right h0, ite_eq_right hlink, ite_eq_left hlt]

theorem select_cell (window output stack₀ W n : ℕ) (bit : ℕ → ℕ)
    (t : Fin T) (stack : Fin k) (j : Fin B) :
    select k window output stack₀ T B W n bit
        (1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val) =
      (3, stack.val, min j.val output) := by
  have hb := triple_bound T k t.val stack.val j.val B t.isLt stack.isLt j.isLt
  have hd := triple_decode k t.val stack.val j.val B stack.isLt j.isLt
  have h0 : 1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val ≠ 0 := by omega
  have hlink : ¬1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val <
      1 + links k window T := by omega
  have hcontrol : ¬1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val <
      1 + links k window T + T := by omega
  have hlt : 1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val <
      boundaryOffset k window T B := by dsimp [boundaryOffset]; omega
  simp only [select, ite_eq_right h0, ite_eq_right hlink, ite_eq_right hcontrol, ite_eq_left hlt]
  have heq : 1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val -
      (1 + links k window T + T) = t.val * (k * B) + stack.val * B + j.val := by omega
  rw [heq, hd.2.1, hd.2.2]


theorem select_boundary (window output stack₀ W n : ℕ) (bit : ℕ → ℕ)
    (b : Bool) (s : Fin (sites k B)) :
    select k window output stack₀ T B W n bit
        (boundaryOffset k window T B + b.toNat * sites k B + s.val) =
      if s.val = 0 then (if b then 6 else 4, stack₀, 0) else
        if b then (7, (s.val - 1) / B, min ((s.val - 1) % B) 1)
        else (5, (s.val - 1) / B,
          inputSelector n W ((s.val - 1) % B) (bit ((s.val - 1) % B))) := by
  have hb : b.toNat < 2 := by cases b <;> decide
  have hb' := Nat.mul_le_mul_right (sites k B) (Nat.succ_le_of_lt hb)
  have hs := s.isLt
  have hsmall : b.toNat * sites k B + s.val < 2 * sites k B := by nlinarith only [hb', hs]
  have hd := pair_decode (sites k B) b.toNat s.val s.isLt
  have hoff : 1 + links k window T + T ≤ boundaryOffset k window T B := by
    dsimp [boundaryOffset]
    omega
  have h0 : boundaryOffset k window T B + b.toNat * sites k B + s.val ≠ 0 := by omega
  have hlink : ¬boundaryOffset k window T B + b.toNat * sites k B + s.val <
      1 + links k window T := by omega
  have hcontrol : ¬boundaryOffset k window T B + b.toNat * sites k B + s.val <
      1 + links k window T + T := by omega
  have hstep : ¬boundaryOffset k window T B + b.toNat * sites k B + s.val <
      boundaryOffset k window T B := by omega
  have hlt : boundaryOffset k window T B + b.toNat * sites k B + s.val <
      constraints k window T B := by dsimp [constraints]; omega
  simp only [select, ite_eq_right h0, ite_eq_right hlink, ite_eq_right hcontrol, ite_eq_right hstep, ite_eq_left hlt]
  have heq : boundaryOffset k window T B + b.toNat * sites k B + s.val -
      boundaryOffset k window T B = b.toNat * sites k B + s.val := by omega
  rw [heq, hd.1, hd.2]
  cases b <;> rfl

theorem select_extra (window output stack₀ W n j : ℕ) (bit : ℕ → ℕ) :
    select k window output stack₀ T B W n bit (constraints k window T B + j) = (8, stack₀, 0) := by
  have hoff : 1 + links k window T + T ≤ boundaryOffset k window T B := by
    dsimp [boundaryOffset]
    omega
  have hcons : boundaryOffset k window T B ≤ constraints k window T B := by
    dsimp [constraints]
    omega
  have h0 : constraints k window T B + j ≠ 0 := by omega
  have hlink : ¬constraints k window T B + j < 1 + links k window T := by omega
  have hcontrol : ¬constraints k window T B + j < 1 + links k window T + T := by omega
  have hstep : ¬constraints k window T B + j < boundaryOffset k window T B := by omega
  have hbound : ¬constraints k window T B + j < constraints k window T B := by omega
  simp only [select, ite_eq_right h0, ite_eq_right hlink, ite_eq_right hcontrol, ite_eq_right hstep, ite_eq_right hbound]



variable {R : List Bool → List Bool → Bool} (h : NPTableau.Checker R)
  (eK : h.tm.K ≃ Fin k) {W : ℕ}

/-- Arithmetic classification agrees with every structural NP tableau constraint. -/
theorem select_correct (x : List Bool) (e : NPCellConstraints.Constraint h.tm T B W) :
    select k (machineWindow h.tm) (FiniteTransitionTable.outputBound h.tm) (eK h.tm.k₀).val
        T B W x.length (fun j => (x.getD j false).toNat) (withWitnessCode eK T B W e).val =
      ((NPTableauRelationTable.descriptor h x e).1,
        (eK (NPTableauRelationTable.descriptor h x e).2.1).val,
        (NPTableauRelationTable.descriptor h x e).2.2) := by
  rcases e with c | j
  · rcases c with _ | ⟨t, s, j⟩ | t | ⟨t, s, j⟩ | ⟨b, _ | ⟨s, j⟩⟩
    · simp only [withWitness_original, constraint_blank, select, ite_true]
      rfl
    · rw [withWitness_original, constraint_link, select_link]
      rfl
    · rw [withWitness_original, constraint_control, select_control]
      rfl
    · rw [withWitness_original, constraint_cell, select_cell]
      rfl
    · rw [withWitness_original, constraint_boundary]
      rw [select_boundary _ _ _ _ _ _ b (siteCode eK B (.inl ()))]
      simp only [site_control]
      cases b <;> rfl
    · rw [withWitness_original, constraint_boundary]
      rw [select_boundary _ _ _ _ _ _ b (siteCode eK B (.inr (s, j)))]
      simp only [site_cell]
      have hsite : 1 + (eK s).val * B + j.val ≠ 0 := by omega
      have hs : 1 + (eK s).val * B + j.val - 1 = (eK s).val * B + j.val := by omega
      rw [ite_eq_right hsite, hs]
      have hd := pair_decode B (eK s).val j.val j.isLt
      rw [hd.1, hd.2]
      cases b <;> rfl
  · rw [withWitness_extra, select_extra]
    rfl

variable [DecidableEq h.tm.Λ] [DecidableEq h.tm.σ]
  [(k : h.tm.K) → DecidableEq (ComputationTableau.Symbol h.tm k)]
  (hs : StackSupported h.tm (haltList h.tm (NPTableau.output h true)).stk)
  {a : ℕ} (eA : Alphabet h.tm ≃ Fin a)

/-- The concrete arithmetic descriptor and one fixed lookup reproduce the actual relation bit. -/
theorem lookup_select (x : List Bool)
    (hb : ∀ k, ((haltList h.tm (NPTableau.output h true)).stk k).length ≤ B)
    (e : NPCellConstraints.Constraint h.tm T B W) (p : Fin (arity h.tm) → Fin a) :
    let z := select k (machineWindow h.tm) (FiniteTransitionTable.outputBound h.tm)
      (eK h.tm.k₀).val T B W x.length (fun j => (x.getD j false).toNat)
      (withWitnessCode eK T B W e).val
    NPTableauRelationTable.lookup h hs eK eA z.1 z.2.1 z.2.2 (finFunctionFinEquiv p).val =
      (NPCellConstraints.relation h.inputAlphabet x (NPCellConstraints.finalRow h B hs hb) e
        (eA.symm ∘ p)).toNat := by
  rw [select_correct]
  exact NPTableauRelationTable.lookup_relation h hs eK eA x hb e p

/-- The only input location inspected by the descriptor; irrelevant branches ignore it. -/
def publicPosition (k window T B e : ℕ) : ℕ :=
  ((e - boundaryOffset k window T B) % sites k B - 1) % B

/-- One unconditional public-bit read is sufficient for every constraint kind. -/
theorem select_publicPosition (k window output stack₀ T B W n : ℕ)
    (bit : ℕ → ℕ) (e : ℕ) :
    select k window output stack₀ T B W n
      (fun _ => bit (publicPosition k window T B e)) e =
    select k window output stack₀ T B W n bit e := by
  unfold select publicPosition
  split_ifs <;> rfl

end PCP.Machine.TableauDescriptorArithmetic
