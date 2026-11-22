/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.FiniteDomainEncoding
import PCP.Reduction.BooleanClauseSource

/-!
# Stored finite-domain constraints and fixed one-hot decoding tables

Only a relation's fixed-width truth table and scope indices are stored. One-hot
pattern decoding is a finite table depending solely on alphabet size and local
arity; no table enumerates a full computation row or a growing collection of cells.
-/

namespace PCP.Reduction.FiniteDomainSource

open FiniteDomainConstraints

variable {v c a d : ℕ}

def width (a d : ℕ) : ℕ := a ^ d + d

def record (R : Fin c → (Fin d → Fin a) → Bool) (s : Fin c → Fin d → Fin v)
    (e : Fin c) (i : Fin (width a d)) : ℕ :=
  if hp : i.val < a ^ d then (R e (finFunctionFinEquiv.symm ⟨i.val, hp⟩)).toNat
  else (s e ⟨i.val - a ^ d, by have := i.isLt; dsimp [width] at *; omega⟩).val

def source (R : Fin c → (Fin d → Fin a) → Bool) (s : Fin c → Fin d → Fin v) : List ℕ :=
  v :: c :: List.ofFn (fun j : Fin (c * width a d) =>
    record R s (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)

def variableCount (input : List ℕ) : ℕ := input.getD 0 0
def constraintCount (input : List ℕ) : ℕ := input.getD 1 0

def scope (input : List ℕ) (a d e i : ℕ) : ℕ :=
  input.getD (2 + (e * width a d + (a ^ d + i))) 0

def relation (input : List ℕ) (a d e p : ℕ) : ℕ :=
  input.getD (2 + (e * width a d + p)) 0

@[simp] theorem source_variableCount (R : Fin c → (Fin d → Fin a) → Bool)
    (s : Fin c → Fin d → Fin v) : variableCount (source R s) = v := rfl

@[simp] theorem source_constraintCount (R : Fin c → (Fin d → Fin a) → Bool)
    (s : Fin c → Fin d → Fin v) : constraintCount (source R s) = c := rfl

theorem source_relation (R : Fin c → (Fin d → Fin a) → Bool) (s : Fin c → Fin d → Fin v)
    (e : Fin c) (p : Fin d → Fin a) :
    relation (source R s) a d e.val (finFunctionFinEquiv p).val = (R e p).toNat := by
  let pi : Fin (width a d) := ⟨(finFunctionFinEquiv p).val,
    lt_of_lt_of_le (finFunctionFinEquiv p).isLt (by dsimp [width]; omega)⟩
  let j := finProdFinEquiv (e, pi)
  have hj : j.val = e.val * width a d + (finFunctionFinEquiv p).val := by
    simp [j, pi, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [relation, ← hj, source, List.getD_eq_getElem?_getD]
  rw [show 2 + j.val = j.val + 2 by omega]
  simp only [List.getElem?_cons_succ, List.getElem?_ofFn, dite_eq_left j.isLt, Option.getD_some]
  change record R s (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2 = _
  rw [show finProdFinEquiv.symm j = (e, pi) from Equiv.symm_apply_apply _ _]
  dsimp only [record, pi]
  rw [dite_eq_left (finFunctionFinEquiv p).isLt]
  exact congrArg (fun x => (R e x).toNat) (Equiv.symm_apply_apply _ _)

theorem source_scope (R : Fin c → (Fin d → Fin a) → Bool) (s : Fin c → Fin d → Fin v)
    (e : Fin c) (i : Fin d) : scope (source R s) a d e.val i.val = (s e i).val := by
  let pi : Fin (width a d) := ⟨a ^ d + i.val, by dsimp [width]; omega⟩
  let j := finProdFinEquiv (e, pi)
  have hj : j.val = e.val * width a d + (a ^ d + i.val) := by
    simp [j, pi, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [scope, ← hj, source, List.getD_eq_getElem?_getD]
  rw [show 2 + j.val = j.val + 2 by omega]
  simp only [List.getElem?_cons_succ, List.getElem?_ofFn, dite_eq_left j.isLt, Option.getD_some]
  change record R s (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2 = _
  rw [show finProdFinEquiv.symm j = (e, pi) from Equiv.symm_apply_apply _ _]
  simp [record, pi]

/-- The fixed Boolean block pattern matches a unique finite-domain tuple, if any. -/
def Matches (p : FiniteBooleanConstraints.Pattern (arity a d)) (x : Fin d → Fin a) : Prop :=
  ∀ i j, p (inputSlot i j) = decide (x i = j)

instance (p : FiniteBooleanConstraints.Pattern (arity a d)) (x : Fin d → Fin a) :
    Decidable (Matches p x) :=
  inferInstanceAs (Decidable (∀ i j, p (inputSlot i j) = decide (x i = j)))

theorem matches_unique {p : FiniteBooleanConstraints.Pattern (arity a d)}
    {x y : Fin d → Fin a} (hx : Matches p x) (hy : Matches p y) : x = y := by
  funext i
  apply oneHot_injective
  intro j
  exact (hx i j).symm.trans (hy i j)

def decode (p : FiniteBooleanConstraints.Pattern (arity a d)) : Option (Fin (a ^ d)) :=
  Fin.find? (fun j => decide (Matches p (finFunctionFinEquiv.symm j)))

theorem decode_complete (p : FiniteBooleanConstraints.Pattern (arity a d))
    (x : Fin d → Fin a) (hx : Matches p x) : decode p = some (finFunctionFinEquiv x) := by
  apply Option.mem_def.mp
  apply Fin.mem_find?_iff.mpr
  refine ⟨by simpa using hx, fun j hj hmatch => ?_⟩
  have hsame : finFunctionFinEquiv.symm j = x := matches_unique (of_decide_eq_true hmatch) hx
  have hjx : j = finFunctionFinEquiv x := by simpa using congrArg finFunctionFinEquiv hsame
  subst j
  exact (lt_irrefl _ hj)

theorem decode_sound (p : FiniteBooleanConstraints.Pattern (arity a d))
    (j : Fin (a ^ d)) (h : decode p = some j) : Matches p (finFunctionFinEquiv.symm j) :=
  of_decide_eq_true (Fin.mem_find?_iff.mp (Option.mem_def.mpr h)).1

/-- The one-hot relation test is one stored truth-table read after fixed pattern decoding. -/
theorem relation_decode (R : (Fin d → Fin a) → Bool)
    (p : FiniteBooleanConstraints.Pattern (arity a d)) :
    (decide (∃ x, R x = true ∧ Matches p x)).toNat =
      match decode p with
      | none => 0
      | some j => (R (finFunctionFinEquiv.symm j)).toNat := by
  cases hdec : decode p with
  | none =>
      have hn : ¬∃ x, R x = true ∧ Matches p x := by
        rintro ⟨x, _, hx⟩
        have hc := decode_complete p x hx
        rw [hdec] at hc
        contradiction
      simp [hn]
  | some j =>
      have hj := decode_sound p j hdec
      have he : (∃ x, R x = true ∧ Matches p x) ↔ R (finFunctionFinEquiv.symm j) = true := by
        constructor
        · rintro ⟨x, hx, hm⟩
          exact matches_unique hm hj ▸ hx
        · intro h
          exact ⟨_, h, hj⟩
      change (decide (∃ x, R x = true ∧ Matches p x)).toNat =
        (R (finFunctionFinEquiv.symm j)).toNat
      apply congrArg Bool.toNat
      apply Bool.eq_iff_iff.mpr
      exact decide_eq_true_iff.trans he

/-- Zero represents an invalid block; successor represents a tuple's numeric truth-table index. -/
def decodeTable (a d : ℕ) : List ℕ :=
  List.ofFn (fun p : Fin (2 ^ arity a d) =>
    ((decode ((FiniteBooleanEncoding.patternCode (arity a d)).symm p)).map
      (fun j => j.val + 1)).getD 0)

def validityTable (a d : ℕ) : List ℕ :=
  List.ofFn (fun p : Fin (2 ^ arity a d) =>
    (decide (∃ x : Fin a, ∀ j, (FiniteBooleanEncoding.patternCode (arity a d)).symm p
      (firstSlot (d := d) j) = decide (x = j))).toNat)

theorem decodeTable_get (p : FiniteBooleanConstraints.Pattern (arity a d)) :
    (decodeTable a d).getD (FiniteBooleanEncoding.patternCode (arity a d) p).val 0 =
      ((decode p).map (fun j => j.val + 1)).getD 0 := by
  simp [decodeTable, List.getD_eq_getElem?_getD]

theorem validityTable_get (p : FiniteBooleanConstraints.Pattern (arity a d)) :
    (validityTable a d).getD (FiniteBooleanEncoding.patternCode (arity a d) p).val 0 =
      (decide (∃ x : Fin a, ∀ j, p (firstSlot (d := d) j) = decide (x = j))).toNat := by
  simp [validityTable, List.getD_eq_getElem?_getD]

/-- Numeric one-hot relation decoder; all pattern tables are fixed by `a,d`. -/
def booleanRelation (a d : ℕ) (input : List ℕ) (e p : ℕ) : ℕ :=
  if e < constraintCount input then
    let j := (decodeTable a d).getD p 0
    if j = 0 then 0 else relation input a d e (j - 1)
  else (validityTable a d).getD p 0

/-- Numeric one-hot scopes include the fixed dummy block used for padding. -/
def booleanScope (a d : ℕ) (input : List ℕ) (e i : ℕ) : ℕ :=
  (if e < constraintCount input then
    if i / a < d then scope input a d e (i / a) else variableCount input
  else e - constraintCount input) * a + i % a


theorem constraintCode_inl (e : Fin c) :
    (FiniteDomainEncoding.constraintCode (Equiv.refl (Fin v)) (Equiv.refl (Fin c))
      (.inl e)).val = e.val := by
  simp [FiniteDomainEncoding.constraintCode, finSumFinEquiv]

theorem constraintCode_inr (x : Fin v) :
    (FiniteDomainEncoding.constraintCode (Equiv.refl (Fin v)) (Equiv.refl (Fin c))
      (.inr x)).val = c + x.val := by
  simp [FiniteDomainEncoding.constraintCode, finSumFinEquiv]

theorem variableCode_inl (x : Fin v) (j : Fin a) :
    (FiniteDomainEncoding.variableCode (Equiv.refl (Fin v)) (.inl x, j)).val =
      x.val * a + j.val := by
  simp [FiniteDomainEncoding.variableCode, finSumFinEquiv, finProdFinEquiv, Nat.add_comm,
    Nat.mul_comm]

theorem variableCode_inr (j : Fin a) :
    (FiniteDomainEncoding.variableCode (Equiv.refl (Fin v)) (.inr (), j)).val =
      v * a + j.val := by
  simp [FiniteDomainEncoding.variableCode, finSumFinEquiv, finProdFinEquiv, Nat.add_comm,
    Nat.mul_comm]

/-- Numeric truth-table reads reproduce the existing one-hot relation compiler. -/
theorem booleanRelation_correct (R : Fin c → (Fin d → Fin a) → Bool)
    (s : Fin c → Fin d → Fin v) (e : Fin (c + v))
    (p : FiniteBooleanConstraints.Pattern (arity a d)) :
    booleanRelation a d (source R s) e.val (FiniteBooleanEncoding.patternCode (arity a d) p).val =
      (FiniteDomainEncoding.indexedRelation
      (Equiv.refl (Fin v)) (Equiv.refl (Fin c)) R e p).toNat := by
  obtain ⟨z, rfl⟩ := (FiniteDomainEncoding.constraintCode
    (Equiv.refl (Fin v)) (Equiv.refl (Fin c))).surjective e
  simp only [FiniteDomainEncoding.indexedRelation, Equiv.symm_apply_apply]
  cases z with
  | inl e =>
      rw [constraintCode_inl]
      simp only [booleanRelation, source_constraintCount, ite_eq_left e.isLt, decodeTable_get]
      change (let j := ((decode p).map (fun j => j.val + 1)).getD 0
        if j = 0 then 0 else relation (source R s) a d e.val (j - 1)) =
          (decide (∃ x, R e x = true ∧ Matches p x)).toNat
      rw [relation_decode]
      cases hd : decode p with
      | none => rfl
      | some j =>
          simp only [Option.map_some, Option.getD_some, Nat.add_one_ne_zero, ite_false,
            Nat.add_sub_cancel]
          have h := source_relation R s e (finFunctionFinEquiv.symm j)
          simpa only [Equiv.apply_symm_apply] using h
  | inr x =>
      rw [constraintCode_inr]
      simp only [booleanRelation, source_constraintCount, ite_eq_right (by omega : ¬c + x.val < c),
        validityTable_get]
      rfl

/-- Arithmetic index decoding reproduces every scope entry, including dummy padding. -/
theorem booleanScope_correct (R : Fin c → (Fin d → Fin a) → Bool)
    (s : Fin c → Fin d → Fin v) (e : Fin (c + v)) (n : Fin (arity a d)) :
    booleanScope a d (source R s) e.val n.val =
      (FiniteDomainEncoding.indexedScope (Equiv.refl (Fin v)) (Equiv.refl (Fin c)) s e n).val := by
  obtain ⟨z, rfl⟩ := (FiniteDomainEncoding.constraintCode
    (Equiv.refl (Fin v)) (Equiv.refl (Fin c))).surjective e
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv : Fin (max 1 d) × Fin a ≃ Fin (arity a d)).surjective n
  have hd : (finProdFinEquiv (i, j)).val / a = i.val := by
    change (j.val + a * i.val) / a = i.val
    rw [Nat.add_mul_div_left _ _ (by have := j.isLt; omega : 0 < a), Nat.div_eq_of_lt j.isLt]
    omega
  have hm : (finProdFinEquiv (i, j)).val % a = j.val := by
    change (j.val + a * i.val) % a = j.val
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  simp only [FiniteDomainEncoding.indexedScope, Equiv.symm_apply_apply]
  cases z with
  | inl e =>
      rw [constraintCode_inl]
      simp only [booleanScope, source_constraintCount, ite_eq_left e.isLt, hd, hm,
        FiniteDomainConstraints.scope, Equiv.symm_apply_apply]
      by_cases hi : i.val < d
      · simp only [ite_eq_left hi, dite_eq_left hi, variableCode_inl]
        rw [source_scope R s e ⟨i.val, hi⟩]
      · simp only [ite_eq_right hi, dite_eq_right hi, variableCode_inr, source_variableCount]
  | inr x =>
      rw [constraintCode_inr]
      simp only [booleanScope, source_constraintCount, ite_eq_right (by omega : ¬c + x.val < c),
        hd, hm, FiniteDomainConstraints.scope, Equiv.symm_apply_apply, variableCode_inl,
        Nat.add_sub_cancel_left]

end PCP.Reduction.FiniteDomainSource
