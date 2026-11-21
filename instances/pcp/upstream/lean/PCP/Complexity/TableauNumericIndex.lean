/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.TableauIndex
import PCP.Complexity.NPCellConstraints

/-!
# Numeric forms of the structural tableau codecs

These identities expose the arithmetic used by the graph-source generator.
Only the stack enumeration is fixed by the source machine; time, cell, witness,
and boundary indices use the explicit structural codecs already proved bijective.
-/

namespace PCP.Machine.TableauNumericIndex

open Turing TM2Locality TableauConstraints TableauIndex

variable {tm : FinTM2} {k T B W : ℕ} (eK : tm.K ≃ Fin k)

def sites (k B : ℕ) : ℕ := 1 + k * B
def variableCount (k T B : ℕ) : ℕ := (T + 1) * sites k B + 1
def links (k window T : ℕ) : ℕ := (T + 1) * (k * window)
def boundaryOffset (k window T B : ℕ) : ℕ := 1 + links k window T + T + T * (k * B)
def constraints (k window T B : ℕ) : ℕ := boundaryOffset k window T B + 2 * sites k B

def prefixAddress (k B t : ℕ) : ℕ := t * sites k B

def cell (k T B t stack j : ℕ) : ℕ :=
  if j < B then t * sites k B + 1 + stack * B + j else (T + 1) * sites k B

@[simp] theorem unitCode_val (u : Unit) : (unitCode u).val = 0 := by
  have := (unitCode u).isLt
  omega

@[simp] theorem site_control : (siteCode eK B (.inl ())).val = 0 := by
  simp [siteCode, finSumFinEquiv]

@[simp] theorem site_cell (s : tm.K) (j : Fin B) :
    (siteCode eK B (.inr (s, j))).val = 1 + (eK s).val * B + j.val := by
  simp [siteCode, finSumFinEquiv, finProdFinEquiv]
  ring

@[simp] theorem variable_real (t : Fin (T + 1)) (s : Site tm B) :
    (variableCode eK T B (.inl (t, s))).val = t.val * sites k B + (siteCode eK B s).val := by
  simp [variableCode, finSumFinEquiv, finProdFinEquiv, sites, Nat.mul_comm, Nat.add_comm]

@[simp] theorem variable_blank :
    (variableCode eK T B (.inr ())).val = (T + 1) * sites k B := by
  simp [variableCode, finSumFinEquiv, sites]

@[simp] theorem variable_prefix (t : Fin (T + 1)) :
    (variableCode eK T B (prefixVariable t)).val = prefixAddress k B t.val := by
  simp [prefixVariable, prefixAddress]

@[simp] theorem variable_cell (t : Fin (T + 1)) (s : tm.K) (j : ℕ) :
    (variableCode eK T B (cellVariable t s j)).val = cell k T B t.val (eK s).val j := by
  unfold cellVariable cell
  split_ifs with hj <;> simp [Nat.add_assoc]

@[simp] theorem constraint_blank (u : Unit) :
    (constraintCode eK T B (.inl u)).val = 0 := by
  simp [constraintCode, finSumFinEquiv]

@[simp] theorem constraint_link (t : Fin (T + 1)) (s : tm.K) (j : Fin (machineWindow tm)) :
    (constraintCode eK T B (.inr (.inl (t, s, j)))).val =
      1 + t.val * (k * machineWindow tm) + (eK s).val * machineWindow tm + j.val := by
  simp [constraintCode, linkCode, finSumFinEquiv, finProdFinEquiv]
  ring

@[simp] theorem constraint_control (t : Fin T) :
    (constraintCode eK T B (.inr (.inr (.inl t)))).val =
      1 + links k (machineWindow tm) T + t.val := by
  simp [constraintCode, finSumFinEquiv, links]
  omega

@[simp] theorem constraint_cell (t : Fin T) (s : tm.K) (j : Fin B) :
    (constraintCode eK T B (.inr (.inr (.inr (.inl (t, s, j)))))).val =
      1 + links k (machineWindow tm) T + T + t.val * (k * B) + (eK s).val * B + j.val := by
  simp [constraintCode, cellCode, finSumFinEquiv, finProdFinEquiv, links]
  ring

@[simp] theorem constraint_boundary (b : Bool) (s : Site tm B) :
    (constraintCode eK T B (.inr (.inr (.inr (.inr (b, s)))))).val =
      boundaryOffset k (machineWindow tm) T B + b.toNat * sites k B + (siteCode eK B s).val := by
  cases b <;> simp [constraintCode, boundaryCode, finSumFinEquiv, finProdFinEquiv,
    PCP.Reduction.ThreeSATGraphEncoding.boolCode, links, sites, boundaryOffset] <;> omega

@[simp] theorem withWitness_original (c : TableauConstraints.Constraint tm T B) :
    (withWitnessCode eK T B W (.inl c)).val = (constraintCode eK T B c).val := by
  simp [withWitnessCode, finSumFinEquiv]

@[simp] theorem withWitness_extra (j : Fin W) :
    (withWitnessCode eK T B W (.inr j)).val = constraints k (machineWindow tm) T B + j.val := by
  simp [withWitnessCode, finSumFinEquiv, constraints, boundaryOffset, links, sites]


/-- Arithmetic scope lookup for all tableau and witness constraint kinds. -/
def scope (k window stack₀ T B n e i : ℕ) : ℕ :=
  if e = 0 then (T + 1) * sites k B else
  if e < 1 + links k window T then
    let z := e - 1
    if i = 0 then prefixAddress k B (z / (k * window))
    else cell k T B (z / (k * window)) (z % (k * window) / window) (z % window)
  else if e < 1 + links k window T + T then
    let t := e - (1 + links k window T)
    prefixAddress k B (if i = 0 then t else t + 1)
  else if e < boundaryOffset k window T B then
    let z := e - (1 + links k window T + T)
    let t := z / (k * B)
    let stack := z % (k * B) / B
    let j := z % B
    if i = 0 then prefixAddress k B t else
    if i = 1 then cell k T B (t + 1) stack j
    else cell k T B t stack (window + (j - (i - 2)))
  else if e < constraints k window T B then
    let z := e - boundaryOffset k window T B
    let t := if z / sites k B = 0 then 0 else T
    let s := z % sites k B
    if s = 0 then prefixAddress k B t
    else cell k T B t ((s - 1) / B) ((s - 1) % B)
  else
    cell k T B 0 stack₀
      (n + 1 + (e - constraints k window T B) + (if i = 0 then 0 else 1))

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

/-- Prefix-link constraints decode into the exact time, stack, and prefix-cell coordinates. -/
theorem scope_link (window stack₀ n i : ℕ) (t : Fin (T + 1)) (stack : Fin k)
    (j : Fin window) :
    scope k window stack₀ T B n (1 + t.val * (k * window) + stack.val * window + j.val) i =
      if i = 0 then prefixAddress k B t.val else cell k T B t.val stack.val j.val := by
  have hb := triple_bound (T + 1) k t.val stack.val j.val window t.isLt stack.isLt j.isLt
  have hd := triple_decode k t.val stack.val j.val window stack.isLt j.isLt
  have h0 : 1 + t.val * (k * window) + stack.val * window + j.val ≠ 0 := by omega
  have hlt : 1 + t.val * (k * window) + stack.val * window + j.val <
      1 + links k window T := by dsimp [links]; omega
  simp only [scope, ite_eq_right h0, ite_eq_left hlt]
  have heq : 1 + t.val * (k * window) + stack.val * window + j.val - 1 =
      t.val * (k * window) + stack.val * window + j.val := by omega
  rw [heq, hd.1, hd.2.1, hd.2.2]

/-- The control-step scope advances the arithmetic row index by one. -/
theorem scope_control (window stack₀ n i : ℕ) (t : Fin T) :
    scope k window stack₀ T B n (1 + links k window T + t.val) i =
      prefixAddress k B (if i = 0 then t.val else t.val + 1) := by
  have h0 : 1 + links k window T + t.val ≠ 0 := by omega
  have hlink : ¬1 + links k window T + t.val < 1 + links k window T := by omega
  have hlt : 1 + links k window T + t.val < 1 + links k window T + T := by omega
  simp only [scope, ite_eq_right h0, ite_eq_right hlink, ite_eq_left hlt, Nat.add_sub_cancel_left]

/-- Every cell-step candidate retains the concrete truncated-subtraction address. -/
theorem scope_cell (window stack₀ n i : ℕ) (t : Fin T) (stack : Fin k) (j : Fin B) :
    scope k window stack₀ T B n
        (1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val) i =
      if i = 0 then prefixAddress k B t.val else
      if i = 1 then cell k T B (t.val + 1) stack.val j.val else
        cell k T B t.val stack.val (window + (j.val - (i - 2))) := by
  have hb := triple_bound T k t.val stack.val j.val B t.isLt stack.isLt j.isLt
  have hd := triple_decode k t.val stack.val j.val B stack.isLt j.isLt
  have h0 : 1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val ≠ 0 := by omega
  have hlink : ¬1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val <
      1 + links k window T := by omega
  have hcontrol : ¬1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val <
      1 + links k window T + T := by omega
  have hlt : 1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val <
      boundaryOffset k window T B := by dsimp [boundaryOffset]; omega
  simp only [scope, ite_eq_right h0, ite_eq_right hlink, ite_eq_right hcontrol, ite_eq_left hlt]
  have heq : 1 + links k window T + T + t.val * (k * B) + stack.val * B + j.val -
      (1 + links k window T + T) = t.val * (k * B) + stack.val * B + j.val := by omega
  rw [heq, hd.1, hd.2.1, hd.2.2]


/-- Boundary scopes select the initial or final row and decode its site arithmetically. -/
theorem scope_boundary (window stack₀ n i : ℕ) (b : Bool) (s : Fin (sites k B)) :
    scope k window stack₀ T B n
        (boundaryOffset k window T B + b.toNat * sites k B + s.val) i =
      if s.val = 0 then prefixAddress k B (if b then T else 0)
      else cell k T B (if b then T else 0) ((s.val - 1) / B) ((s.val - 1) % B) := by
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
  simp only [scope, ite_eq_right h0, ite_eq_right hlink, ite_eq_right hcontrol, ite_eq_right hstep, ite_eq_left hlt]
  have heq : boundaryOffset k window T B + b.toNat * sites k B + s.val -
      boundaryOffset k window T B = b.toNat * sites k B + s.val := by omega
  rw [heq, hd.1, hd.2]
  cases b <;> rfl

/-- The appended witness scopes inspect adjacent input-stack positions. -/
theorem scope_extra (window stack₀ n i j : ℕ) :
    scope k window stack₀ T B n (constraints k window T B + j) i =
      cell k T B 0 stack₀ (n + 1 + j + if i = 0 then 0 else 1) := by
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
  simp only [scope, ite_eq_right h0, ite_eq_right hlink, ite_eq_right hcontrol, ite_eq_right hstep, ite_eq_right hbound,
    Nat.add_sub_cancel_left]

/-- Arithmetic scope generation equals the structural NP tableau scope at every actual index. -/
theorem scope_correct (x : List Bool) (e : NPCellConstraints.Constraint tm T B W)
    (i : Fin (TableauConstraints.arity tm)) :
    scope k (machineWindow tm) (eK tm.k₀).val T B x.length
        (withWitnessCode eK T B W e).val i.val =
      (variableCode eK T B (NPCellConstraints.scope x e i)).val := by
  rcases e with c | j
  · rcases c with _ | ⟨t, s, j⟩ | t | ⟨t, s, j⟩ | ⟨b, _ | ⟨s, j⟩⟩
    · simp only [withWitness_original, constraint_blank, scope, ite_true,
        NPCellConstraints.scope, TableauConstraints.scope, variable_blank]
    · simp only [withWitness_original, constraint_link, scope_link, NPCellConstraints.scope,
        TableauConstraints.scope]
      by_cases hi : i.val = 0 <;> simp only [hi, ite_true, ite_false, variable_prefix, variable_cell]
    · simp only [withWitness_original, constraint_control, scope_control,
        NPCellConstraints.scope, TableauConstraints.scope]
      by_cases hi : i.val = 0 <;>
        simp only [hi, ite_true, ite_false, variable_prefix, Fin.val_castSucc, Fin.val_succ]
    · simp only [withWitness_original, constraint_cell, scope_cell, NPCellConstraints.scope,
        TableauConstraints.scope]
      by_cases h0 : i.val = 0 <;> by_cases h1 : i.val = 1 <;>
        simp only [h0, h1, Nat.reduceEqDiff, ite_true, ite_false, variable_prefix, variable_cell,
          Fin.val_castSucc, Fin.val_succ]
    · rw [withWitness_original, constraint_boundary]
      rw [scope_boundary _ _ _ _ b (siteCode eK B (.inl ()))]
      simp only [site_control, NPCellConstraints.scope, TableauConstraints.scope,
        variable_prefix]
      cases b <;> rfl
    · rw [withWitness_original, constraint_boundary]
      rw [scope_boundary _ _ _ _ b (siteCode eK B (.inr (s, j)))]
      simp only [site_cell, NPCellConstraints.scope, TableauConstraints.scope, variable_cell]
      have hsite : 1 + (eK s).val * B + j.val ≠ 0 := by omega
      have hs : 1 + (eK s).val * B + j.val - 1 = (eK s).val * B + j.val := by omega
      rw [ite_eq_right hsite, hs]
      have hd := pair_decode B (eK s).val j.val j.isLt
      rw [hd.1, hd.2]
      cases b <;> rfl
  · rw [withWitness_extra, scope_extra]
    simp only [NPCellConstraints.scope]
    by_cases hi : i.val = 0 <;>
      simp only [hi, ite_true, ite_false, variable_cell, Fin.val_zero, Nat.add_zero, Nat.add_assoc]

end PCP.Machine.TableauNumericIndex
