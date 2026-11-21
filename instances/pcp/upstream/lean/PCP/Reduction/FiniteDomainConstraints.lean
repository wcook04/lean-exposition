/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.FiniteBooleanConstraints

/-!
# Finite-domain constraints as Boolean local constraints

Every source variable over `Fin a` is represented by `a` one-hot bits. A validity
constraint ensures exactly one selected symbol per variable. Each source relation
reads the relevant bit blocks and checks the same finite relation. Padding uses
one dummy block and a fixed common arity `max 1 d * a`; empty domains and zero-arity
relations are included. Satisfiability is preserved in both directions.
-/

namespace PCP.Reduction.FiniteDomainConstraints

open FiniteBooleanConstraints

variable {V C : Type*} {a d : ℕ}

/-- The Boolean positions of one finite-domain variable. -/
abbrev Variable (V : Type*) (a : ℕ) := (V ⊕ Unit) × Fin a

/-- Original relations and one one-hot validity constraint per source variable. -/
abbrev Constraint (V C : Type*) := C ⊕ V

def arity (a d : ℕ) : ℕ := max 1 d * a

def slot (i : Fin (max 1 d)) (j : Fin a) : Fin (arity a d) :=
  finProdFinEquiv (i, j)

def inputSlot (i : Fin d) (j : Fin a) : Fin (arity a d) :=
  slot (Fin.castLE (le_max_right 1 d) i) j

def firstSlot (j : Fin a) : Fin (arity a d) :=
  slot ⟨0, lt_of_lt_of_le (by decide) (le_max_left 1 d)⟩ j

/-- The explicit input positions, with a dummy block for any unused padding. -/
def scope (s : C → Fin d → V) : Constraint V C → Fin (arity a d) → Variable V a
  | .inl e, n =>
      let ij := finProdFinEquiv.symm n
      (if h : ij.1.val < d then .inl (s e ⟨ij.1.val, h⟩) else .inr (), ij.2)
  | .inr v, n => (.inl v, (finProdFinEquiv.symm n).2)

@[simp] theorem scope_inputSlot (s : C → Fin d → V) (e : C) (i : Fin d) (j : Fin a) :
    scope s (.inl e) (inputSlot i j) = (.inl (s e i), j) := by
  simp [scope, inputSlot, slot, i.isLt]

@[simp] theorem scope_firstSlot (s : C → Fin d → V) (v : V) (j : Fin a) :
    scope s (.inr v) (firstSlot (d := d) j) = (.inl v, j) := by
  simp [scope, firstSlot, slot]

/-- Source satisfiability over the actual finite alphabet. -/
def Holds (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V) (x : V → Fin a) : Prop :=
  ∀ e, R e (fun i => x (s e i)) = true

/-- One-hot truth tables use only bounded quantification over finite types. -/
def relation (R : C → (Fin d → Fin a) → Bool) :
    Constraint V C → Pattern (arity a d) → Bool
  | .inl e, p => decide (∃ x : Fin d → Fin a,
      R e x = true ∧ ∀ i j, p (inputSlot i j) = decide (x i = j))
  | .inr _, p => decide (∃ x : Fin a, ∀ j, p (firstSlot (d := d) j) = decide (x = j))

/-- Encode all source symbols in one-hot form; the unused dummy block is false. -/
def encodeAssignment (x : V → Fin a) : Variable V a → Bool
  | (.inl v, j) => decide (x v = j)
  | (.inr _, _) => false

/-- Original solutions satisfy both the relation constraints and every one-hot validity check. -/
theorem encodeAssignment_holds (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V)
    (x : V → Fin a) (hx : Holds R s x) :
    LocalHolds (relation R) (scope s) (encodeAssignment x) := by
  rintro (e | v)
  · apply decide_eq_true_iff.mpr
    refine ⟨fun i => x (s e i), hx e, ?_⟩
    intro i j
    dsimp only
    rw [scope_inputSlot]
    rfl
  · apply decide_eq_true_iff.mpr
    refine ⟨x v, ?_⟩
    intro j
    dsimp only
    rw [scope_firstSlot]
    rfl

/-- A valid one-hot block determines its represented source symbol uniquely. -/
theorem oneHot_injective (x y : Fin a)
    (h : ∀ j : Fin a, decide (x = j) = decide (y = j)) : x = y := by
  have hx := h x
  have hyx : y = x := by simpa using hx.symm
  exact hyx.symm

/-- A Boolean solution yields actual symbols, and each relation sees those same symbols. -/
theorem exists_symbols (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V)
    (b : Variable V a → Bool) (hb : LocalHolds (relation R) (scope s) b) :
    ∃ x : V → Fin a, Holds R s x := by
  have hv : ∀ v : V, ∃ x : Fin a, ∀ j, b (.inl v, j) = decide (x = j) := by
    intro v
    have h := of_decide_eq_true (hb (.inr v))
    simpa only [scope_firstSlot] using h
  choose x hx using hv
  refine ⟨x, fun e => ?_⟩
  obtain ⟨y, hy, hbits⟩ := of_decide_eq_true (hb (.inl e))
  have heq : y = fun i => x (s e i) := by
    funext i
    apply oneHot_injective
    intro j
    have hh := hbits i j
    dsimp only at hh
    rw [scope_inputSlot, hx] at hh
    exact hh.symm
  simpa only [heq] using hy

/-- Exact finite-domain to Boolean satisfiability preservation. -/
theorem satisfiable_iff (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V) :
    (∃ b, LocalHolds (relation R) (scope s) b) ↔ ∃ x : V → Fin a, Holds R s x := by
  constructor
  · rintro ⟨b, hb⟩
    exact exists_symbols R s b hb
  · rintro ⟨x, hx⟩
    exact ⟨encodeAssignment x, encodeAssignment_holds R s x hx⟩

/-- The complete finite-domain constraint graph, using the fixed-arity Boolean compiler. -/
def graph (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V) :=
  FiniteBooleanConstraints.graph (relation R) (scope s)

theorem colorable_iff (R : C → (Fin d → Fin a) → Bool) (s : C → Fin d → V) :
    (graph R s).Colorable 3 ↔ ∃ x : V → Fin a, Holds R s x :=
  (FiniteBooleanConstraints.colorable_iff _ _).trans (satisfiable_iff R s)

theorem card_variable [Fintype V] :
    Fintype.card (Variable V a) = (Fintype.card V + 1) * a := by
  simp [Variable]

theorem card_constraint [Fintype V] [Fintype C] :
    Fintype.card (Constraint V C) = Fintype.card C + Fintype.card V := by
  simp [Constraint]

end PCP.Reduction.FiniteDomainConstraints
