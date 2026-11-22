/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.ThreeSATToColor

/-!
# Fixed-arity Boolean constraints to ternary clauses and three-coloring

For each local relation and each Boolean input pattern, a chain records whether
the actual input differs from that pattern. The last clause permits the pattern
exactly when the supplied relation accepts it. Each chain consists solely of
three-literal clauses and has a canonical extension for every input assignment.

The construction has `2^k * (3*k+2)` clauses per arity-`k` constraint. This is
linear in the number of constraints for fixed `k`; it is not polynomial in an
unbounded arity. In the machine-tableau application, the local prefix arity is
fixed by the source machine. The whole tableau is wired in `NPThreeColor`; the
certified executable reduction is `NPThreeColorRuntime`.
-/

namespace PCP.Reduction.FiniteBooleanConstraints

open NAEThreeColor

variable {V C W : Type*} {k : ℕ}

/-- Negation preserves the source variable and flips its literal sign. -/
def negate : Literal W → Literal W
  | .const b => .const (!b)
  | .var v b => .var v (!b)

@[simp] theorem eval_negate (a : W → Bool) (l : Literal W) :
    (negate l).eval a = !(l.eval a) := by
  cases l with
  | const b => rfl
  | var v b => cases ha : a v <;> cases b <;> simp [negate, Literal.eval, ha]

def ClauseHolds (q : Fin 3 → Literal W) (a : W → Bool) : Prop :=
  (q 0).eval a = true ∨ (q 1).eval a = true ∨ (q 2).eval a = true

/-- Three standard clauses enforce exactly one Boolean OR gate. -/
def orGate (z x y : Literal W) : Fin 3 → Fin 3 → Literal W :=
  ![![z, negate x, .const false], ![z, negate y, .const false], ![negate z, x, y]]

theorem orGate_iff (z x y : Literal W) (a : W → Bool) :
    (∀ j, ClauseHolds (orGate z x y j) a) ↔ z.eval a = (x.eval a || y.eval a) := by
  have hfin : (∀ j, ClauseHolds (orGate z x y j) a) ↔
      ClauseHolds (orGate z x y 0) a ∧ ClauseHolds (orGate z x y 1) a ∧
        ClauseHolds (orGate z x y 2) a := by
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2⟩
    · rintro ⟨h0, h1, h2⟩ j
      fin_cases j <;> assumption
  rw [hfin]
  change ((z.eval a = true ∨ (negate x).eval a = true ∨ false = true) ∧
    (z.eval a = true ∨ (negate y).eval a = true ∨ false = true) ∧
    ((negate z).eval a = true ∨ x.eval a = true ∨ y.eval a = true)) ↔ _
  simp only [eval_negate]
  cases z.eval a <;> cases x.eval a <;> cases y.eval a <;> decide

/-- The input patterns range over exactly `2^k` choices. -/
abbrev Pattern (k : ℕ) := Fin k → Bool

/-- A flag after each of the `k` comparison bits, including the empty prefix. -/
abbrev Aux (C : Type*) (k : ℕ) := C × Pattern k × Fin (k + 1)

abbrev Variable (V C : Type*) (k : ℕ) := V ⊕ Aux C k

/-- Three gate clauses per comparison, plus the initial and final unit clauses. -/
abbrev Clause (C : Type*) (k : ℕ) := C × Pattern k × ((Fin k × Fin 3) ⊕ Fin 2)

def flagLiteral (e : C) (p : Pattern k) (i : Fin (k + 1)) : Literal (Variable V C k) :=
  .var (.inr (e, p, i)) false

def differenceLiteral (scope : C → Fin k → V) (e : C) (p : Pattern k) (i : Fin k) :
    Literal (Variable V C k) := .var (.inl (scope e i)) (p i)

/-- The actual three-literal formula for the supplied family of local relations. -/
def clauses (relation : C → Pattern k → Bool) (scope : C → Fin k → V) :
    Clause C k → Fin 3 → Literal (Variable V C k)
  | (e, p, .inl (i, j)) => orGate (flagLiteral e p i.succ)
      (flagLiteral e p i.castSucc) (differenceLiteral scope e p i) j
  | (e, p, .inr j) => if j.val = 0 then
      ![negate (flagLiteral e p 0), .const false, .const false]
    else ![.const (relation e p), flagLiteral e p (Fin.last k), .const false]

/-- Prefix comparison, executable without enumerating the whole assignment space. -/
def flag (x p : Pattern k) (n : ℕ) : Bool :=
  (List.range n).any (fun j => if hj : j < k then Bool.xor (x ⟨j, hj⟩) (p ⟨j, hj⟩) else false)

@[simp] theorem flag_zero (x p : Pattern k) : flag x p 0 = false := rfl

theorem flag_succ (x p : Pattern k) (i : Fin k) :
    flag x p (i.val + 1) = (flag x p i.val || Bool.xor (x i) (p i)) := by
  simp [flag, List.range_succ, List.any_append, i.isLt]

theorem flag_eq_false_iff (x p : Pattern k) : flag x p k = false ↔ x = p := by
  constructor
  · intro h
    funext i
    have hi := List.any_eq_false.mp h i.val (List.mem_range.mpr i.isLt)
    simp only [dite_eq_left i.isLt] at hi
    change ¬ Bool.xor (x i) (p i) = true at hi
    cases hx : x i <;> cases hp : p i <;> simp_all
  · rintro rfl
    simp [flag]

theorem flag_eq_true_iff (x p : Pattern k) : flag x p k = true ↔ x ≠ p := by
  rw [← Bool.not_eq_false, flag_eq_false_iff]

def LocalHolds (relation : C → Pattern k → Bool) (scope : C → Fin k → V)
    (a : V → Bool) : Prop := ∀ e, relation e (fun i => a (scope e i)) = true

private theorem pattern_spec (relation : C → Pattern k → Bool) (scope : C → Fin k → V)
    (a : Variable V C k → Bool) (e : C) (p : Pattern k) :
    (∀ j, ClauseHolds (clauses relation scope (e, p, j)) a) ↔
      a (.inr (e, p, 0)) = false ∧
      (∀ i : Fin k, a (.inr (e, p, i.succ)) =
        (a (.inr (e, p, i.castSucc)) || Bool.xor (a (.inl (scope e i))) (p i))) ∧
      (relation e p = true ∨ a (.inr (e, p, Fin.last k)) = true) := by
  constructor
  · intro h
    have hzero := h (.inr 0)
    have hlast := h (.inr 1)
    refine ⟨?_, ?_, ?_⟩
    · simpa [clauses, ClauseHolds, flagLiteral, negate, Literal.eval] using hzero
    · intro i
      have hg := (orGate_iff (flagLiteral e p i.succ) (flagLiteral e p i.castSucc)
        (differenceLiteral scope e p i) a).mp (fun j => h (.inl (i, j)))
      simpa [flagLiteral, differenceLiteral, Literal.eval] using hg
    · simpa [clauses, ClauseHolds, flagLiteral, Literal.eval] using hlast
  · rintro ⟨hzero, hstep, hlast⟩ (⟨i, j⟩ | j)
    · apply (orGate_iff (flagLiteral e p i.succ) (flagLiteral e p i.castSucc)
        (differenceLiteral scope e p i) a).mpr ?_ j
      simpa [flagLiteral, differenceLiteral, Literal.eval] using hstep i
    · fin_cases j
      · simpa [clauses, ClauseHolds, flagLiteral, negate, Literal.eval] using hzero
      · simpa [clauses, ClauseHolds, flagLiteral, Literal.eval] using hlast

private theorem chain_eq_flag (x p : Pattern k) (z : Fin (k + 1) → Bool)
    (hzero : z 0 = false)
    (hstep : ∀ i : Fin k, z i.succ = (z i.castSucc || Bool.xor (x i) (p i)))
    (i : Fin (k + 1)) : z i = flag x p i.val := by
  obtain ⟨j, hj⟩ := i
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have h := hstep ⟨j, by omega⟩
      change z ⟨j + 1, hj⟩ = (z ⟨j, by omega⟩ || Bool.xor (x ⟨j, by omega⟩)
        (p ⟨j, by omega⟩)) at h
      rw [h, ih (by omega)]
      exact (flag_succ x p ⟨j, by omega⟩).symm

/-- Every satisfying ternary assignment restricts to a solution of the original relations. -/
theorem satisfies_implies (relation : C → Pattern k → Bool) (scope : C → Fin k → V)
    (a : Variable V C k → Bool) (ha : ThreeSATToColor.Satisfies (clauses relation scope) a) :
    LocalHolds relation scope (a ∘ Sum.inl) := by
  intro e
  let p : Pattern k := fun i => a (.inl (scope e i))
  obtain ⟨hz, hs, hf⟩ := (pattern_spec relation scope a e p).mp (fun j => ha (e, p, j))
  have heq := chain_eq_flag p p (fun i => a (.inr (e, p, i))) hz hs (Fin.last k)
  have hfalse : a (.inr (e, p, Fin.last k)) = false :=
    heq.trans ((flag_eq_false_iff p p).mpr rfl)
  exact hf.resolve_right (by rw [hfalse]; decide)

/-- The unique prefix-comparison values supply all auxiliary bits explicitly. -/
def extend (scope : C → Fin k → V) (a : V → Bool) : Variable V C k → Bool :=
  Sum.elim a (fun epn => flag (fun i => a (scope epn.1 i)) epn.2.1 epn.2.2.val)

/-- Every original solution extends to the constructed ternary clauses. -/
theorem extend_satisfies (relation : C → Pattern k → Bool) (scope : C → Fin k → V)
    (a : V → Bool) (ha : LocalHolds relation scope a) :
    ThreeSATToColor.Satisfies (clauses relation scope) (extend scope a) := by
  rintro ⟨e, p, j⟩
  apply (pattern_spec relation scope (extend scope a) e p).mpr ?_ j
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    exact flag_succ (fun i => a (scope e i)) p i
  · by_cases hp : (fun i => a (scope e i)) = p
    · exact Or.inl (hp ▸ ha e)
    · exact Or.inr ((flag_eq_true_iff _ p).mpr hp)

/-- Exact satisfiability preservation, including repeated scopes and arity zero. -/
theorem satisfiable_iff (relation : C → Pattern k → Bool) (scope : C → Fin k → V) :
    (∃ a, ThreeSATToColor.Satisfies (clauses relation scope) a) ↔
      ∃ a : V → Bool, LocalHolds relation scope a := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a ∘ Sum.inl, satisfies_implies relation scope a ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨extend scope a, extend_satisfies relation scope a ha⟩

/-- The concrete three-color graph for a family of fixed-arity Boolean constraints. -/
def graph (relation : C → Pattern k → Bool) (scope : C → Fin k → V) :=
  ThreeSATToColor.graph (clauses relation scope)

theorem colorable_iff (relation : C → Pattern k → Bool) (scope : C → Fin k → V) :
    (graph relation scope).Colorable 3 ↔ ∃ a : V → Bool, LocalHolds relation scope a :=
  (ThreeSATToColor.colorable_iff _).trans (satisfiable_iff relation scope)

theorem card_variable [Fintype V] [Fintype C] :
    Fintype.card (Variable V C k) =
      Fintype.card V + Fintype.card C * 2 ^ k * (k + 1) := by
  simp [Variable, Aux, Pattern, mul_assoc]

theorem card_clause [Fintype C] :
    Fintype.card (Clause C k) = Fintype.card C * 2 ^ k * (3 * k + 2) := by
  simp [Clause, Pattern, mul_assoc, mul_comm]

end PCP.Reduction.FiniteBooleanConstraints
