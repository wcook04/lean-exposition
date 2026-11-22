/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Not-all-equal clauses and three-coloring

The clause gadget is a triangle whose three vertices are joined to the three
Boolean inputs. It is colorable precisely when the inputs are not all equal.
The construction below shares one palette triangle and two vertices per variable.
No complexity certificate for the graph encoding is asserted here.
-/

namespace PCP.Reduction.NAEThreeColor

/-- False and true occupy the first two palette colors. -/
def boolColor (b : Bool) : Fin 3 := if b then 1 else 0

@[simp] theorem boolColor_inj (a b : Bool) : boolColor a = boolColor b ↔ a = b := by
  cases a <;> cases b <;> decide

@[simp] theorem boolColor_ne_two (b : Bool) : boolColor b ≠ 2 := by cases b <;> decide

/-- A ternary clause accepts exactly the nonconstant Boolean triples. -/
def NAE (b : Fin 3 → Bool) : Prop := b 0 ≠ b 1 ∨ b 1 ≠ b 2

/-- A fixed finite table supplies the clause triangle's colors. -/
def triangleWitness : Bool → Bool → Bool → Fin 3 → Fin 3
  | false, false, true => ![1, 2, 0]
  | true, true, false => ![0, 2, 1]
  | false, true, _ => ![1, 0, 2]
  | _, _, _ => ![0, 1, 2]

theorem triangleWitness_injective (a b c : Bool) :
    Function.Injective (triangleWitness a b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem triangleWitness_avoids (b : Fin 3 → Bool) (h : NAE b) (i : Fin 3) :
    triangleWitness (b 0) (b 1) (b 2) i ≠ boolColor (b i) := by
  unfold NAE at h
  fin_cases i <;> cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
    simp_all [triangleWitness, boolColor]

/-- The three-edge triangle gadget enforces not-all-equal, in both directions. -/
theorem triangle_iff (b : Fin 3 → Bool) :
    (∃ g : Fin 3 → Fin 3, Function.Injective g ∧ ∀ i, g i ≠ boolColor (b i)) ↔ NAE b := by
  constructor
  · rintro ⟨g, hg, havoid⟩
    by_contra h
    have hb : ∀ i, b i = b 0 := by
      have hn : b 0 = b 1 ∧ b 1 = b 2 := by simpa only [NAE, not_or, not_not] using h
      intro i
      fin_cases i <;> simp_all
    obtain ⟨i, hi⟩ := (Finite.surjective_of_injective hg) (boolColor (b 0))
    exact havoid i (hi.trans (congrArg boolColor (hb i)).symm)
  · intro h
    exact ⟨triangleWitness (b 0) (b 1) (b 2), triangleWitness_injective _ _ _,
      triangleWitness_avoids b h⟩

/-- A three-literal OR splits into two not-all-equal clauses with one fresh bit. -/
theorem or_iff_two_nae (a b c : Bool) :
    (a = true ∨ b = true ∨ c = true) ↔
      ∃ z : Bool, NAE ![a, b, z] ∧ NAE ![!z, c, false] := by
  unfold NAE
  cases a <;> cases b <;> cases c <;> decide

/-- Literals include the two fixed Boolean constants. -/
inductive Literal (V : Type*)
  | const : Bool → Literal V
  | var : V → Bool → Literal V
  deriving DecidableEq, Fintype

/-- The sign bit is false for a positive literal and true for its negation. -/
def Literal.eval {V : Type*} (a : V → Bool) : Literal V → Bool
  | .const b => b
  | .var v b => Bool.xor (a v) b

/-- One palette triangle, a complementary pair per variable, a triangle per clause. -/
abbrev Vertex (V C : Type*) := Fin 3 ⊕ ((V × Bool) ⊕ (C × Fin 3))

variable {V C : Type*}

def base (i : Fin 3) : Vertex V C := Sum.inl i
def variableVertex (v : V) (b : Bool) : Vertex V C := Sum.inr (Sum.inl (v, b))
def clauseVertex (e : C) (i : Fin 3) : Vertex V C := Sum.inr (Sum.inr (e, i))

def literalVertex : Literal V → Vertex V C
  | .const b => base (boolColor b)
  | .var v b => variableVertex v b

/-- Each edge is listed in one orientation; `graph` adds its reverse. -/
def direct (Q : C → Fin 3 → Literal V) : Vertex V C → Vertex V C → Prop
  | .inl i, .inl j => i ≠ j
  | .inr (.inl _), .inl i => i = 2
  | .inr (.inl (v, b)), .inr (.inl (w, d)) => v = w ∧ b ≠ d
  | .inr (.inr (e, i)), .inr (.inr (f, j)) => e = f ∧ i ≠ j
  | .inr (.inr (e, i)), x => x = literalVertex (Q e i)
  | _, _ => False

instance directDecidable [DecidableEq V] [DecidableEq C] (Q : C → Fin 3 → Literal V) :
    DecidableRel (direct Q) := by
  intro u w
  rcases u with a | (⟨v, b⟩ | ⟨e, i⟩) <;>
    rcases w with d | (⟨v', b'⟩ | ⟨e', i'⟩) <;> dsimp [direct] <;> infer_instance

/-- The explicit graph associated to the not-all-equal instance. -/
def graph (Q : C → Fin 3 → Literal V) : SimpleGraph (Vertex V C) :=
  SimpleGraph.fromRel (direct Q)

instance [DecidableEq V] [DecidableEq C] (Q : C → Fin 3 → Literal V) :
    DecidableRel (graph Q).Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

theorem card_vertex [Fintype V] [Fintype C] :
    Fintype.card (Vertex V C) = 3 + 2 * Fintype.card V + 3 * Fintype.card C := by
  simp only [Vertex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

/-- Extend a satisfying Boolean assignment to all gadget vertices. -/
def color (Q : C → Fin 3 → Literal V) (a : V → Bool) : Vertex V C → Fin 3
  | .inl i => i
  | .inr (.inl (v, b)) => boolColor (Bool.xor (a v) b)
  | .inr (.inr (e, i)) => triangleWitness
      ((Q e 0).eval a) ((Q e 1).eval a) ((Q e 2).eval a) i

@[simp] theorem color_literalVertex (Q : C → Fin 3 → Literal V) (a : V → Bool)
    (l : Literal V) : color Q a (literalVertex l) = boolColor (l.eval a) := by
  cases l <;> rfl

private theorem color_direct (Q : C → Fin 3 → Literal V) (a : V → Bool)
    (ha : ∀ e, NAE (fun i => (Q e i).eval a)) (u w : Vertex V C)
    (h : direct Q u w) : color Q a u ≠ color Q a w := by
  rcases u with k | (⟨v, b⟩ | ⟨e, i⟩) <;>
    rcases w with d | (⟨v', b'⟩ | ⟨e', i'⟩)
  · exact h
  · exact h.elim
  · exact h.elim
  · change d = 2 at h
    subst d
    exact boolColor_ne_two _
  · rcases h with ⟨rfl, h⟩
    change boolColor (Bool.xor (a v) b) ≠ boolColor (Bool.xor (a v) b')
    cases a v <;> cases b <;> cases b' <;> simp_all [boolColor]
  · exact h.elim
  · change base d = literalVertex (Q e i) at h
    change _ ≠ color Q a (base d)
    rw [h, color_literalVertex]
    exact triangleWitness_avoids _ (ha e) i
  · change variableVertex v' b' = literalVertex (Q e i) at h
    change _ ≠ color Q a (variableVertex v' b')
    rw [h, color_literalVertex]
    exact triangleWitness_avoids _ (ha e) i
  · rcases h with ⟨rfl, h⟩
    exact fun he => h (triangleWitness_injective _ _ _ he)

/-- Every satisfying assignment supplies an explicit proper three-coloring. -/
def coloring (Q : C → Fin 3 → Literal V) (a : V → Bool)
    (ha : ∀ e, NAE (fun i => (Q e i).eval a)) : (graph Q).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk (color Q a) (by
    intro u w h
    rcases h.2 with h | h
    · exact color_direct Q a ha u w h
    · exact (color_direct Q a ha w u h).symm)

theorem adj_base (Q : C → Fin 3 → Literal V) {i j : Fin 3} (h : i ≠ j) :
    (graph Q).Adj (base i) (base j) := by
  simp [graph, SimpleGraph.fromRel_adj, base, direct, h]

theorem adj_variable_base (Q : C → Fin 3 → Literal V) (v : V) (b : Bool) :
    (graph Q).Adj (variableVertex v b) (base 2) := by
  simp [graph, SimpleGraph.fromRel_adj, base, variableVertex, direct]

theorem adj_variable_pair (Q : C → Fin 3 → Literal V) (v : V) :
    (graph Q).Adj (variableVertex v false) (variableVertex v true) := by
  simp [graph, SimpleGraph.fromRel_adj, variableVertex, direct]

theorem adj_clause (Q : C → Fin 3 → Literal V) (e : C) {i j : Fin 3} (h : i ≠ j) :
    (graph Q).Adj (clauseVertex e i) (clauseVertex e j) := by
  simp [graph, SimpleGraph.fromRel_adj, clauseVertex, direct, h]

theorem adj_clause_literal (Q : C → Fin 3 → Literal V) (e : C) (i : Fin 3) :
    (graph Q).Adj (clauseVertex e i) (literalVertex (Q e i)) := by
  cases h : Q e i <;>
    simp [graph, SimpleGraph.fromRel_adj, clauseVertex, literalVertex, direct, base,
      variableVertex, h]

/-- Any proper coloring assigns a permutation of the three colors to the palette. -/
noncomputable def palette (Q : C → Fin 3 → Literal V) (f : (graph Q).Coloring (Fin 3)) :
    Fin 3 ≃ Fin 3 := by
  have hi : Function.Injective (fun i => f (base i)) := by
    intro i j he
    by_contra hn
    exact f.valid (adj_base Q hn) he
  exact Equiv.ofBijective _ ⟨hi, Finite.surjective_of_injective hi⟩

/-- Relabel all colors so the palette vertices have their literal numeric colors. -/
noncomputable def normalize (Q : C → Fin 3 → Literal V) (f : (graph Q).Coloring (Fin 3)) :
    (graph Q).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk (fun v => (palette Q f).symm (f v))
    (fun h he => f.valid h ((palette Q f).symm.injective he))

@[simp] theorem normalize_base (Q : C → Fin 3 → Literal V)
    (f : (graph Q).Coloring (Fin 3)) (i : Fin 3) : normalize Q f (base i) = i :=
  (palette Q f).symm_apply_apply i

private theorem decode_pair (x y : Fin 3) (hx : x ≠ 2) (hy : y ≠ 2) (hxy : x ≠ y) :
    x = boolColor (decide (x = 1)) ∧ y = boolColor (!decide (x = 1)) := by
  fin_cases x <;> fin_cases y <;> simp_all [boolColor]

/-- Reading the positive variable vertex recovers a satisfying assignment. -/
theorem exists_assignment_of_coloring (Q : C → Fin 3 → Literal V)
    (f : (graph Q).Coloring (Fin 3)) : ∃ a : V → Bool, ∀ e, NAE (fun i => (Q e i).eval a) := by
  let g := normalize Q f
  let a : V → Bool := fun v => decide (g (variableVertex v false) = 1)
  have hv (v : V) (b : Bool) : g (variableVertex v b) = boolColor (Bool.xor (a v) b) := by
    have hn (d : Bool) : g (variableVertex v d) ≠ 2 := by
      have h := g.valid (adj_variable_base Q v d)
      simpa only [g, normalize_base] using h
    have hpair := decode_pair _ _ (hn false) (hn true) (g.valid (adj_variable_pair Q v))
    cases b
    · simpa only [Bool.xor_false] using hpair.1
    · simpa only [Bool.xor_true] using hpair.2
  have hl (l : Literal V) : g (literalVertex l) = boolColor (l.eval a) := by
    cases l with
    | const b => exact normalize_base Q f (boolColor b)
    | var v b => exact hv v b
  refine ⟨a, fun e => (triangle_iff _).mp ?_⟩
  refine ⟨fun i => g (clauseVertex e i), ?_, ?_⟩
  · intro i j he
    by_contra hn
    exact g.valid (adj_clause Q e hn) he
  · intro i
    rw [← hl]
    exact g.valid (adj_clause_literal Q e i)

/-- The explicit graph is three-colorable exactly for satisfiable NAE instances. -/
theorem colorable_iff (Q : C → Fin 3 → Literal V) :
    (graph Q).Colorable 3 ↔ ∃ a : V → Bool, ∀ e, NAE (fun i => (Q e i).eval a) := by
  constructor
  · rintro ⟨f⟩
    exact exists_assignment_of_coloring Q f
  · rintro ⟨a, ha⟩
    exact ⟨coloring Q a ha⟩

end PCP.Reduction.NAEThreeColor
