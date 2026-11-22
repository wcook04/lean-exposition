/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.NAEThreeColor

/-!
# Explicit three-literal satisfiability to three-colorability

Each OR clause becomes two not-all-equal clauses with one private variable.
The triangle construction then gives a graph with `3 + 2*variables + 8*clauses`
vertices. The graph and its adjacency decision are computable. Equivalence of
satisfiability and three-colorability is proved here. The numeric encoding is in
`ThreeSATGraphEncoding`; the certified executable reduction is `NPThreeColorRuntime`.
-/

namespace PCP.Reduction.ThreeSATToColor

open NAEThreeColor

variable {V W C : Type*}

/-- Rename a literal's variable while retaining its sign or constant. -/
def mapLiteral (f : V → W) : Literal V → Literal W
  | .const b => .const b
  | .var v b => .var (f v) b

@[simp] theorem eval_mapLiteral (f : V → W) (a : W → Bool) (l : Literal V) :
    (mapLiteral f l).eval a = l.eval (a ∘ f) := by cases l <;> rfl

/-- Every source clause is the disjunction of its three literal values. -/
def Satisfies (Q : C → Fin 3 → Literal V) (a : V → Bool) : Prop :=
  ∀ e, (Q e 0).eval a = true ∨ (Q e 1).eval a = true ∨ (Q e 2).eval a = true

/-- One new variable per original clause supplies two ternary NAE clauses. -/
def splitClauses (Q : C → Fin 3 → Literal V) : C × Bool → Fin 3 → Literal (V ⊕ C)
  | (e, false) => ![mapLiteral Sum.inl (Q e 0), mapLiteral Sum.inl (Q e 1), .var (.inr e) false]
  | (e, true) => ![.var (.inr e) true, mapLiteral Sum.inl (Q e 2), .const false]

theorem eval_splitClauses_false (Q : C → Fin 3 → Literal V)
    (a : V ⊕ C → Bool) (e : C) :
    (fun i => (splitClauses Q (e, false) i).eval a) =
      ![(Q e 0).eval (a ∘ Sum.inl), (Q e 1).eval (a ∘ Sum.inl), a (.inr e)] := by
  funext i
  fin_cases i
  · exact eval_mapLiteral Sum.inl a (Q e 0)
  · exact eval_mapLiteral Sum.inl a (Q e 1)
  · exact Bool.xor_false _

theorem eval_splitClauses_true (Q : C → Fin 3 → Literal V)
    (a : V ⊕ C → Bool) (e : C) :
    (fun i => (splitClauses Q (e, true) i).eval a) =
      ![!a (.inr e), (Q e 2).eval (a ∘ Sum.inl), false] := by
  funext i
  fin_cases i
  · exact Bool.xor_true _
  · exact eval_mapLiteral Sum.inl a (Q e 2)
  · rfl

/-- Splitting clauses preserves satisfiability in both directions. -/
theorem splitClauses_satisfiable_iff (Q : C → Fin 3 → Literal V) :
    (∃ a : V ⊕ C → Bool, ∀ e, NAE (fun i => (splitClauses Q e i).eval a)) ↔
      ∃ a : V → Bool, Satisfies Q a := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ∘ Sum.inl, fun e => (or_iff_two_nae _ _ _).mpr ?_⟩
    refine ⟨a (.inr e), ?_, ?_⟩
    · simpa only [eval_splitClauses_false] using ha (e, false)
    · simpa only [eval_splitClauses_true] using ha (e, true)
  · rintro ⟨a, ha⟩
    have h : ∀ e, ∃ z : Bool,
        NAE ![(Q e 0).eval a, (Q e 1).eval a, z] ∧
          NAE ![!z, (Q e 2).eval a, false] := fun e => (or_iff_two_nae _ _ _).mp (ha e)
    choose z hz using h
    refine ⟨Sum.elim a z, ?_⟩
    rintro ⟨e, b⟩
    cases b
    · simpa only [eval_splitClauses_false, Sum.elim_inr, Function.comp_def, Sum.elim_inl]
        using (hz e).1
    · simpa only [eval_splitClauses_true, Sum.elim_inr, Function.comp_def, Sum.elim_inl]
        using (hz e).2

/-- The reduced graph, including palette, source variables and private clause gadgets. -/
def graph (Q : C → Fin 3 → Literal V) : SimpleGraph (NAEThreeColor.Vertex (V ⊕ C) (C × Bool)) :=
  NAEThreeColor.graph (splitClauses Q)

instance [DecidableEq V] [DecidableEq C] (Q : C → Fin 3 → Literal V) :
    DecidableRel (graph Q).Adj :=
  inferInstanceAs (DecidableRel (NAEThreeColor.graph (splitClauses Q)).Adj)

/-- The standard semantic reduction, for arbitrary source clauses including constants. -/
theorem colorable_iff (Q : C → Fin 3 → Literal V) :
    (graph Q).Colorable 3 ↔ ∃ a, Satisfies Q a :=
  (NAEThreeColor.colorable_iff (splitClauses Q)).trans (splitClauses_satisfiable_iff Q)

/-- Each clause adds one variable pair and two triangles, hence eight vertices. -/
theorem card_vertex [Fintype V] [Fintype C] :
    Fintype.card (NAEThreeColor.Vertex (V ⊕ C) (C × Bool)) =
      3 + 2 * Fintype.card V + 8 * Fintype.card C := by
  rw [NAEThreeColor.card_vertex]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  omega

end PCP.Reduction.ThreeSATToColor
