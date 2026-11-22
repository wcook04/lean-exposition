/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.ThreeSATGraphEncoding

/-!
# Arithmetic adjacency for the three-color clause gadgets

The only instance-dependent operation is the numeric clause-literal lookup.
All remaining adjacency tests use comparisons, division, and remainder on vertex
numbers. The correctness theorem matches the explicit graph and vertex codec.
-/

namespace PCP.Reduction.ThreeColorNumericAdjacency

open NAEThreeColor

/-- The numeric address of a literal's palette or variable vertex. -/
def literalAddress {v : ℕ} : Literal (Fin v) → ℕ
  | .const b => b.toNat
  | .var i b => 3 + (2 * i.val + b.toNat)

/-- The arithmetic form of the structural graph-vertex codec. -/
def address {v c : ℕ} : Vertex (Fin v) (Fin c) → ℕ
  | .inl i => i.val
  | .inr (.inl (i, b)) => 3 + (2 * i.val + b.toNat)
  | .inr (.inr (e, i)) => 3 + 2 * v + (3 * e.val + i.val)

@[simp] theorem address_literal {v c : ℕ} (l : Literal (Fin v)) :
    address (literalVertex (C := Fin c) l) = literalAddress l := by
  cases l with
  | const b => cases b <;> rfl
  | var i b => rfl

theorem address_code {v c : ℕ} (u : Vertex (Fin v) (Fin c)) :
    address u = (ThreeSATGraphEncoding.vertexCode (Equiv.refl _) (Equiv.refl _) u).val := by
  rcases u with i | ⟨i, b⟩ | ⟨e, i⟩
  · rfl
  · cases b <;> simp [address, ThreeSATGraphEncoding.vertexCode,
      ThreeSATGraphEncoding.boolCode, finProdFinEquiv, finSumFinEquiv]
    omega
  · simp [address, ThreeSATGraphEncoding.vertexCode, finProdFinEquiv, finSumFinEquiv]
    omega

theorem address_injective {v c : ℕ} : Function.Injective (@address v c) := by
  intro u w h
  apply (ThreeSATGraphEncoding.vertexCode (Equiv.refl _) (Equiv.refl _)).injective
  apply Fin.ext
  simpa only [← address_code] using h

/-- One oriented gadget edge, written purely in natural arithmetic. -/
def direct (v : ℕ) (literal : ℕ → ℕ → ℕ) (u w : ℕ) : Bool :=
  if u < 3 then decide (w < 3 ∧ u ≠ w) else
  if u < 3 + 2 * v then
    if w < 3 then decide (w = 2) else
      decide (w < 3 + 2 * v ∧ (u - 3) / 2 = (w - 3) / 2 ∧ (u - 3) % 2 ≠ (w - 3) % 2)
  else if w < 3 + 2 * v then
    decide (w = literal ((u - (3 + 2 * v)) / 3) ((u - (3 + 2 * v)) % 3))
  else decide ((u - (3 + 2 * v)) / 3 = (w - (3 + 2 * v)) / 3 ∧
    (u - (3 + 2 * v)) % 3 ≠ (w - (3 + 2 * v)) % 3)

/-- Symmetrization and loop removal are also explicit arithmetic tests. -/
def adjacency (v : ℕ) (literal : ℕ → ℕ → ℕ) (u w : ℕ) : Bool :=
  decide (u ≠ w) && (direct v literal u w || direct v literal w u)

private theorem var_lt {v : ℕ} (i : Fin v) (b : Bool) :
    3 + (2 * i.val + b.toNat) < 3 + 2 * v := by
  cases b <;> simp
  omega

private theorem var_div (i : ℕ) (b : Bool) : (3 + (2 * i + b.toNat) - 3) / 2 = i := by
  cases b <;> simp
  omega

private theorem var_mod (i : ℕ) (b : Bool) : (3 + (2 * i + b.toNat) - 3) % 2 = b.toNat := by
  cases b <;> simp

private theorem clause_div (v e : ℕ) (i : Fin 3) :
    (3 + 2 * v + (3 * e + i.val) - (3 + 2 * v)) / 3 = e := by omega

private theorem clause_mod (v e : ℕ) (i : Fin 3) :
    (3 + 2 * v + (3 * e + i.val) - (3 + 2 * v)) % 3 = i.val := by omega

/-- The literal oracle is needed only at actual clause and triangle indices. -/
theorem direct_correct {v c : ℕ} (Q : Fin c → Fin 3 → Literal (Fin v))
    (literal : ℕ → ℕ → ℕ) (hl : ∀ e i, literal e.val i.val = literalAddress (Q e i))
    (u w : Vertex (Fin v) (Fin c)) :
    direct v literal (address u) (address w) = true ↔ NAEThreeColor.direct Q u w := by
  rcases u with i | ⟨i, b⟩ | ⟨e, i⟩ <;>
    rcases w with j | ⟨j, d⟩ | ⟨f, j⟩
  · simp [address, direct, i.isLt, j.isLt, Fin.ext_iff, NAEThreeColor.direct]
  · simp [address, direct, i.isLt, NAEThreeColor.direct]
  · simp [address, direct, i.isLt, NAEThreeColor.direct,
      show ¬3 + 2 * v + (3 * f.val + j.val) < 3 by omega]
  · by_cases hj : j.val = 2 <;>
      simp [address, direct, var_lt i b, j.isLt, NAEThreeColor.direct, Fin.ext_iff, hj]
  · simp only [address, direct, ite_eq_right (by omega : ¬3 + (2 * i.val + b.toNat) < 3),
      ite_eq_left (var_lt i b), ite_eq_right (by omega : ¬3 + (2 * j.val + d.toNat) < 3),
      decide_eq_true_eq, var_div, var_mod, NAEThreeColor.direct]
    constructor
    · rintro ⟨_, hij, hbd⟩
      exact ⟨Fin.ext hij, fun he => hbd (congrArg Bool.toNat he)⟩
    · rintro ⟨rfl, hbd⟩
      refine ⟨var_lt i d, rfl, ?_⟩
      cases b <;> cases d <;> simp_all
  · simp [address, direct, var_lt i b, NAEThreeColor.direct,
      show ¬3 + 2 * v + (3 * f.val + j.val) < 3 by omega,
      show ¬3 + 2 * v + (3 * f.val + j.val) < 3 + 2 * v by omega]
  · simp only [address, direct, ite_eq_right (by omega : ¬3 + 2 * v + (3 * e.val + i.val) < 3),
      ite_eq_right (by omega : ¬3 + 2 * v + (3 * e.val + i.val) < 3 + 2 * v),
      ite_eq_left (by have := j.isLt; omega : j.val < 3 + 2 * v),
      decide_eq_true_eq, clause_div, clause_mod, hl, NAEThreeColor.direct]
    constructor
    · intro he
      apply address_injective
      rw [address_literal]
      exact he
    · intro he
      have hh := congrArg address he
      rw [address_literal] at hh
      exact hh
  · simp only [address, direct, ite_eq_right (by omega : ¬3 + 2 * v + (3 * e.val + i.val) < 3),
      ite_eq_right (by omega : ¬3 + 2 * v + (3 * e.val + i.val) < 3 + 2 * v),
      ite_eq_left (var_lt j d), decide_eq_true_eq, clause_div, clause_mod, hl, NAEThreeColor.direct]
    constructor
    · intro he
      apply address_injective
      rw [address_literal]
      exact he
    · intro he
      have hh := congrArg address he
      rw [address_literal] at hh
      exact hh
  · simp only [address, direct, ite_eq_right (by omega : ¬3 + 2 * v + (3 * e.val + i.val) < 3),
      ite_eq_right (by omega : ¬3 + 2 * v + (3 * e.val + i.val) < 3 + 2 * v),
      ite_eq_right (by omega : ¬3 + 2 * v + (3 * f.val + j.val) < 3 + 2 * v),
      decide_eq_true_eq, clause_div, clause_mod, NAEThreeColor.direct]
    exact ⟨fun h => ⟨Fin.ext h.1, fun he => h.2 (congrArg Fin.val he)⟩,
      fun h => ⟨congrArg Fin.val h.1, fun he => h.2 (Fin.ext he)⟩⟩

/-- This is the actual graph adjacency, including its explicit symmetrization. -/
theorem adjacency_correct {v c : ℕ} (Q : Fin c → Fin 3 → Literal (Fin v))
    (literal : ℕ → ℕ → ℕ) (hl : ∀ e i, literal e.val i.val = literalAddress (Q e i))
    (u w : Vertex (Fin v) (Fin c)) :
    adjacency v literal (address u) (address w) = true ↔ (NAEThreeColor.graph Q).Adj u w := by
  simp only [adjacency, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    direct_correct Q literal hl, NAEThreeColor.graph, SimpleGraph.fromRel_adj]
  exact and_congr (not_congr address_injective.eq_iff) Iff.rfl


/-- A total numeric literal lookup for the finite source formula. -/
def literalLookup {v c : ℕ} (Q : Fin c → Fin 3 → Literal (Fin v)) (e i : ℕ) : ℕ :=
  if he : e < c then if hi : i < 3 then literalAddress (Q ⟨e, he⟩ ⟨i, hi⟩) else 0 else 0

@[simp] theorem literalLookup_fin {v c : ℕ} (Q : Fin c → Fin 3 → Literal (Fin v))
    (e : Fin c) (i : Fin 3) : literalLookup Q e.val i.val = literalAddress (Q e i) := by
  simp [literalLookup]

/-- The graph on the exact arithmetic vertex order used by the clause codec. -/
def indexedGraph {v c : ℕ} (Q : Fin c → Fin 3 → Literal (Fin v)) :
    SimpleGraph (Fin (3 + 2 * v + 3 * c)) :=
  (NAEThreeColor.graph Q).comap
    (ThreeSATGraphEncoding.vertexCode (Equiv.refl _) (Equiv.refl _)).symm

instance {v c : ℕ} (Q : Fin c → Fin 3 → Literal (Fin v)) :
    DecidableRel (indexedGraph Q).Adj := by unfold indexedGraph; infer_instance

/-- Arithmetic adjacency coincides with the finite graph at every numeric vertex pair. -/
theorem adjacency_indexed {v c : ℕ} (Q : Fin c → Fin 3 → Literal (Fin v))
    (u w : Fin (3 + 2 * v + 3 * c)) :
    adjacency v (literalLookup Q) u.val w.val = true ↔ (indexedGraph Q).Adj u w := by
  let e := ThreeSATGraphEncoding.vertexCode (Equiv.refl (Fin v)) (Equiv.refl (Fin c))
  have h := adjacency_correct Q (literalLookup Q) (literalLookup_fin Q) (e.symm u) (e.symm w)
  simpa only [address_code, e, Equiv.apply_symm_apply, indexedGraph, SimpleGraph.comap_adj] using h

/-- Unary header and row-major payload, computed from natural-number arithmetic alone. -/
def encode (v c : ℕ) (literal : ℕ → ℕ → ℕ) : List Bool :=
  let N := 3 + 2 * v + 3 * c
  List.replicate N true ++ false :: List.ofFn (fun k : Fin (N * N) =>
    adjacency v literal (k.val / N) (k.val % N))

/-- The arithmetic encoder is exactly the production graph-bitstring format. -/
theorem encode_eq {v c : ℕ} (Q : Fin c → Fin 3 → Literal (Fin v)) :
    encode v c (literalLookup Q) = Algebraic.ThreeColorEncoding.encode (indexedGraph Q) := by
  simp only [encode, Algebraic.ThreeColorEncoding.encode,
    Algebraic.ThreeColorEncoding.adjacencyBits]
  congr 2
  apply congrArg List.ofFn
  funext k
  apply Bool.eq_iff_iff.mpr
  have hdiv : (finProdFinEquiv.symm k).1.val = k.val / (3 + 2 * v + 3 * c) := rfl
  have hmod : (finProdFinEquiv.symm k).2.val = k.val % (3 + 2 * v + 3 * c) := rfl
  rw [← hdiv, ← hmod]
  exact (adjacency_indexed Q (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2).trans
    ⟨decide_eq_true, of_decide_eq_true⟩

end PCP.Reduction.ThreeColorNumericAdjacency
