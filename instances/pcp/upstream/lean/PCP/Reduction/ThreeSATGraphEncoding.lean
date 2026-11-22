/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Reduction.ThreeSATToColor
import PCP.Algebraic.ThreeColorEncoding

/-!
# Numeric graph encoding for the three-literal reduction

Explicit sum and product codecs number the graph vertices. The adjacency matrix
then uses the exact bitstring format consumed by the algebraic verifier. Decoding
preserves satisfiability and the output length is quadratic in variables plus
clauses. These are computable definitions and size bounds, not machine-time
certificates.
-/

namespace PCP.Reduction.ThreeSATGraphEncoding

open NAEThreeColor

/-- The two Boolean signs have their fixed numeric codes. -/
def boolCode : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i = 1)
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Number the palette, variable pairs and clause triangles in that order. -/
def vertexCode {V C : Type*} {v c : ℕ} (eV : V ≃ Fin v) (eC : C ≃ Fin c) :
    Vertex V C ≃ Fin (3 + 2 * v + 3 * c) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 3))
    ((Equiv.sumCongr ((Equiv.prodCongr eV boolCode).trans finProdFinEquiv)
      ((Equiv.prodCongr eC (Equiv.refl (Fin 3))).trans finProdFinEquiv)).trans
        finSumFinEquiv)).trans finSumFinEquiv).trans (finCongr (by omega))

/-- The split formula has one extra variable and two triangles per source clause. -/
def threeSatCode (v c : ℕ) :
    Vertex (Fin v ⊕ Fin c) (Fin c × Bool) ≃ Fin (3 + 2 * v + 8 * c) :=
  (vertexCode finSumFinEquiv ((Equiv.prodCongr (Equiv.refl (Fin c)) boolCode).trans
    finProdFinEquiv)).trans (finCongr (by omega))

variable {v c : ℕ}

/-- The source graph on explicitly numbered vertices. -/
def indexedGraph (Q : Fin c → Fin 3 → Literal (Fin v)) :
    SimpleGraph (Fin (3 + 2 * v + 8 * c)) :=
  (ThreeSATToColor.graph Q).comap (threeSatCode v c).symm

instance (Q : Fin c → Fin 3 → Literal (Fin v)) : DecidableRel (indexedGraph Q).Adj := by
  unfold indexedGraph
  infer_instance

/-- Numeric indexing preserves all edges exactly. -/
def graphIso (Q : Fin c → Fin 3 → Literal (Fin v)) :
    ThreeSATToColor.graph Q ≃g indexedGraph Q where
  toEquiv := threeSatCode v c
  map_rel_iff' := by
    intro a b
    simp [indexedGraph]

/-- The actual binary input for the algebraic three-color verifier. -/
def encode (Q : Fin c → Fin 3 → Literal (Fin v)) : List Bool :=
  Algebraic.ThreeColorEncoding.encode (indexedGraph Q)

/-- Decoding the computed bitstring yields the original satisfiability question. -/
theorem decode_colorable_iff (Q : Fin c → Fin 3 → Literal (Fin v)) :
    (Algebraic.ThreeColorEncoding.graph (encode Q)).Colorable 3 ↔
      ∃ a, ThreeSATToColor.Satisfies Q a := by
  rw [encode, Algebraic.ThreeColorEncoding.decode_encode_colorable_iff]
  exact (SimpleGraph.colorable_congr (graphIso Q)).symm.trans (ThreeSATToColor.colorable_iff Q)

/-- Exact size of the unary header and square adjacency matrix. -/
@[simp] theorem length_encode (Q : Fin c → Fin 3 → Literal (Fin v)) :
    (encode Q).length = (3 + 2 * v + 8 * c) + 1 + (3 + 2 * v + 8 * c) ^ 2 :=
  Algebraic.ThreeColorEncoding.length_encode _

/-- The concrete output encoding has a uniform quadratic size bound. -/
theorem length_encode_le (Q : Fin c → Fin 3 → Literal (Fin v)) :
    (encode Q).length ≤ 64 * (v + c + 1) ^ 2 := by
  rw [length_encode]
  have hn : 3 + 2 * v + 8 * c + 1 ≤ 8 * (v + c + 1) := by omega
  have h := Nat.pow_le_pow_left hn 2
  nlinarith

end PCP.Reduction.ThreeSATGraphEncoding
