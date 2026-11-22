/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.GraphGridEmbedding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Embedding

/-!
# Explicit base-alphabet indexing of the graph grid

Given an actual indexing of the grid alphabet, vertices `Fin N` occupy the first
`N` base-alphabet addresses. The remaining addresses are isolated. Both vertex
decoding and padded adjacency are explicit computations; colorability agrees
with the existing generic graph-padding construction. All bounds also cover
zero-dimensional grids and empty alphabets. No running-time claim is made.
-/

namespace PCP.Algebraic.ThreeColorGridIndex

variable {A : Type*} {h n N : ℕ}

/-- Integer addresses are the little-endian base-`h` coordinates of the actual grid. -/
def gridEquiv (eH : A ≃ Fin h) (n : ℕ) : (Fin n → A) ≃ Fin (h ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) eH).trans finFunctionFinEquiv

/-- Vertex numbers occupy the initial addresses of a grid with enough capacity. -/
def embedding (eH : A ≃ Fin h) (hsize : N ≤ h ^ n) : Fin N ↪ (Fin n → A) :=
  (Fin.castLEEmb hsize).trans (gridEquiv eH n).symm.toEmbedding

/-- No vertex relabeling is hidden in the integer address. -/
@[simp] theorem gridEquiv_embedding (eH : A ≃ Fin h) (hsize : N ≤ h ^ n) (v : Fin N) :
    gridEquiv eH n (embedding eH hsize v) = Fin.castLE hsize v :=
  (gridEquiv eH n).apply_symm_apply _

/-- The `i`th grid coordinate is exactly the `i`th base-`h` digit of the vertex number. -/
theorem embedding_coordinate (eH : A ≃ Fin h) (hsize : N ≤ h ^ n)
    (v : Fin N) (i : Fin n) :
    (eH (embedding eH hsize v i)).val = v.val / h ^ i.val % h := by
  change (eH (eH.symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Decode a grid point if and only if its explicit address names an original vertex. -/
def decodeVertex (eH : A ≃ Fin h) (N : ℕ) (x : Fin n → A) : Option (Fin N) :=
  if hx : (gridEquiv eH n x).val < N then some ⟨(gridEquiv eH n x).val, hx⟩ else none

@[simp] theorem decodeVertex_embedding (eH : A ≃ Fin h) (hsize : N ≤ h ^ n)
    (v : Fin N) : decodeVertex eH N (embedding eH hsize v) = some v := by
  simp [decodeVertex, v.isLt]

/-- Successful decoding identifies the precise embedded vertex. -/
theorem decodeVertex_eq_some_iff (eH : A ≃ Fin h) (hsize : N ≤ h ^ n)
    (x : Fin n → A) (v : Fin N) :
    decodeVertex eH N x = some v ↔ embedding eH hsize v = x := by
  constructor
  · intro hv
    unfold decodeVertex at hv
    split_ifs at hv with hx
    · cases Option.some.inj hv
      apply (gridEquiv eH n).injective
      rw [gridEquiv_embedding]
      rfl
  · rintro rfl
    exact decodeVertex_embedding eH hsize v

/-- Padded adjacency checks the decoded vertex pair and rejects every unused address. -/
def pad (eH : A ≃ Fin h) (n : ℕ) (G : SimpleGraph (Fin N)) : SimpleGraph (Fin n → A) where
  Adj x y := match decodeVertex eH N x, decodeVertex eH N y with
    | some u, some v => G.Adj u v
    | _, _ => False
  symm := by
    refine ⟨?_⟩
    intro x y
    cases decodeVertex eH N x <;> cases decodeVertex eH N y <;>
      simp only [false_implies]
    exact G.symm.symm _ _
  loopless := by
    refine ⟨?_⟩
    intro x
    cases decodeVertex eH N x <;> simp only [not_false_eq_true]
    exact G.irrefl

/-- The padded adjacency is decidable by actual vertex decoding and input adjacency. -/
instance padDecidableAdj (eH : A ≃ Fin h) (n : ℕ) (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] : DecidableRel (pad eH n G).Adj := by
  intro x y
  change Decidable (match decodeVertex eH N x, decodeVertex eH N y with
    | some u, some v => G.Adj u v
    | _, _ => False)
  split <;> infer_instance

/-- The computational padding is exactly the established edge-image construction. -/
theorem pad_eq_map (eH : A ≃ Fin h) (hsize : N ≤ h ^ n) (G : SimpleGraph (Fin N)) :
    pad eH n G = GraphGridEmbedding.pad G (embedding eH hsize) := by
  ext x y
  rw [GraphGridEmbedding.pad_adj]
  simp_rw [← decodeVertex_eq_some_iff eH hsize]
  cases hx : decodeVertex eH N x <;> cases hy : decodeVertex eH N y <;>
    simp [pad, hx, hy]

/-- The original graph is the induced graph on the explicitly addressed vertices. -/
@[simp] theorem pad_adj_embedding (eH : A ≃ Fin h) (hsize : N ≤ h ^ n)
    (G : SimpleGraph (Fin N)) (u v : Fin N) :
    (pad eH n G).Adj (embedding eH hsize u) (embedding eH hsize v) ↔ G.Adj u v := by
  rw [pad_eq_map eH hsize]
  exact GraphGridEmbedding.pad_adj_image G _ u v

/-- Every unused explicit grid address is isolated. -/
theorem pad_isIsolated (eH : A ≃ Fin h) (n : ℕ) (G : SimpleGraph (Fin N))
    (x : Fin n → A) (hx : decodeVertex eH N x = none) : (pad eH n G).IsIsolated x := by
  intro y
  simp [pad, hx]

/-- Explicit graph padding preserves ordinary three-colorability exactly. -/
theorem threeColorable_pad_iff (eH : A ≃ Fin h) (hsize : N ≤ h ^ n)
    (G : SimpleGraph (Fin N)) : (pad eH n G).Colorable 3 ↔ G.Colorable 3 := by
  rw [pad_eq_map eH hsize]
  exact GraphGridEmbedding.threeColorable_pad_iff G _

/-- The same preservation holds for every positive number of colors. -/
theorem colorable_pad_iff (eH : A ≃ Fin h) (hsize : N ≤ h ^ n)
    (G : SimpleGraph (Fin N)) (k : ℕ) [NeZero k] :
    (pad eH n G).Colorable k ↔ G.Colorable k := by
  rw [pad_eq_map eH hsize]
  exact GraphGridEmbedding.colorable_pad_iff G _ k

end PCP.Algebraic.ThreeColorGridIndex
