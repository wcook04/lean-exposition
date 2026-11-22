/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A concrete bitstring format for finite graphs

The header is `N` true bits followed by one false bit. The payload lists the
`N*N` adjacency bits in row-major order. Decoding is total: missing payload
bits are false, either orientation supplies an edge, and loops are discarded.
Thus every input string denotes an actual finite simple graph.

The definitions are computable and the encoder round-trips exactly. No
machine-level running-time certificate is asserted here.
-/

namespace PCP.Algebraic.ThreeColorEncoding

/-- The number of leading true bits is the decoded vertex count. -/
def vertexCount (x : List Bool) : ℕ := (x.takeWhile id).length

theorem size_le_length (x : List Bool) : vertexCount x ≤ x.length :=
  (List.takeWhile_prefix id).length_le

/-- Everything after the unary header and its separator is adjacency data. -/
def payload (x : List Bool) : List Bool := x.drop (vertexCount x + 1)

/-- Missing adjacency bits are false. -/
def edgeBit (x : List Bool) (i j : Fin (vertexCount x)) : Bool :=
  (payload x).getD (i.val * vertexCount x + j.val) false

/-- A total graph decoder, symmetrizing the two stored orientations and removing loops. -/
def graph (x : List Bool) : SimpleGraph (Fin (vertexCount x)) where
  Adj i j := i ≠ j ∧ (edgeBit x i j = true ∨ edgeBit x j i = true)
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    intro i h
    exact h.1 rfl⟩

instance graphDecidableAdj (x : List Bool) : DecidableRel (graph x).Adj := by
  intro i j
  change Decidable (i ≠ j ∧ (edgeBit x i j = true ∨ edgeBit x j i = true))
  infer_instance

/-- Ordered adjacency bits, indexed by the standard finite-product equivalence. -/
def adjacencyBits {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] : List Bool :=
  List.ofFn (fun k : Fin (N * N) =>
    decide (G.Adj (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))

/-- The unary size header, separator, and full row-major adjacency matrix. -/
def encode {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] : List Bool :=
  List.replicate N true ++ false :: adjacencyBits G

private theorem takeWhile_header (N : ℕ) (bits : List Bool) :
    (List.replicate N true ++ false :: bits).takeWhile id = List.replicate N true := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.replicate_succ, ih]

@[simp] theorem vertexCount_encode {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] : vertexCount (encode G) = N := by
  simp only [vertexCount, encode, takeWhile_header, List.length_replicate]

/-- The precise length includes the one-bit header terminator. -/
@[simp] theorem length_encode {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    (encode G).length = N + 1 + N ^ 2 := by
  simp only [encode, adjacencyBits, List.length_append, List.length_replicate,
    List.length_cons, List.length_ofFn, pow_two]
  omega

@[simp] theorem payload_encode {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    payload (encode G) = adjacencyBits G := by
  unfold payload
  rw [vertexCount_encode]
  simp [encode, List.drop_append]

/-- The finite coordinate transport caused solely by reading the size header. -/
def vertexEquiv {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    Fin (vertexCount (encode G)) ≃ Fin N := finCongr (vertexCount_encode G)

private theorem adjacencyBits_getD {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (i j : Fin N) :
    (adjacencyBits G).getD (i.val * N + j.val) false = decide (G.Adj i j) := by
  let k : Fin (N * N) := finProdFinEquiv (i, j)
  have hk : k.val = i.val * N + j.val := by
    change j.val + N * i.val = i.val * N + j.val
    ac_rfl
  rw [← hk]
  unfold adjacencyBits
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt)]
  simp only [List.getElem_ofFn]
  change decide (G.Adj (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) = _
  simp [k]

/-- Each decoded bit of an honest encoding is precisely its original adjacency bit. -/
theorem edgeBit_encode {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (i j : Fin (vertexCount (encode G))) :
    edgeBit (encode G) i j = decide (G.Adj (vertexEquiv G i) (vertexEquiv G j)) := by
  unfold edgeBit
  rw [payload_encode]
  have h := adjacencyBits_getD G (vertexEquiv G i) (vertexEquiv G j)
  simpa only [vertexEquiv, finCongr_apply, Fin.val_cast, vertexCount_encode] using h

/-- The decoded graph is isomorphic to the original graph by the header's coordinate cast. -/
def decodeEncodeIso {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    graph (encode G) ≃g G where
  toEquiv := vertexEquiv G
  map_rel_iff' := by
    intro i j
    change G.Adj (vertexEquiv G i) (vertexEquiv G j) ↔
      i ≠ j ∧ (edgeBit (encode G) i j = true ∨ edgeBit (encode G) j i = true)
    rw [edgeBit_encode, edgeBit_encode, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨fun he => h.ne (congrArg (vertexEquiv G) he), Or.inl h⟩
    · rintro ⟨_, h | h⟩
      · exact h
      · exact h.symm

/-- In particular, encoding and decoding preserve every finite colorability question. -/
theorem decode_encode_colorable_iff {N : ℕ} (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (k : ℕ) : (graph (encode G)).Colorable k ↔ G.Colorable k :=
  SimpleGraph.colorable_congr (decodeEncodeIso G)

end PCP.Algebraic.ThreeColorEncoding
