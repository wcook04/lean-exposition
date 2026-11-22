/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorParameterChoice
import PCP.Algebraic.ThreeColorResourceBounds
import PCP.Algebraic.ThreeColorSeedSize
import PCP.Algebraic.BinarySeedEncoding
import PCP.Algebraic.ThreeColorFullFieldSampling
import PCP.Algebraic.BooleanCoefficientIndex
import PCP.Algebraic.ThreeColorQueryIndex
import PCP.Algebraic.ThreeColorSeedIndex
import PCP.Algebraic.ThreeColorGridIndex

/-!
# Finite binary words and logarithmic randomness for three-colorability

Parameters are chosen from the number of vertices, with inner degree fixed at
four. The resulting proof address space has polynomial size, and the exact
whole-field random seed uses logarithmically many bits. Seed and address codecs
use explicit mixed-radix encodings relative to the field coordinates. The
field and coordinates use concrete coefficient arithmetic. Graphs supplied with
explicit vertex indices use base-alphabet grid addresses. Generic finite-graph
callers may use the default chosen vertex indexing; the canonical bitstring
verifier supplies its own. Its amplified algorithm, including these codecs and
field operations, is certified by `PCP.Lang.ThreeColorRuntime.polyTimeAlg`.
-/

namespace PCP.Algebraic.ThreeColorBinaryVerifier

open ThreeColorParameters ThreeColorParameterChoice

/-- The actual eight-table address space at the chosen parameters. -/
abbrev Address (N : ℕ) := ThreeColorVerifier.Query (Field (exponent N))
  (size (exponent N)) (size (exponent N)) 4 (binaryDimension (exponent N))

/-- Length of the single binary word containing the eight physical tables. -/
def proofLength (N : ℕ) : ℕ :=
  let a := exponent N
  let t := binaryDimension a
  ThreeColorQueryIndex.addressLength (2 ^ t) (size a) (size a) 4
    (2 ^ (1 + t)) (2 ^ (1 + t + t.choose 2 + t.choose 3))

/-- Exact bit count for the whole-field sampler, including every independent seed. -/
def randomBits (N : ℕ) : ℕ := ThreeColorSeedSize.rawBits
  (size (exponent N)) (size (exponent N)) 4 (binaryDimension (exponent N))

abbrev ProofWord (N : ℕ) := Fin (proofLength N) → ZMod 2

abbrev Seed (N : ℕ) := Fin (randomBits N) → ZMod 2

abbrev StructuredProof (N : ℕ) := ThreeColorVerifier.Proof (Field (exponent N))
  (size (exponent N)) (size (exponent N)) 4 (binaryDimension (exponent N))

/-- The only supplied component codec is the selected field's binary coordinates. -/
def fieldIndex (N : ℕ) :
    Field (exponent N) ≃ Fin (2 ^ binaryDimension (exponent N)) :=
  (coordinates (exponent N)).toEquiv.trans
    (BinarySeedPadding.finSeedEquiv (binaryDimension (exponent N))).symm

/-- Explicit constructor and coefficient indexing relative to the field coordinates. -/
def addressEquiv (N : ℕ) : Address N ≃ Fin (proofLength N) :=
  ThreeColorQueryIndex.equiv (fieldIndex N)
    (BooleanCoefficientIndex.affineEquiv (binaryDimension (exponent N)))
    (BooleanCoefficientIndex.cubicEquiv (binaryDimension (exponent N)))

/-- The computed length is exactly the cardinality used in the resource bound. -/
theorem proofLength_eq_card (N : ℕ) : proofLength N = Fintype.card (Address N) := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (addressEquiv N)).symm

/-- Read each structured-table bit from its single-word address. -/
def decodeProof {N : ℕ} (π : ProofWord N) : StructuredProof N :=
  ThreeColorVerifier.ofOracle (fun q => π (addressEquiv N q))

/-- Pack the structured proof into the same finite word. -/
def encodeProof {N : ℕ} (π : StructuredProof N) : ProofWord N :=
  fun i => ThreeColorVerifier.read π ((addressEquiv N).symm i)

@[simp] theorem decode_encode {N : ℕ} (π : StructuredProof N) :
    decodeProof (encodeProof π) = π := by
  simp [decodeProof, encodeProof]

/-- The exact seed length is bounded by a fixed multiple of the input-size logarithm. -/
theorem randomBits_le (N : ℕ) : randomBits N ≤ 32000000 * (Nat.clog 2 N + 1) := by
  have h := ThreeColorResourceBounds.family_seed_exponent_le (exponent_ge_two N)
  have hv := volume_le_log_add_one N
  simp only [randomBits, ThreeColorSeedSize.rawBits, ThreeColorSeedSize.originalBits,
    size, binaryDimension_eq]
  dsimp [volume] at hv
  nlinarith

/-- The actual proof word, not an independent bound parameter, has polynomial length. -/
theorem proofLength_le (N : ℕ) : proofLength N ≤ (4 * max 1 N) ^ 4224000 := by
  rw [proofLength_eq_card]
  have h := ThreeColorResourceBounds.card_family_query_le (exponent_ge_two N)
  have hv := volume_le_log_add_one N
  apply h.trans
  apply (Nat.pow_le_pow_right (by decide : 1 ≤ 2) ?_).trans
    (ThreeColorResourceBounds.pow_logarithmic_le_polynomial N 4224000)
  dsimp [volume] at hv
  omega

abbrev RawSeed (N : ℕ) := ThreeColorFullFieldSampling.RawSample (Field (exponent N))
  (size (exponent N)) (size (exponent N)) 4 (binaryDimension (exponent N))

/-- Uniform binary strings and whole-field seeds have exactly the same distribution. -/
def seedEquiv (N : ℕ) : RawSeed N ≃ Seed N :=
  ThreeColorSeedIndex.equiv (coordinates (exponent N))
    (size (exponent N)) (size (exponent N)) 4

variable {V : Type*} [Fintype V]

/-- The supplied vertex index becomes a base-grid-alphabet address. -/
def vertexEmbedding
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) :
    V ↪ (Fin (size (exponent (Fintype.card V))) → grid (exponent (Fintype.card V))) :=
  eV.toEmbedding.trans (ThreeColorGridIndex.embedding (gridCode (exponent (Fintype.card V)))
    (by simpa only [card_grid] using size_le_grid_capacity (Fintype.card V)))

/-- Each actual vertex coordinate is the corresponding digit of its supplied index. -/
theorem vertexEmbedding_coordinate
    (eV : V ≃ Fin (Fintype.card V)) (v : V)
    (i : Fin (size (exponent (Fintype.card V)))) :
    (gridCode (exponent (Fintype.card V)) (vertexEmbedding eV v i)).val =
      (eV v).val / size (exponent (Fintype.card V)) ^ i.val %
        size (exponent (Fintype.card V)) :=
  ThreeColorGridIndex.embedding_coordinate _ _ _ _

/-- Place the input graph in the selected grid, adding isolated vertices. -/
def gridGraph (G : SimpleGraph V)
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) :
    SimpleGraph (Fin (size (exponent (Fintype.card V))) → grid (exponent (Fintype.card V))) :=
  ThreeColorGridIndex.pad (gridCode (exponent (Fintype.card V)))
    (size (exponent (Fintype.card V))) (G.comap eV.symm)

/-- The explicitly placed vertices induce exactly the input graph. -/
@[simp] theorem gridGraph_adj_vertexEmbedding (G : SimpleGraph V)
    (eV : V ≃ Fin (Fintype.card V)) (u v : V) :
    (gridGraph G eV).Adj (vertexEmbedding eV u) (vertexEmbedding eV v) ↔ G.Adj u v := by
  change (ThreeColorGridIndex.pad _ _ (G.comap eV.symm)).Adj
    (ThreeColorGridIndex.embedding _ _ (eV u))
    (ThreeColorGridIndex.embedding _ _ (eV v)) ↔ _
  rw [ThreeColorGridIndex.pad_adj_embedding]
  change G.Adj (eV.symm (eV u)) (eV.symm (eV v)) ↔ _
  simp only [Equiv.symm_apply_apply]

@[simp] theorem gridGraph_colorable_iff (G : SimpleGraph V)
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) :
    (gridGraph G eV).Colorable 3 ↔ G.Colorable 3 := by
  rw [gridGraph, ThreeColorGridIndex.threeColorable_pad_iff _
    (by simpa only [card_grid] using size_le_grid_capacity (Fintype.card V))]
  exact SimpleGraph.colorable_congr
    { toEquiv := eV.symm
      map_rel_iff' := by intros; rfl }

/-- The verifier on one finite proof word and a fixed-length fair-bit seed. -/
noncomputable def test (G : SimpleGraph V) (π : ProofWord (Fintype.card V))
    (s : Seed (Fintype.card V))
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) : Bool :=
  let a := exponent (Fintype.card V)
  ThreeColorFullFieldSampling.test (coordinates a) (nodes a) (generator a) (grid a)
    (gridGraph G eV) (decodeProof π) ((seedEquiv _).symm s)

/-- Physical bit addresses in the finite proof word; invalid parameters make no reads. -/
noncomputable def queries (G : SimpleGraph V) (s : Seed (Fintype.card V))
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) :
    List (Fin (proofLength (Fintype.card V))) :=
  let a := exponent (Fintype.card V)
  (ThreeColorFullFieldSampling.queries (coordinates a) (nodes a) (generator a) (grid a)
    (gridGraph G eV) ((seedEquiv _).symm s)).map (addressEquiv _)

/-- Every seed reads at most 187 actual bits of the indexed proof. -/
theorem queries_length_le (G : SimpleGraph V) (s : Seed (Fintype.card V))
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) :
    (queries G s eV).length ≤ 187 := by
  simpa only [queries, List.length_map] using
    ThreeColorFullFieldSampling.queries_length_le _ _ _ _ (gridGraph G eV) ((seedEquiv _).symm s)

/-- Acceptance depends only on the listed physical proof bits. -/
theorem test_congr (G : SimpleGraph V) (π π' : ProofWord (Fintype.card V))
    (s : Seed (Fintype.card V))
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V)
    (h : ∀ i ∈ queries G s eV, π i = π' i) :
    test G π s eV = test G π' s eV := by
  apply ThreeColorFullFieldSampling.test_congr
  intro q hq
  simp only [decodeProof, ThreeColorVerifier.read_ofOracle]
  exact h _ (List.mem_map.mpr ⟨q, hq, rfl⟩)

/-- The same honest eight tables give perfect completeness after both finite reindexings. -/
theorem exists_proof_test_eq_true (G : SimpleGraph V) (hG : G.Colorable 3)
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) :
    ∃ π : ProofWord (Fintype.card V), ∀ s, test G π s eV = true := by
  let a := exponent (Fintype.card V)
  obtain ⟨π, hπ⟩ := ThreeColorFullFieldSampling.exists_proof_test_eq_true
    (coordinates a) (nodes a).injective (generator_goodNodes a) (cubeRoot_spec a)
    (grid a) (grid_nonempty a) (gridGraph G eV) ((gridGraph_colorable_iff G eV).mpr hG)
    (capacity (exponent_ge_two _))
  refine ⟨encodeProof π, fun s => ?_⟩
  simpa only [test, decode_encode] using hπ ((seedEquiv _).symm s)

/-- The gap is a fixed positive rational, independent of graph size. -/
def gap : ℚ := ThreeColorSoundnessBudget.gap 4 / 16

theorem gap_pos : 0 < gap := div_pos (ThreeColorSoundnessBudget.gap_pos 4) (by norm_num)

/-- Actual rejection probability under uniform fixed-length binary randomness. -/
noncomputable def rejectionRate (G : SimpleGraph V) (π : ProofWord (Fintype.card V))
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) : ℚ :=
  relativeDistance (fun s => test G π s eV) (fun _ => true)

open scoped Classical in
theorem rejectionRate_eq (G : SimpleGraph V) (π : ProofWord (Fintype.card V))
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) :
    rejectionRate G π eV =
      let a := exponent (Fintype.card V)
      ThreeColorFullFieldSampling.rejectionRate (coordinates a) (nodes a) (generator a)
        (grid a) (gridGraph G eV) (decodeProof π) := by
  classical
  unfold rejectionRate test ThreeColorFullFieldSampling.rejectionRate
  let a := exponent (Fintype.card V)
  let f : RawSeed (Fintype.card V) → Bool := ThreeColorFullFieldSampling.test
    (coordinates a) (nodes a) (generator a) (grid a) (gridGraph G eV) (decodeProof π)
  exact relativeDistance_comp_equiv (ι := RawSeed (Fintype.card V))
    (κ := Seed (Fintype.card V)) (seedEquiv (Fintype.card V)).symm f (fun _ => true)

/-- No proof for a noncolorable graph defeats the fixed positive rejection bound. -/
theorem rejectionRate_ge_of_not_colorable (G : SimpleGraph V) (hG : ¬ G.Colorable 3)
    (π : ProofWord (Fintype.card V))
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) : gap ≤ rejectionRate G π eV := by
  classical
  rw [rejectionRate_eq G π eV]
  let a := exponent (Fintype.card V)
  have hcap := capacity (exponent_ge_two (Fintype.card V))
  have hd : ((grid a).card - 1) * size a ≤ 4 * size a ^ 4 := by
    dsimp [a]
    omega
  exact ThreeColorFullFieldSampling.rejectionRate_ge_of_not_colorable
    (by decide) (soundness_field_bound a) (coordinates a) (nodes_spec a)
    (generator_goodNodes a) (cubeRoot_spec a) (grid a) (grid_nonempty a)
    (grid_field_bound a) hd (gridGraph G eV)
    (fun hc => hG ((gridGraph_colorable_iff G eV).mp hc))
    (decodeProof π)

/-- All mathematical resource and verification guarantees for every finite input graph.
The concrete runtime and NP reduction are supplied downstream by
`PCP.Lang.ThreeColorRuntime.polyTimeAlg` and
`PCP.Algebraic.ThreeColorFinalAssembly.of_runtime`. -/
theorem verification_guarantees (G : SimpleGraph V)
    (eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V) :
    0 < gap ∧
      randomBits (Fintype.card V) ≤ 32000000 * (Nat.clog 2 (Fintype.card V) + 1) ∧
      proofLength (Fintype.card V) ≤ (4 * max 1 (Fintype.card V)) ^ 4224000 ∧
      (∀ s, (queries G s eV).length ≤ 187) ∧
      (G.Colorable 3 → ∃ π, ∀ s, test G π s eV = true) ∧
      (¬ G.Colorable 3 → ∀ π, gap ≤ rejectionRate G π eV) :=
  ⟨gap_pos, randomBits_le _, proofLength_le _, fun s => queries_length_le G s eV,
    fun hG => exists_proof_test_eq_true G hG eV,
    fun hG π => rejectionRate_ge_of_not_colorable G hG π eV⟩

end PCP.Algebraic.ThreeColorBinaryVerifier
