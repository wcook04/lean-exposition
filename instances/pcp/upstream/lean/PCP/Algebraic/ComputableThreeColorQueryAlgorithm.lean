/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ComputableThreeColorVerifier
import PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

/-!
# Executable production three-color verifier callbacks and protocols

The actual bitstring input, seed codecs, coefficient labels, field operations,
and finite proof addresses all have executable implementations. Their exact
identities with the semantic verifier transfer its existing correctness and
query guarantees. The answer-history algorithms below are ordinary definitions,
including the amplified algorithm. The concrete `Machine.PolyTimeAlg` certificate
for that amplified algorithm is proved downstream as
`PCP.Lang.ThreeColorRuntime.polyTimeAlg`.
-/

namespace PCP.Algebraic.ComputableThreeColorBinaryVerifier

open ThreeColorBinaryVerifier ThreeColorParameterChoice ThreeColorParameters

variable {V : Type*} [Fintype V]

/-- Decidable input adjacency remains decidable after explicit grid padding. -/
instance gridGraphDecidableAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (eV : V ≃ Fin (Fintype.card V)) : DecidableRel (gridGraph G eV).Adj := by
  unfold gridGraph
  infer_instance

/-- The production verdict on the single indexed binary proof word. -/
def test (G : SimpleGraph V) [DecidableRel G.Adj] (π : ProofWord (Fintype.card V))
    (s : Seed (Fintype.card V)) (eV : V ≃ Fin (Fintype.card V)) : Bool :=
  let a := exponent (Fintype.card V)
  ComputableThreeColorFullFieldSampling.test (coordinates a) (nodes a) (generator a) (grid a)
    (gridGraph G eV) (decodeProof π) ((seedEquiv _).symm s)

/-- The production list of actual finite proof addresses. -/
def queries (G : SimpleGraph V) [DecidableRel G.Adj] (s : Seed (Fintype.card V))
    (eV : V ≃ Fin (Fintype.card V)) : List (Fin (proofLength (Fintype.card V))) :=
  let a := exponent (Fintype.card V)
  (ComputableThreeColorFullFieldSampling.queries
    (coordinates a) (nodes a) (generator a) (grid a)
    (gridGraph G eV) ((seedEquiv _).symm s)).map (addressEquiv _)

@[simp] theorem test_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (π : ProofWord (Fintype.card V)) (s : Seed (Fintype.card V))
    (eV : V ≃ Fin (Fintype.card V)) : test G π s eV = ThreeColorBinaryVerifier.test G π s eV := by
  simp only [test, ThreeColorBinaryVerifier.test, ComputableThreeColorFullFieldSampling.test_eq]

@[simp] theorem queries_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Seed (Fintype.card V)) (eV : V ≃ Fin (Fintype.card V)) :
    queries G s eV = ThreeColorBinaryVerifier.queries G s eV := by
  simp only [queries, ThreeColorBinaryVerifier.queries,
    ComputableThreeColorFullFieldSampling.queries_eq]

end PCP.Algebraic.ComputableThreeColorBinaryVerifier

namespace PCP.Algebraic.ComputableThreeColorQueryAlgorithm

open ThreeColorCanonicalVerifier

/-- Actual finite proof addresses computed from the supplied random-bit list. -/
def queryList (x bits : List Bool) :
    List (Fin (ThreeColorBinaryVerifier.proofLength (graphOrder x))) :=
  ComputableThreeColorBinaryVerifier.queries (ThreeColorEncoding.graph x)
    (ThreeColorQueryAlgorithm.sampleBits x bits) (vertexCode x)

/-- Executable verdict on a finite Boolean proof word. -/
def verdict (x bits : List Bool)
    (w : Fin (ThreeColorBinaryVerifier.proofLength (graphOrder x)) → Bool) : Bool :=
  ComputableThreeColorBinaryVerifier.test (ThreeColorEncoding.graph x)
    (fieldWord w) (ThreeColorQueryAlgorithm.sampleBits x bits) (vertexCode x)

/-- The complete executable next-query or halt function. -/
def algorithm : VerifierAlg :=
  fun x bits => QueryTree.wordStep (queryList x bits) (verdict x bits)

@[simp] theorem queryList_eq (x bits : List Bool) :
    queryList x bits = ThreeColorQueryAlgorithm.queryList x bits := by
  simp [queryList, ThreeColorQueryAlgorithm.queryList]

@[simp] theorem verdict_eq (x bits : List Bool)
    (w : Fin (ThreeColorBinaryVerifier.proofLength (graphOrder x)) → Bool) :
    verdict x bits w = ThreeColorQueryAlgorithm.verdict x bits w := by
  simp [verdict, ThreeColorQueryAlgorithm.verdict]

@[simp] theorem algorithm_eq : algorithm = ThreeColorQueryAlgorithm.algorithm := by
  funext x bits answers
  simp only [algorithm, ThreeColorQueryAlgorithm.algorithm, queryList_eq]
  congr 2
  funext w
  exact verdict_eq x bits w

/-- The executable protocol implements the named semantic verifier exactly. -/
theorem implementedBy : ThreeColorCanonicalVerifier.verifier.ImplementedBy algorithm := by
  rw [algorithm_eq]
  exact ThreeColorQueryAlgorithm.implementedBy

/-- The executable procedure still uses at most 187 supplied answers. -/
theorem algorithm_halts_after_budget (x bits answers : List Bool) (h : 187 ≤ answers.length) :
    ∃ b, algorithm x bits answers = .inl b := by
  rw [algorithm_eq]
  exact ThreeColorQueryAlgorithm.algorithm_halts_after_budget x bits answers h

end PCP.Algebraic.ComputableThreeColorQueryAlgorithm

namespace PCP.Algebraic.ComputableThreeColorCanonicalVerifier

open ThreeColorCanonicalVerifier

/-- Compile the computed callbacks into the original depth-187 query tree. -/
def tree (x : List Bool) (r : Fin (2 ^ randomBudget x.length)) : QueryTree 187 :=
  QueryTree.compileWordBounded
    (ComputableThreeColorBinaryVerifier.queries
      (ThreeColorEncoding.graph x) (sample x r) (vertexCode x))
    (fun w => ComputableThreeColorBinaryVerifier.test (ThreeColorEncoding.graph x)
      (fieldWord w) (sample x r) (vertexCode x))
    (by
      simpa using ThreeColorBinaryVerifier.queries_length_le
        (ThreeColorEncoding.graph x) (sample x r) (vertexCode x))

/-- One executable verifier for all encoded input graphs. -/
def verifier : Verifier where
  randomness := randomBudget
  queries := 187
  run := tree

@[simp] theorem tree_eq (x : List Bool) (r : Fin (2 ^ randomBudget x.length)) :
    tree x r = ThreeColorCanonicalVerifier.tree x r := by
  simp [tree, ThreeColorCanonicalVerifier.tree]

@[simp] theorem verifier_eq : verifier = ThreeColorCanonicalVerifier.verifier := by
  unfold verifier ThreeColorCanonicalVerifier.verifier
  congr 1
  funext x r
  exact tree_eq x r

/-- The executable tree has the existing precise answer-history implementation. -/
theorem implementedBy : verifier.ImplementedBy ComputableThreeColorQueryAlgorithm.algorithm := by
  rw [verifier_eq]
  exact ComputableThreeColorQueryAlgorithm.implementedBy

end PCP.Algebraic.ComputableThreeColorCanonicalVerifier

namespace PCP.Algebraic.ComputableThreeColorAmplifiedQueryAlgorithm

open ThreeColorAmplifiedQueryAlgorithm

/-- Execute independent copies sequentially with the original repetition bit codec. -/
def algorithmFor (k : ℕ) : VerifierAlg :=
  fun x bits => QueryTree.sequenceStep
    (fun i => (ComputableThreeColorQueryAlgorithm.queryList x (blockBits k x bits i)).map Fin.val)
    (fun i π => ComputableThreeColorQueryAlgorithm.verdict x (blockBits k x bits i)
      (QueryTree.wordOfOracle _ π))

/-- The production repetition count is computed directly from the rational gap. -/
def algorithm : VerifierAlg := algorithmFor ThreeColorAmplifiedVerifier.repetitions

@[simp] theorem algorithmFor_eq (k : ℕ) :
    algorithmFor k = ThreeColorAmplifiedQueryAlgorithm.algorithmFor k := by
  funext x bits answers
  simp only [algorithmFor, ThreeColorAmplifiedQueryAlgorithm.algorithmFor,
    ComputableThreeColorQueryAlgorithm.queryList_eq, ComputableThreeColorQueryAlgorithm.verdict_eq]

@[simp] theorem algorithm_eq : algorithm = ThreeColorAmplifiedQueryAlgorithm.algorithm := by
  simp only [algorithm, ThreeColorAmplifiedQueryAlgorithm.algorithm, algorithmFor_eq]

/-- Exact implementation of the existing amplified semantic verifier. -/
theorem implementedBy : ThreeColorAmplifiedVerifier.verifier.ImplementedBy algorithm := by
  rw [algorithm_eq]
  exact ThreeColorAmplifiedQueryAlgorithm.implementedBy

end PCP.Algebraic.ComputableThreeColorAmplifiedQueryAlgorithm

namespace PCP.Algebraic.ComputableThreeColorAmplifiedVerifier

/-- An executable verifier with perfect completeness and soundness one half. -/
def verifier : Verifier :=
  ComputableThreeColorCanonicalVerifier.verifier.repeat ThreeColorAmplifiedVerifier.repetitions

@[simp] theorem verifier_eq : verifier = ThreeColorAmplifiedVerifier.verifier := by
  simp only [verifier, ThreeColorAmplifiedVerifier.verifier,
    ComputableThreeColorCanonicalVerifier.verifier_eq]

/-- The actual executable amplified answer-history protocol computes these trees. -/
theorem implementedBy :
    verifier.ImplementedBy ComputableThreeColorAmplifiedQueryAlgorithm.algorithm := by
  rw [verifier_eq]
  exact ComputableThreeColorAmplifiedQueryAlgorithm.implementedBy

/-- All established mathematical guarantees now hold for the executable verifier.
The implementation identity is included; a machine-time certificate is not assumed. -/
theorem verification_guarantees :
    0 < ThreeColorAmplifiedVerifier.repetitions ∧
      verifier.queries = ThreeColorAmplifiedVerifier.repetitions * 187 ∧
      verifier.CanonicalRandomness (ThreeColorAmplifiedVerifier.repetitions * 32000000)
        (ThreeColorAmplifiedVerifier.repetitions * 32000000) ∧
      (∀ x, verifier.ReadsBelow x (ThreeColorCanonicalVerifier.proofBound.eval x.length)) ∧
      (∀ x, (ThreeColorEncoding.graph x).Colorable 3 → verifier.CompleteAt x) ∧
      (∀ x, ¬ (ThreeColorEncoding.graph x).Colorable 3 → verifier.SoundAt x (1 / 2)) ∧
      verifier.ImplementedBy ComputableThreeColorAmplifiedQueryAlgorithm.algorithm := by
  rw [verifier_eq]
  obtain ⟨hpos, hq, hr, hp, hc, hs⟩ := ThreeColorAmplifiedVerifier.verification_guarantees
  exact ⟨hpos, hq, hr, hp, hc, hs, ComputableThreeColorAmplifiedQueryAlgorithm.implementedBy⟩

end PCP.Algebraic.ComputableThreeColorAmplifiedVerifier
