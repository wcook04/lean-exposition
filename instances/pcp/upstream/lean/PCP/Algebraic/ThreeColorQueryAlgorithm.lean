/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorCanonicalVerifier
import PCP.Algebraic.SeedBitCompatibility
import PCP.Verifier.QueryListAlgorithm

/-!
# The query-by-query interface of the algebraic verifier

The random seed is read from the actual little-endian input bit list. The
answer-history procedure asks for the actual query list and then evaluates the
verdict on those answers. Unfolding this procedure reproduces the canonical
verifier's decision tree exactly, including all hypothetical answer histories.

The semantic query and verdict callbacks use noncomputable polynomial query
transformations. The theorem `implementedBy` proves the exact step-function
identity. An executable counterpart is identified with this procedure by
`PCP.Algebraic.ComputableThreeColorQueryAlgorithm.algorithm_eq`; the amplified
production algorithm has the concrete polynomial-time certificate
`PCP.Lang.ThreeColorRuntime.polyTimeAlg`.
-/

namespace PCP.Algebraic.ThreeColorQueryAlgorithm

open ThreeColorCanonicalVerifier

/-- Read only the initial seed cells actually used by the algebraic test. -/
def sampleBits (x bits : List Bool) : ThreeColorBinaryVerifier.Seed (graphOrder x) :=
  SeedBitCompatibility.seedOfBits (ThreeColorBinaryVerifier.randomBits (graphOrder x)) bits

/-- The physical random-bit input agrees with the existing exact finite sampler. -/
theorem sampleBits_bitsOfFin (x : List Bool) (r : Fin (2 ^ randomBudget x.length)) :
    sampleBits x (bitsOfFin (randomBudget x.length) r) = sample x r :=
  SeedBitCompatibility.prefix_seedOfBits_bitsOfFin (randomBits_le_budget x) r

/-- Actual finite-word queries as a function of the supplied random-bit list. -/
noncomputable def queryList (x bits : List Bool) :
    List (Fin (ThreeColorBinaryVerifier.proofLength (graphOrder x))) :=
  ThreeColorBinaryVerifier.queries (ThreeColorEncoding.graph x) (sampleBits x bits) (vertexCode x)

theorem queryList_length_le (x bits : List Bool) : (queryList x bits).length ≤ 187 :=
  ThreeColorBinaryVerifier.queries_length_le _ _ (vertexCode x)

/-- The existing mathematical verdict on a finite Boolean proof word. -/
noncomputable def verdict (x bits : List Bool)
    (w : Fin (ThreeColorBinaryVerifier.proofLength (graphOrder x)) → Bool) : Bool :=
  ThreeColorBinaryVerifier.test (ThreeColorEncoding.graph x)
    (fieldWord w) (sampleBits x bits) (vertexCode x)

/-- The concrete answer-history protocol, with its query and verdict callbacks explicit. -/
noncomputable def algorithm : VerifierAlg :=
  fun x bits => QueryTree.wordStep (queryList x bits) (verdict x bits)

/-- Before the list is exhausted, the next address is its next actual finite-word index. -/
theorem algorithm_next (x bits answers : List Bool)
    (h : answers.length < (queryList x bits).length) :
    algorithm x bits answers = .inr (queryList x bits)[answers.length].val := by
  have h' : answers.length < ((queryList x bits).map Fin.val).length := by simpa using h
  simpa only [algorithm, QueryTree.wordStep, List.getElem_map] using
    QueryTree.listStep_next ((queryList x bits).map Fin.val)
      (fun π => verdict x bits (QueryTree.wordOfOracle _ π)) answers h'

/-- After all requested answers, the procedure returns a verdict without any more queries. -/
theorem algorithm_halts (x bits answers : List Bool)
    (h : (queryList x bits).length ≤ answers.length) :
    ∃ b, algorithm x bits answers = .inl b := by
  refine ⟨verdict x bits (QueryTree.wordOfOracle _
    (QueryTree.answersOracle ((queryList x bits).map Fin.val) answers)), ?_⟩
  exact QueryTree.listStep_halt _ _ _ (by simpa using h)

/-- In particular, every supplied seed terminates after at most 187 proof answers. -/
theorem algorithm_halts_after_budget (x bits answers : List Bool) (h : 187 ≤ answers.length) :
    ∃ b, algorithm x bits answers = .inl b :=
  algorithm_halts x bits answers ((queryList_length_le x bits).trans h)

/-- Exact agreement with the model's prescribed random-bit handling and decision tree.
The production amplified algorithm's machine-time certificate is proved downstream as
`PCP.Lang.ThreeColorRuntime.polyTimeAlg`. -/
theorem implementedBy : ThreeColorCanonicalVerifier.verifier.ImplementedBy algorithm := by
  intro x r
  change Fin (2 ^ randomBudget x.length) at r
  change QueryTree.ofStep (algorithm x (bitsOfFin (randomBudget x.length) r)) 187 [] = tree x r
  unfold algorithm queryList verdict
  rw [sampleBits_bitsOfFin]
  exact QueryTree.ofStep_wordStep _ _ _

/-- Every run of the history procedure reads the original physical query list, in order. -/
theorem queryTrace (x : List Bool) (r : Fin (2 ^ randomBudget x.length)) (π : ProofOracle) :
    (QueryTree.ofStep (algorithm x (bitsOfFin (randomBudget x.length) r)) 187 []).queryTrace π =
      (queryList x (bitsOfFin (randomBudget x.length) r)).map Fin.val := by
  exact QueryTree.queryTrace_ofStep_listStep _ _
    (by simpa using queryList_length_le x (bitsOfFin (randomBudget x.length) r)) π

end PCP.Algebraic.ThreeColorQueryAlgorithm
