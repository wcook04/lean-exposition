import PCP.Complexity.AmplifiedProtocolSetupCost
import PCP.Complexity.ThreeColorQuerySize
import PCP.Algebraic.AmplifiedSlicedAlgorithm

/-!
# Production runtime assembly from the concrete base callback

The public parser, canonical random budget, query storage, repetition protocol,
and machine compilation are discharged here. Only the concrete base callback's
exact behavior and charged polynomial cost remain as explicit premises.
-/

namespace PCP.Lang.ThreeColorAmplifiedRuntime

open PCP.Algebraic PCP.Machine AmplifiedStream

abbrev queries (x bits : List Bool) : List ℕ :=
  (ComputableThreeColorQueryAlgorithm.queryList x bits).map Fin.val

abbrev verdict (x bits : List Bool) (π : PCP.ProofOracle) : Bool :=
  ComputableThreeColorQueryAlgorithm.verdict x bits (QueryTree.wordOfOracle _ π)

/-- Semantic query storage follows from the already proved production proof bound. -/
theorem resources (P : Stmt 400 128) (C d : ℕ)
    (hcost : ∀ x bits answers : List Bool,
      (P.run (AmplifiedWorkspace.initial (x.map Bool.toNat) (bits.map Bool.toNat)
        (answers.map Bool.toNat))).2 ≤ C*(x.length+bits.length+answers.length+1)^d) :
    ∃ C' d', PolynomialResources P queries C' d' := by
  obtain ⟨Cq, dq, hq⟩ := ThreeColorQuerySize.polynomial_queryList_size
  refine ⟨C+Cq, max d dq, ?_⟩
  constructor
  · intro x bits answers
    exact (hcost x bits answers).trans (Nat.mul_le_mul (Nat.le_add_right C Cq)
      (Nat.pow_le_pow_right (by omega) (le_max_left d dq)))
  · intro x bits
    exact (hq x bits).trans (Nat.mul_le_mul (Nat.le_add_left Cq C)
      ((Nat.pow_le_pow_left (by omega : x.length+1 ≤ x.length+bits.length+1) dq).trans
        (Nat.pow_le_pow_right (by omega) (le_max_right d dq))))

/-- Every fixed repetition count is realized by the actual compiled protocol. -/
theorem algorithmFor_of_callback (P : Stmt 400 128) (hc : Correct P queries verdict)
    (C d : ℕ)
    (hcost : ∀ x bits answers : List Bool,
      (P.run (AmplifiedWorkspace.initial (x.map Bool.toNat) (bits.map Bool.toNat)
        (answers.map Bool.toNat))).2 ≤ C*(x.length+bits.length+answers.length+1)^d)
    (k : ℕ) : PolyTimeAlg (ComputableThreeColorAmplifiedQueryAlgorithm.algorithmFor k) := by
  obtain ⟨C', d', hR⟩ := resources P C d hcost
  have h := AmplifiedProtocol.polyTimeAlg AmplifiedProtocolSetup.program
    AmplifiedProtocolSetup.setup AmplifiedProtocolSetup.costConstant 2
    AmplifiedProtocolSetup.program_cost P queries verdict hc C' d' hR k
  have he : ComputableThreeColorAmplifiedQueryAlgorithm.algorithmFor k =
      (fun x bits answers => ThreeColorAmplifiedQueryAlgorithm.slicedSequence
        (ThreeColorCanonicalVerifier.randomBudget x.length)
        (queries x) (verdict x) k bits answers) := by
    funext x bits answers
    exact ThreeColorAmplifiedQueryAlgorithm.computableAlgorithmFor_sliced k x bits answers
  rwa [he]

/-- This is the production fixed amplified verifier, with no parser or query-size premise. -/
theorem of_callback (P : Stmt 400 128) (hc : Correct P queries verdict) (C d : ℕ)
    (hcost : ∀ x bits answers : List Bool,
      (P.run (AmplifiedWorkspace.initial (x.map Bool.toNat) (bits.map Bool.toNat)
        (answers.map Bool.toNat))).2 ≤ C*(x.length+bits.length+answers.length+1)^d) :
    PolyTimeAlg ComputableThreeColorAmplifiedQueryAlgorithm.algorithm :=
  algorithmFor_of_callback P hc C d hcost ThreeColorAmplifiedVerifier.repetitions

end PCP.Lang.ThreeColorAmplifiedRuntime
