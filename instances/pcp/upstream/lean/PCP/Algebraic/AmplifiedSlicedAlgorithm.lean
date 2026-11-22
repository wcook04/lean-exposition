import PCP.Algebraic.AmplifiedSequenceSlicing
import PCP.Algebraic.AmplifiedSeedSlicing

/-! A streaming formulation of the exact fixed repetition protocol. -/

namespace PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

/-- Each copy uses one padded random block and consumes only its own answers. -/
def slicedSequence (b : ℕ) (qs : List Bool → List ℕ)
    (fs : List Bool → ProofOracle → Bool) : ℕ → List Bool → List Bool → Bool ⊕ ℕ
  | 0, _, _ => .inl true
  | k+1, bits, answers => QueryTree.thenStep (qs (paddedBits b bits))
      (fs (paddedBits b bits)) (slicedSequence b qs fs k (bits.drop b)) answers

theorem sequenceStep_sliced (b k : ℕ) (qs : List Bool → List ℕ)
    (fs : List Bool → ProofOracle → Bool) (bits answers : List Bool) :
    QueryTree.sequenceStep (fun i : Fin k => qs (paddedBits b (bits.drop (b*i.val))))
      (fun i => fs (paddedBits b (bits.drop (b*i.val)))) answers =
        slicedSequence b qs fs k bits answers := by
  induction k generalizing bits answers with
  | zero => rfl
  | succ k ih =>
      simp only [QueryTree.sequenceStep, slicedSequence, Fin.val_zero, Nat.mul_zero,
        List.drop_zero]
      congr 1
      funext rest
      rw [← ih]
      congr 1 <;> funext i <;>
        simp [List.drop_drop, Nat.mul_add, Nat.add_comm]

theorem computableAlgorithmFor_sliced (k : ℕ) (x bits answers : List Bool) :
    ComputableThreeColorAmplifiedQueryAlgorithm.algorithmFor k x bits answers =
      slicedSequence (ThreeColorCanonicalVerifier.randomBudget x.length)
        (fun bs => (ComputableThreeColorQueryAlgorithm.queryList x bs).map Fin.val)
        (fun bs π => ComputableThreeColorQueryAlgorithm.verdict x bs
          (QueryTree.wordOfOracle _ π)) k bits answers := by
  unfold ComputableThreeColorAmplifiedQueryAlgorithm.algorithmFor
  simp only [blockBits_eq_padded]
  exact sequenceStep_sliced (ThreeColorCanonicalVerifier.randomBudget x.length) k
    (fun bs => (ComputableThreeColorQueryAlgorithm.queryList x bs).map Fin.val)
    (fun bs π => ComputableThreeColorQueryAlgorithm.verdict x bs
      (QueryTree.wordOfOracle _ π)) bits answers

end PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm
