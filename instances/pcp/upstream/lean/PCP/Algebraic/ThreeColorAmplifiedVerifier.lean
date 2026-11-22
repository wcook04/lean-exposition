/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorCanonicalVerifier
import PCP.Algebraic.ThreeColorGap
import PCP.Algebraic.RationalRepetitionBound
import PCP.Verifier.Repetition

/-!
# Soundness one half for the encoded three-color verifier

A single positive repetition count depends only on the already proved rational
gap. It gives soundness at most one half while preserving perfect completeness,
a fixed polynomial proof-address bound, and canonical logarithmic randomness.

This file proves the semantic verifier guarantees. The concrete implementation
is certified by `PCP.Lang.ThreeColorRuntime.polyTimeAlg`, and
`PCP.Algebraic.ThreeColorFinalAssembly.of_runtime` combines it with the certified
NP reduction to obtain the final PCP theorem.
-/

namespace PCP.Algebraic.ThreeColorAmplifiedVerifier

/-- A fixed positive repetition count, independent of every input and proof. -/
def repetitions : ℕ := RationalRepetitionBound.repetitions ThreeColorBinaryVerifier.gap

theorem repetitions_pos : 0 < repetitions :=
  RationalRepetitionBound.repetitions_pos ThreeColorBinaryVerifier.gap_pos

theorem acceptance_pow_le_half : (1 - ThreeColorBinaryVerifier.gap) ^ repetitions ≤ 1 / 2 :=
  RationalRepetitionBound.acceptance_pow_le_half ThreeColorBinaryVerifier.gap_pos
    ThreeColorGap.gap_le_one

/-- The same canonical verifier repeated a fixed number of times on the same proof. -/
noncomputable def verifier : Verifier := ThreeColorCanonicalVerifier.verifier.repeat repetitions

theorem queries_eq : verifier.queries = repetitions * 187 := rfl

theorem canonicalRandomness :
    verifier.CanonicalRandomness (repetitions * 32000000) (repetitions * 32000000) :=
  Verifier.repeat_canonicalRandomness _ _ ThreeColorCanonicalVerifier.canonicalRandomness

theorem readsBelow (x : List Bool) :
    verifier.ReadsBelow x (ThreeColorCanonicalVerifier.proofBound.eval x.length) :=
  Verifier.repeat_readsBelow _ _ _ (ThreeColorCanonicalVerifier.readsBelow x)

theorem completeAt (x : List Bool) (hx : (ThreeColorEncoding.graph x).Colorable 3) :
    verifier.CompleteAt x :=
  Verifier.repeat_completeAt _ _ _ (ThreeColorCanonicalVerifier.completeAt x hx)

/-- Standard constant soundness for every proof oracle. -/
theorem soundAt (x : List Bool) (hx : ¬ (ThreeColorEncoding.graph x).Colorable 3) :
    verifier.SoundAt x (1 / 2) := by
  have h := Verifier.repeat_soundAt _ repetitions x (ThreeColorCanonicalVerifier.soundAt x hx)
  intro π
  exact (h π).trans acceptance_pow_le_half

/-- Encoding an ordinary finite graph gives the intended completeness statement. -/
theorem completeAt_encode {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : G.Colorable 3) : verifier.CompleteAt (ThreeColorEncoding.encode G) :=
  completeAt _ ((ThreeColorEncoding.decode_encode_colorable_iff G 3).mpr hG)

/-- Encoding an ordinary finite graph gives the intended soundness statement. -/
theorem soundAt_encode {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : ¬ G.Colorable 3) : verifier.SoundAt (ThreeColorEncoding.encode G) (1 / 2) :=
  soundAt _ (fun h => hG ((ThreeColorEncoding.decode_encode_colorable_iff G 3).mp h))

/-- One actual verifier has all mathematical resource and probability properties,
including the standard soundness target. Efficiency and NP transfer are not asserted. -/
theorem verification_guarantees :
    0 < repetitions ∧ verifier.queries = repetitions * 187 ∧
      verifier.CanonicalRandomness (repetitions * 32000000) (repetitions * 32000000) ∧
      (∀ x, verifier.ReadsBelow x (ThreeColorCanonicalVerifier.proofBound.eval x.length)) ∧
      (∀ x, (ThreeColorEncoding.graph x).Colorable 3 → verifier.CompleteAt x) ∧
      (∀ x, ¬ (ThreeColorEncoding.graph x).Colorable 3 → verifier.SoundAt x (1 / 2)) :=
  ⟨repetitions_pos, queries_eq, canonicalRandomness, readsBelow, completeAt, soundAt⟩

end PCP.Algebraic.ThreeColorAmplifiedVerifier
