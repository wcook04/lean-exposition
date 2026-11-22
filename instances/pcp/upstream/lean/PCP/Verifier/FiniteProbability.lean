/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Verifier.Definition
import PCP.Algebraic.Distance

/-!
# Finite-distance probabilities for oracle verifiers

The verifier model's acceptance count is identified with relative agreement on
its actual finite random-bit space. This connects algebraic rejection bounds to
the model's `CompleteAt` and `SoundAt` predicates without changing normalization.
-/

namespace PCP.Verifier

open Algebraic

/-- The actual rejection probability on the verifier's uniform random strings. -/
def rejectionProb (V : Verifier) (x : List Bool) (π : ProofOracle) : ℚ :=
  relativeDistance (fun r => (V.run x r).eval π) (fun _ => true)

theorem accProb_eq_relativeAgreement (V : Verifier) (x : List Bool) (π : ProofOracle) :
    V.accProb x π = relativeAgreement (fun r => (V.run x r).eval π) (fun _ => true) := by
  simp only [accProb, acceptingRandomness, relativeAgreement, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat]

theorem accProb_add_rejectionProb (V : Verifier) (x : List Bool) (π : ProofOracle) :
    V.accProb x π + V.rejectionProb x π = 1 := by
  rw [accProb_eq_relativeAgreement]
  exact relativeAgreement_add_relativeDistance _ _

theorem accProb_eq_one_sub_rejectionProb (V : Verifier) (x : List Bool) (π : ProofOracle) :
    V.accProb x π = 1 - V.rejectionProb x π := by
  have h := accProb_add_rejectionProb V x π
  linarith

/-- An actual rejection lower bound gives soundness with the complementary error. -/
theorem soundAt_of_rejectionProb_ge (V : Verifier) (x : List Bool) {δ : ℚ}
    (h : ∀ π, δ ≤ V.rejectionProb x π) : V.SoundAt x (1 - δ) := by
  intro π
  rw [accProb_eq_one_sub_rejectionProb]
  exact sub_le_sub_left (h π) 1

end PCP.Verifier
