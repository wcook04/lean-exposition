/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.SeedBitCompatibility
import PCP.Verifier.FiniteProbability

/-!
# Transporting oracle verifiers along input reductions

The source verifier runs the target verifier on the reduced input and ignores
surplus random bits. Exact uniform prefix sampling preserves acceptance probability.
The algorithm below computes that same seed restriction. Its implementation theorem
does not assert machine time; the concrete reduction and seed-processing certificates
are `PCP.Reduction.NPThreeColorRuntime.of_inNP_program` and
`PCP.Machine.InputReductionRuntime.polyTimeAlg`.
-/

namespace PCP.Verifier.Reduction

open Algebraic BinarySeedPadding SeedBitCompatibility

/-- Restrict an integer seed to its initial `r` little-endian bits. -/
def prefixSeed {r b : ℕ} (h : r ≤ b) (s : Fin (2 ^ b)) : Fin (2 ^ r) :=
  (finSeedEquiv r).symm (BinarySeedPadding.prefix h (finSeedEquiv b s))

@[simp] theorem decodeSeed_bits_prefix {r b : ℕ} (h : r ≤ b) (s : Fin (2 ^ b)) :
    decodeSeed r (bitsOfFin b s) = prefixSeed h s := by
  rw [decodeSeed, prefix_seedOfBits_bitsOfFin h]
  rfl

/-- A supplied source budget is sufficient for every reduced input. -/
def verifier (V : Verifier) (f : List Bool → List Bool) (budget : ℕ → ℕ)
    (h : ∀ x, V.randomness (f x).length ≤ budget x.length) : Verifier where
  randomness := budget
  queries := V.queries
  run x s := V.run (f x) (prefixSeed (h x) s)

theorem rejectionProb_eq (V : Verifier) (f : List Bool → List Bool) (budget : ℕ → ℕ)
    (h : ∀ x, V.randomness (f x).length ≤ budget x.length) (x : List Bool) (π : ProofOracle) :
    (verifier V f budget h).rejectionProb x π = V.rejectionProb (f x) π := by
  let test := fun s : Seed (V.randomness (f x).length) =>
    (V.run (f x) ((finSeedEquiv _).symm s)).eval π
  have hp := relativeDistance_finSeed_prefix (h x) test (fun _ => true)
  have he := relativeDistance_comp_equiv (finSeedEquiv (V.randomness (f x).length))
    test (fun _ => true)
  exact hp.trans (by simpa only [test, Equiv.symm_apply_apply, rejectionProb] using he.symm)

/-- The reduction and seed padding preserve the exact normalized acceptance probability. -/
theorem accProb_eq (V : Verifier) (f : List Bool → List Bool) (budget : ℕ → ℕ)
    (h : ∀ x, V.randomness (f x).length ≤ budget x.length) (x : List Bool) (π : ProofOracle) :
    (verifier V f budget h).accProb x π = V.accProb (f x) π := by
  rw [accProb_eq_one_sub_rejectionProb, accProb_eq_one_sub_rejectionProb, rejectionProb_eq]

theorem completeAt_iff (V : Verifier) (f : List Bool → List Bool) (budget : ℕ → ℕ)
    (h : ∀ x, V.randomness (f x).length ≤ budget x.length) (x : List Bool) :
    (verifier V f budget h).CompleteAt x ↔ V.CompleteAt (f x) := by
  simp only [CompleteAt, accProb_eq]

theorem soundAt_iff (V : Verifier) (f : List Bool → List Bool) (budget : ℕ → ℕ)
    (h : ∀ x, V.randomness (f x).length ≤ budget x.length) (x : List Bool) (s : ℚ) :
    (verifier V f budget h).SoundAt x s ↔ V.SoundAt (f x) s := by
  simp only [SoundAt, accProb_eq]

theorem readsBelow (V : Verifier) (f : List Bool → List Bool) (budget : ℕ → ℕ)
    (h : ∀ x, V.randomness (f x).length ≤ budget x.length) (x : List Bool) {N : ℕ}
    (hN : V.ReadsBelow (f x) N) : (verifier V f budget h).ReadsBelow x N :=
  fun s => hN (prefixSeed (h x) s)

/-- The exact answer-history protocol, including restriction to the target seed width. -/
def algorithm (alg : VerifierAlg) (f : List Bool → List Bool) (width : ℕ → ℕ) : VerifierAlg :=
  fun x random answers =>
    let y := f x
    alg y (bitsOfFin (width y.length) (decodeSeed (width y.length) random)) answers

/-- The protocol reproduces the transported decision tree on every actual random string. -/
theorem implementedBy (V : Verifier) (alg : VerifierAlg) (hi : V.ImplementedBy alg)
    (f : List Bool → List Bool) (budget : ℕ → ℕ)
    (h : ∀ x, V.randomness (f x).length ≤ budget x.length) :
    (verifier V f budget h).ImplementedBy (algorithm alg f V.randomness) := by
  intro x s
  change Fin (2 ^ budget x.length) at s
  change QueryTree.ofStep
    (alg (f x) (bitsOfFin _ (decodeSeed _ (bitsOfFin (budget x.length) s)))) V.queries [] = _
  rw [decodeSeed_bits_prefix (h x)]
  exact hi (f x) (prefixSeed (h x) s)

end PCP.Verifier.Reduction
