/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Verifier.QueryTreeConjunction
import PCP.Verifier.FiniteProbability
import PCP.Algebraic.FiniteRepetition

/-!
# Independent repetition in the oracle-verifier model

The repeated verifier uses independent blocks of random bits and the same proof
oracle in every copy. Its acceptance probability is exactly the corresponding
power. Query depth and canonical randomness multiply by the repetition count;
the proof-address bound and perfect completeness are preserved.
-/

namespace PCP.Verifier

open Algebraic Algebraic.FiniteRepetition

/-- Accept only if all independently seeded copies of the same verifier accept. -/
def «repeat» (V : Verifier) (k : ℕ) : Verifier where
  randomness n := k * V.randomness n
  queries := k * V.queries
  run x r := QueryTree.all (fun i => V.run x (blockSeedEquiv k (V.randomness x.length) r i))

@[simp] theorem repeat_queries (V : Verifier) (k : ℕ) :
    (V.repeat k).queries = k * V.queries := rfl

@[simp] theorem repeat_randomness (V : Verifier) (k n : ℕ) :
    (V.repeat k).randomness n = k * V.randomness n := rfl

theorem repeat_eval (V : Verifier) (k : ℕ) (x : List Bool)
    (r : Fin (2 ^ (k * V.randomness x.length))) (π : ProofOracle) :
    ((V.repeat k).run x r).eval π =
      allTest k (fun s => (V.run x s).eval π) (blockSeedEquiv k (V.randomness x.length) r) :=
  QueryTree.eval_all _ _

/-- The product probability is proved for the actual shared proof oracle. -/
theorem repeat_accProb (V : Verifier) (k : ℕ) (x : List Bool) (π : ProofOracle) :
    (V.repeat k).accProb x π = (V.accProb x π) ^ k := by
  rw [accProb_eq_relativeAgreement, accProb_eq_relativeAgreement]
  simp only [«repeat», QueryTree.eval_all]
  exact relativeAgreement_allTest_fin k (V.randomness x.length) (fun s => (V.run x s).eval π)

theorem repeat_canonicalRandomness (V : Verifier) (k : ℕ) {a b : ℕ}
    (h : V.CanonicalRandomness a b) : (V.repeat k).CanonicalRandomness (k * a) (k * b) := by
  intro n
  rw [repeat_randomness, h n]
  ring

/-- Repetition reads the same proof; its length does not multiply. -/
theorem repeat_readsBelow (V : Verifier) (k : ℕ) (x : List Bool) {N : ℕ}
    (h : V.ReadsBelow x N) : (V.repeat k).ReadsBelow x N := by
  intro r a ha
  exact QueryTree.addresses_all_lt _ (fun i => h _) a ha

theorem repeat_completeAt (V : Verifier) (k : ℕ) (x : List Bool) (h : V.CompleteAt x) :
    (V.repeat k).CompleteAt x := by
  obtain ⟨π, hπ⟩ := h
  refine ⟨π, ?_⟩
  rw [repeat_accProb, hπ, one_pow]

theorem repeat_soundAt (V : Verifier) (k : ℕ) (x : List Bool) {s : ℚ}
    (h : V.SoundAt x s) : (V.repeat k).SoundAt x (s ^ k) := by
  intro π
  rw [repeat_accProb]
  exact pow_le_pow_left₀ (V.accProb_nonneg x π) (h π) k

end PCP.Verifier
