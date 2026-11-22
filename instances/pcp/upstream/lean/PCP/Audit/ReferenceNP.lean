/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.ReferenceNPConverse

/-!
# Independent definition checks for the reference complexity class

These checks pin the imported NP class to nondeterministic polynomial time and
retain both parts of its decision contract: every branch halts, and membership
is equivalent to the existence of an accepting branch.
-/

namespace PCP.Audit.ReferenceNP

example : Complexity.NP = ⋃ k : ℕ, Complexity.NTIME (· ^ k) := rfl

example (n : ℕ) (tm : Complexity.NTM n) (L : Complexity.Language) (T : ℕ → ℕ) :
    tm.DecidesInTime L T ↔
      (∀ x (choices : Fin (T x.length) → Bool),
        tm.halted (tm.trace (T x.length) choices (tm.initCfg x))) ∧
      (∀ x, x ∈ L ↔ ∃ choices : Fin (T x.length) → Bool,
        tm.halted (tm.trace (T x.length) choices (tm.initCfg x)) ∧
        (tm.trace (T x.length) choices (tm.initCfg x)).output.cells 1 = Complexity.Γ.one) :=
  Iff.rfl

/-- Independent intended signature of the forward reference-class inclusion. -/
def IntendedInclusionType : Prop :=
  ∀ {L : Complexity.Language}, L ∈ Complexity.NP → PCP.InNP PCP.Machine.PolyTimeRel L

/-- Independent intended converse, with the concrete source machine class. -/
def IntendedConverseType : Prop :=
  ∀ {L : Complexity.Language}, PCP.InNP PCP.Machine.PolyTimeRel L → L ∈ Complexity.NP

/-- The comparison concerns exactly the same binary language in both definitions. -/
def IntendedEquivalenceType : Prop :=
  ∀ {L : Complexity.Language}, PCP.InNP PCP.Machine.PolyTimeRel L ↔ L ∈ Complexity.NP

/-- Independent longhand PCP guarantee, with the exact upstream NP premise. -/
def IntendedPCPType : Prop :=
  ∀ (L : Complexity.Language), L ∈ Complexity.NP →
    ∃ (V : PCP.Verifier) (alg : PCP.VerifierAlg) (a b q : ℕ) (p : Polynomial ℕ),
      PCP.Machine.PolyTimeAlg alg ∧
      V.ImplementedBy alg ∧
      V.queries = q ∧
      V.CanonicalRandomness a b ∧
      (∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) ∧
      (∀ x : List Bool, x ∈ L → V.CompleteAt x) ∧
      (∀ x : List Bool, x ∉ L → V.SoundAt x (1 / 2))

example : IntendedInclusionType := PCP.ReferenceNP.to_inNP

example : IntendedConverseType := PCP.ReferenceNP.of_inNP

example : IntendedEquivalenceType := PCP.ReferenceNP.inNP_iff_mem

example : IntendedPCPType := PCP.ReferenceNP.np_subset_pcp

end PCP.Audit.ReferenceNP
