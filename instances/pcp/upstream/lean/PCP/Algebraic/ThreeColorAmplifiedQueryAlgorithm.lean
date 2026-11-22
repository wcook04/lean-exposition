/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorQueryAlgorithm
import PCP.Algebraic.ThreeColorAmplifiedVerifier

/-!
# Sequential answer-history implementation of the amplified verifier

Each copy consumes its own query list from the shared answer history, then
either rejects or proceeds to the next independently seeded copy. The random
input is split by the same explicit block codec used in verifier repetition.
Unfolding this procedure reproduces the actual amplified tree exactly.

The semantic verdict callbacks use noncomputable polynomial query transformations,
and the repetition count is computed from the gap. This file proves the exact
implementation identity. The executable counterpart is identified with this
procedure by `PCP.Algebraic.ComputableThreeColorAmplifiedQueryAlgorithm.algorithm_eq`,
and its concrete polynomial-time certificate is
`PCP.Lang.ThreeColorRuntime.polyTimeAlg`.
-/

namespace PCP.QueryTree

private theorem weaken_trans_eq {d e f : ℕ} (hde : d ≤ e) (hef : e ≤ f)
    (T : QueryTree d) : weaken hef (weaken hde T) = weaken (hde.trans hef) T := by
  induction T generalizing e f with
  | leaf b => simp only [weaken]
  | @query d a l r hl hr =>
    cases e with
    | zero => omega
    | succ e =>
      cases f with
      | zero => omega
      | succ f => simp only [weaken, hl, hr]

private theorem weaken_self_eq {d : ℕ} (T : QueryTree d) : weaken le_rfl T = T := by
  induction T with
  | leaf b => simp only [weaken]
  | query a l r hl hr => simp only [weaken, hl, hr]

private theorem ofStep_constant (b : Bool) (d : ℕ) (as : List Bool) :
    ofStep (fun _ => .inl b) d as = .leaf b := by cases d <;> rfl

/-- Consume one list of query answers; continue only when its verdict accepts. -/
def thenStep : List ℕ → (ProofOracle → Bool) →
    (List Bool → Bool ⊕ ℕ) → List Bool → Bool ⊕ ℕ
  | [], f, next, as => if f (fun _ => false) then next as else .inl false
  | a :: _, _, _, [] => .inr a
  | a :: qs, f, next, b :: bs => thenStep qs (fun π => f (Function.update π a b)) next bs

private theorem ofStep_thenStep_cons (a : ℕ) (qs : List ℕ) (f : ProofOracle → Bool)
    (next : List Bool → Bool ⊕ ℕ) (b : Bool) (d : ℕ) (as : List Bool) :
    ofStep (thenStep (a :: qs) f next) d (b :: as) =
      ofStep (thenStep qs (fun π => f (Function.update π a b)) next) d as :=
  ofStep_prefix (thenStep (a :: qs) f next) [b] d as

private theorem ofStep_thenStep (qs : List ℕ) (f : ProofOracle → Bool)
    {p e : ℕ} (hqs : qs.length ≤ p) (next : List Bool → Bool ⊕ ℕ) (U : QueryTree e)
    (hnext : ∀ {D : ℕ} (h : e ≤ D), ofStep next D [] = weaken h U)
    {D : ℕ} (hD : p + e ≤ D) :
    ofStep (thenStep qs f next) D [] =
      weaken hD (andThen (compileBounded qs f hqs) U) := by
  induction qs generalizing p D f with
  | nil =>
    cases hb : f (fun _ => false)
    · simp [thenStep, hb, ofStep_constant, compileBounded, compile, andThen, weaken]
    · simp only [thenStep, hb, ite_true, compileBounded, compile, weaken, andThen]
      rw [hnext (by omega), weaken_trans_eq]
  | cons a qs ih =>
    cases p with
    | zero => simp at hqs
    | succ p =>
      cases D with
      | zero => omega
      | succ D =>
        simp only [ofStep, thenStep, List.nil_append, compileBounded, compile, weaken,
          andThen, weaken_trans_eq]
        congr 1
        · rw [ofStep_thenStep_cons]
          exact ih _ (by simpa using hqs) (by omega)
        · rw [ofStep_thenStep_cons]
          exact ih _ (by simpa using hqs) (by omega)

/-- Run the supplied query-list procedures in order, sharing the actual proof oracle. -/
def sequenceStep : {k : ℕ} → (Fin k → List ℕ) →
    (Fin k → ProofOracle → Bool) → List Bool → Bool ⊕ ℕ
  | 0, _, _, _ => .inl true
  | k + 1, qs, fs, as =>
      thenStep (qs 0) (fs 0) (sequenceStep (fun i : Fin k => qs i.succ)
        (fun i => fs i.succ)) as

/-- A surplus query budget is unused: the sequential history protocol equals the
weakened conjunction of the concrete per-copy compilers. -/
theorem ofStep_sequenceStep_le {k q D : ℕ} (qs : Fin k → List ℕ)
    (fs : Fin k → ProofOracle → Bool) (hq : ∀ i, (qs i).length ≤ q) (hD : k * q ≤ D) :
    ofStep (sequenceStep qs fs) D [] =
      weaken hD (all (fun i => compileBounded (qs i) (fs i) (hq i))) := by
  induction k generalizing D with
  | zero => simp [sequenceStep, ofStep_constant, all, weaken]
  | succ k ih =>
    change ofStep (thenStep (qs 0) (fs 0)
      (sequenceStep (fun i : Fin k => qs i.succ) (fun i => fs i.succ))) D [] = _
    rw [ofStep_thenStep (qs 0) (fs 0) (hq 0) _
      (all (fun i : Fin k => compileBounded (qs i.succ) (fs i.succ) (hq i.succ)))
      (fun h => ih _ _ (fun i => hq i.succ) h) (by simpa [Nat.add_mul, Nat.add_comm] using hD)]
    simp only [all, weaken_trans_eq]

theorem ofStep_sequenceStep {k q : ℕ} (qs : Fin k → List ℕ)
    (fs : Fin k → ProofOracle → Bool) (hq : ∀ i, (qs i).length ≤ q) :
    ofStep (sequenceStep qs fs) (k * q) [] =
      all (fun i => compileBounded (qs i) (fs i) (hq i)) := by
  rw [ofStep_sequenceStep_le qs fs hq le_rfl, weaken_self_eq]

end PCP.QueryTree

namespace PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm

open ThreeColorCanonicalVerifier

/-- Decode and split the supplied random-bit list with the actual repetition codec. -/
def blockBits (k : ℕ) (x bits : List Bool) (i : Fin k) : List Bool :=
  bitsOfFin (randomBudget x.length)
    (FiniteRepetition.blockSeedEquiv k (randomBudget x.length)
      (SeedBitCompatibility.decodeSeed (k * randomBudget x.length) bits) i)

@[simp] theorem blockBits_bitsOfFin (k : ℕ) (x : List Bool)
    (r : Fin (2 ^ (k * randomBudget x.length))) (i : Fin k) :
    blockBits k x (bitsOfFin (k * randomBudget x.length) r) i =
      bitsOfFin (randomBudget x.length)
        (FiniteRepetition.blockSeedEquiv k (randomBudget x.length) r i) := by
  simp [blockBits]

/-- Explicit sequential repetition of the real query-list and verdict callbacks. -/
noncomputable def algorithmFor (k : ℕ) : VerifierAlg :=
  fun x bits => QueryTree.sequenceStep
    (fun i => (ThreeColorQueryAlgorithm.queryList x (blockBits k x bits i)).map Fin.val)
    (fun i π => ThreeColorQueryAlgorithm.verdict x (blockBits k x bits i)
      (QueryTree.wordOfOracle _ π))

/-- Every finite repetition count has the same exact step-function implementation. -/
theorem implementedByFor (k : ℕ) :
    (ThreeColorCanonicalVerifier.verifier.repeat k).ImplementedBy (algorithmFor k) := by
  intro x r
  change Fin (2 ^ (k * randomBudget x.length)) at r
  change QueryTree.ofStep (algorithmFor k x (bitsOfFin (k * randomBudget x.length) r))
    (k * 187) [] = _
  unfold algorithmFor
  rw [QueryTree.ofStep_sequenceStep _ _ (fun i => by
    simpa only [List.length_map] using ThreeColorQueryAlgorithm.queryList_length_le
      x (blockBits k x (bitsOfFin (k * randomBudget x.length) r) i))]
  change QueryTree.all _ = QueryTree.all _
  apply congrArg (fun ts : Fin k → QueryTree 187 => QueryTree.all ts)
  funext i
  rw [blockBits_bitsOfFin]
  exact (QueryTree.ofStep_wordStep _ _
    (ThreeColorQueryAlgorithm.queryList_length_le _ _)).symm.trans
    (ThreeColorQueryAlgorithm.implementedBy x
      (FiniteRepetition.blockSeedEquiv k (randomBudget x.length) r i))

/-- The fixed amplified verifier's actual answer-history algorithm. -/
noncomputable def algorithm : VerifierAlg := algorithmFor ThreeColorAmplifiedVerifier.repetitions

theorem implementedBy : ThreeColorAmplifiedVerifier.verifier.ImplementedBy algorithm :=
  implementedByFor ThreeColorAmplifiedVerifier.repetitions

end PCP.Algebraic.ThreeColorAmplifiedQueryAlgorithm
