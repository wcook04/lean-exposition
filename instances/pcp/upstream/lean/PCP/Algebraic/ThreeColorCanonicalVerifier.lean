/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Algebraic.ThreeColorBinaryVerifier
import PCP.Algebraic.ThreeColorEncoding
import PCP.Algebraic.BinarySeedPadding
import PCP.Verifier.QueryList
import PCP.Verifier.FiniteProbability

/-!
# The algebraic verifier in the oracle decision-tree model

One verifier handles all graph bitstrings. Its random-bit budget is exactly a
fixed affine function of the ceiling logarithm of input length. Query-list
compilation preserves the actual algebraic verdict, and unused bits preserve
its normalized rejection probability. Every reachable proof address is bounded
by one fixed polynomial in encoded input length.

This is a semantic verifier with proved resource and probability properties.
It does not assert a polynomial-time implementation or an NP-hardness reduction.
-/

namespace PCP.Algebraic.ThreeColorCanonicalVerifier

open BinarySeedPadding

/-- Number of vertices of the actual decoded input graph. -/
abbrev graphOrder (x : List Bool) : ℕ := Fintype.card (Fin (ThreeColorEncoding.vertexCount x))

@[simp] theorem graphOrder_eq (x : List Bool) : graphOrder x = ThreeColorEncoding.vertexCount x :=
  Fintype.card_fin _

/-- Decoded vertices already carry their actual numeric addresses; only the bound is cast. -/
def vertexCode (x : List Bool) : Fin (ThreeColorEncoding.vertexCount x) ≃ Fin (graphOrder x) :=
  finCongr (graphOrder_eq x).symm

@[simp] theorem vertexCode_val (x : List Bool) (v : Fin (ThreeColorEncoding.vertexCount x)) :
    (vertexCode x v).val = v.val := rfl

theorem graphOrder_le_length (x : List Bool) : graphOrder x ≤ x.length := by
  rw [graphOrder_eq]
  exact ThreeColorEncoding.size_le_length x

/-- The randomness budget is a closed formula in encoded input length. -/
def randomBudget (n : ℕ) : ℕ := 32000000 * Nat.clog 2 (n + 2) + 32000000

theorem randomBits_le_budget (x : List Bool) :
    ThreeColorBinaryVerifier.randomBits (graphOrder x) ≤ randomBudget x.length := by
  have hr := ThreeColorBinaryVerifier.randomBits_le (graphOrder x)
  have hl := Nat.clog_mono_right 2 ((graphOrder_le_length x).trans (Nat.le_add_right _ 2))
  dsimp [randomBudget]
  omega

/-- Ignore precisely the excess bits of the canonical random string. -/
def sample (x : List Bool) (r : Fin (2 ^ randomBudget x.length)) :
    ThreeColorBinaryVerifier.Seed (graphOrder x) :=
  BinarySeedPadding.prefix (randomBits_le_budget x) (finSeedEquiv _ r)

/-- Convert a finite Boolean word to the binary-field alphabet used by the algebraic test. -/
def fieldWord {N : ℕ} (w : Fin (ThreeColorBinaryVerifier.proofLength N) → Bool) :
    ThreeColorBinaryVerifier.ProofWord N := fun i => boolEquiv (w i)

/-- Restrict the ordinary proof oracle to the actual finite algebraic word. -/
def proofWord (x : List Bool) (π : ProofOracle) :
    ThreeColorBinaryVerifier.ProofWord (graphOrder x) :=
  fieldWord (QueryTree.wordOfOracle _ π)

/-- Extend an honest finite algebraic word by false outside its actual address space. -/
def proofOracle (x : List Bool)
    (w : ThreeColorBinaryVerifier.ProofWord (graphOrder x)) : ProofOracle :=
  fun i => if h : i < ThreeColorBinaryVerifier.proofLength (graphOrder x) then
    boolEquiv.symm (w ⟨i, h⟩) else false

@[simp] theorem proofWord_proofOracle (x : List Bool)
    (w : ThreeColorBinaryVerifier.ProofWord (graphOrder x)) :
    proofWord x (proofOracle x w) = w := by
  funext i
  simp only [proofWord, fieldWord, QueryTree.wordOfOracle, proofOracle, dite_eq_left i.isLt,
    Equiv.apply_symm_apply]

/-- The actual input-and-seed decision tree, with its original 187-bit query budget. -/
noncomputable def tree (x : List Bool) (r : Fin (2 ^ randomBudget x.length)) : QueryTree 187 :=
  QueryTree.compileWordBounded
    (ThreeColorBinaryVerifier.queries (ThreeColorEncoding.graph x) (sample x r) (vertexCode x))
    (fun w => ThreeColorBinaryVerifier.test (ThreeColorEncoding.graph x)
      (fieldWord w) (sample x r) (vertexCode x))
    (ThreeColorBinaryVerifier.queries_length_le _ _ (vertexCode x))

theorem tree_eval (x : List Bool) (r : Fin (2 ^ randomBudget x.length)) (π : ProofOracle) :
    (tree x r).eval π =
      ThreeColorBinaryVerifier.test (ThreeColorEncoding.graph x)
        (proofWord x π) (sample x r) (vertexCode x) := by
  apply QueryTree.eval_compileWordBounded
  intro w w' hw
  apply ThreeColorBinaryVerifier.test_congr (eV := vertexCode x)
  intro i hi
  exact congrArg boolEquiv (hw i hi)

theorem tree_addresses_lt (x : List Bool) (r : Fin (2 ^ randomBudget x.length)) :
    ∀ i ∈ (tree x r).addresses, i < ThreeColorBinaryVerifier.proofLength (graphOrder x) :=
  QueryTree.addresses_compileWordBounded_lt _ _ _

/-- A single oracle verifier for every encoded graph. -/
noncomputable def verifier : Verifier where
  randomness := randomBudget
  queries := 187
  run := tree

@[simp] theorem verifier_queries : verifier.queries = 187 := rfl

/-- The budget satisfies the model's exact canonical-randomness requirement. -/
theorem canonicalRandomness : verifier.CanonicalRandomness 32000000 32000000 := fun _ => rfl

/-- One fixed polynomial bounds all reachable proof addresses in input length. -/
noncomputable def proofBound : Polynomial ℕ := (Polynomial.C 4 * (Polynomial.X + 1)) ^ 4224000

private theorem power_bound_mono {N n : ℕ} (hn : N ≤ n) (k : ℕ) :
    (4 * max 1 N) ^ k ≤
      ((Polynomial.C 4 * (Polynomial.X + 1) : Polynomial ℕ) ^ k).eval n := by
  rw [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  exact Nat.pow_le_pow_left (by omega) k

theorem proofLength_le_bound (x : List Bool) :
    ThreeColorBinaryVerifier.proofLength (graphOrder x) ≤ proofBound.eval x.length := by
  apply (ThreeColorBinaryVerifier.proofLength_le (graphOrder x)).trans
  exact power_bound_mono (N := graphOrder x) (n := x.length)
    (graphOrder_le_length x) 4224000

theorem readsBelow (x : List Bool) : verifier.ReadsBelow x (proofBound.eval x.length) := by
  intro r i hi
  exact (tree_addresses_lt x r i hi).trans_le (proofLength_le_bound x)

/-- The decision-tree and padding adapters preserve the exact rejection probability. -/
theorem rejectionProb_eq (x : List Bool) (π : ProofOracle) :
    verifier.rejectionProb x π =
      ThreeColorBinaryVerifier.rejectionRate (ThreeColorEncoding.graph x)
        (proofWord x π) (vertexCode x) := by
  unfold Verifier.rejectionProb
  simp only [verifier, tree_eval]
  exact relativeDistance_finSeed_prefix (randomBits_le_budget x)
    (fun s => ThreeColorBinaryVerifier.test (ThreeColorEncoding.graph x)
      (proofWord x π) s (vertexCode x)) (fun _ => true)

/-- Perfect completeness in the original oracle-verifier model. -/
theorem completeAt (x : List Bool) (hx : (ThreeColorEncoding.graph x).Colorable 3) :
    verifier.CompleteAt x := by
  obtain ⟨w, hw⟩ := ThreeColorBinaryVerifier.exists_proof_test_eq_true _ hx (vertexCode x)
  refine ⟨proofOracle x w, (Verifier.accProb_eq_one_iff _ _ _).mpr ?_⟩
  intro r
  change Fin (2 ^ randomBudget x.length) at r
  change (tree x r).eval _ = true
  rw [tree_eval, proofWord_proofOracle]
  exact hw _

/-- Every ordinary proof oracle for a noncolorable decoded graph has constant soundness. -/
theorem soundAt (x : List Bool) (hx : ¬ (ThreeColorEncoding.graph x).Colorable 3) :
    verifier.SoundAt x (1 - ThreeColorBinaryVerifier.gap) := by
  apply Verifier.soundAt_of_rejectionProb_ge
  intro π
  rw [rejectionProb_eq]
  exact ThreeColorBinaryVerifier.rejectionRate_ge_of_not_colorable _ hx _ (vertexCode x)

/-- Mathematical guarantees for one verifier on all encoded inputs.
No efficient implementation or NP-completeness result is asserted here. -/
theorem verification_guarantees :
    verifier.queries = 187 ∧ verifier.CanonicalRandomness 32000000 32000000 ∧
      (∀ x, verifier.ReadsBelow x (proofBound.eval x.length)) ∧
      (∀ x, (ThreeColorEncoding.graph x).Colorable 3 → verifier.CompleteAt x) ∧
      (∀ x, ¬ (ThreeColorEncoding.graph x).Colorable 3 →
        verifier.SoundAt x (1 - ThreeColorBinaryVerifier.gap)) :=
  ⟨verifier_queries, canonicalRandomness, readsBelow, completeAt, soundAt⟩

end PCP.Algebraic.ThreeColorCanonicalVerifier
