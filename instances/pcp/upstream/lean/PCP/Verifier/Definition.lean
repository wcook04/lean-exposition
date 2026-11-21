/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Oracle verifiers, bit queries, and acceptance probability

A verifier uses a depth-bounded adaptive decision tree over a Boolean proof oracle.
Randomness is an exact number of fair bits, and acceptance probability is the
corresponding rational fraction. Proof length is bounded through the addresses
reachable over all random strings and all answers.

`CanonicalRandomness` fixes the computable budget used by the concrete runtime
and reverse-inclusion proofs. `ImplementedBy` in `PCP.Complexity.CostModel` ties
these semantic query trees to a single verifier algorithm.
-/

namespace PCP

/-- A proof oracle is an infinite Boolean string; `π a` is the bit at address `a`. -/
abbrev ProofOracle : Type := ℕ → Bool

/-- A decision tree over a Boolean proof oracle, of depth at most `d`.

`leaf` may occur at any depth, so `QueryTree d` is "at most `d` queries", not "exactly `d`". -/
inductive QueryTree : ℕ → Type
  /-- Stop and accept (`true`) or reject (`false`). -/
  | leaf {d : ℕ} (accept : Bool) : QueryTree d
  /-- Query proof address `addr`, then continue in `onFalse` or `onTrue`. -/
  | query {d : ℕ} (addr : ℕ) (onFalse onTrue : QueryTree d) : QueryTree (d + 1)

namespace QueryTree

/-- Run the decision tree against a proof oracle. -/
def eval : {d : ℕ} → QueryTree d → ProofOracle → Bool
  | _, .leaf b, _ => b
  | _, .query a f t, π => if π a then (t.eval π) else (f.eval π)

/-- Every address the tree could query, along any branch. -/
def addresses : {d : ℕ} → QueryTree d → Finset ℕ
  | _, .leaf _ => ∅
  | _, .query a f t => insert a (f.addresses ∪ t.addresses)

/-- The tree reads at most `d` bits along any branch: its address set has at most `2 ^ d - 1`
elements, and along a single run at most `d` queries are made. -/
theorem card_addresses_lt_two_pow : ∀ {d : ℕ} (T : QueryTree d), T.addresses.card < 2 ^ d
  | _, .leaf _ => by simp [addresses]
  | d + 1, .query a f t => by
      have hf := card_addresses_lt_two_pow f
      have ht := card_addresses_lt_two_pow t
      have : (insert a (f.addresses ∪ t.addresses)).card
          ≤ 1 + (f.addresses.card + t.addresses.card) := by
        refine (Finset.card_insert_le _ _).trans ?_
        have := Finset.card_union_le f.addresses t.addresses
        omega
      simp only [addresses]
      have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      omega

/-- If the oracles agree on every address the tree can reach, the tree cannot tell them apart. -/
theorem eval_congr : ∀ {d : ℕ} (T : QueryTree d) {π π' : ProofOracle},
    (∀ a ∈ T.addresses, π a = π' a) → T.eval π = T.eval π'
  | _, .leaf _, _, _, _ => rfl
  | _, .query a f t, π, π', h => by
      have ha : π a = π' a := h a (by simp [addresses])
      have hf : f.eval π = f.eval π' :=
        eval_congr f fun b hb => h b (by simp [addresses]; tauto)
      have ht : t.eval π = t.eval π' :=
        eval_congr t fun b hb => h b (by simp [addresses]; tauto)
      simp only [eval, ha, hf, ht]

end QueryTree

/-- An oracle verifier.

On an input `x` of length `n` it draws `randomness n` fair bits and then runs the decision tree
selected by that random string, making at most `queries` *bit* queries into the proof. -/
structure Verifier where
  /-- Fair random bits used on inputs of length `n`. -/
  randomness : ℕ → ℕ
  /-- Bound on the number of proof **bits** read (bits, not larger proof symbols). -/
  queries : ℕ
  /-- The decision tree used on input `x` and random string `r`. -/
  run : (x : List Bool) → Fin (2 ^ randomness x.length) → QueryTree queries

namespace Verifier

variable (V : Verifier) (x : List Bool) (π : ProofOracle)

/-- The random strings on which `V` accepts `x` given proof `π`. -/
def acceptingRandomness : Finset (Fin (2 ^ V.randomness x.length)) :=
  Finset.univ.filter (fun r => (V.run x r).eval π = true)

/-- Acceptance probability, as an exact rational: the fraction of the `2 ^ randomness` equally
likely random strings on which `V` accepts. -/
def accProb : ℚ :=
  ((V.acceptingRandomness x π).card : ℚ) / ((2 : ℚ) ^ V.randomness x.length)

theorem accProb_nonneg : 0 ≤ V.accProb x π :=
  div_nonneg (by positivity) (by positivity)

theorem accProb_le_one : V.accProb x π ≤ 1 := by
  rw [accProb, div_le_one (by positivity)]
  calc ((V.acceptingRandomness x π).card : ℚ)
      ≤ (Fintype.card (Fin (2 ^ V.randomness x.length)) : ℚ) := by
        exact_mod_cast Finset.card_le_univ _
    _ = (2 : ℚ) ^ V.randomness x.length := by simp

/-- `V` reads only proof addresses below `N` on input `x`, whatever the randomness and whatever
the oracle answers.  This is how "a proof of polynomial length" is expressed. -/
def ReadsBelow (N : ℕ) : Prop :=
  ∀ r, ∀ a ∈ (V.run x r).addresses, a < N

/-- Only the first `N` proof bits matter when `V.ReadsBelow x N`. -/
theorem accProb_congr_of_readsBelow {N : ℕ} (h : V.ReadsBelow x N) {π π' : ProofOracle}
    (hππ' : ∀ a < N, π a = π' a) : V.accProb x π = V.accProb x π' := by
  have : V.acceptingRandomness x π = V.acceptingRandomness x π' := by
    ext r
    simp only [acceptingRandomness, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [QueryTree.eval_congr _ fun a ha => hππ' a (h r a ha)]
  rw [accProb, accProb, this]

/-- Perfect completeness at `x`: some proof is accepted with probability 1. -/
def CompleteAt : Prop := ∃ π : ProofOracle, V.accProb x π = 1

/-- Soundness at `x` with error `s`: every proof is accepted with probability at most `s`. -/
def SoundAt (s : ℚ) : Prop := ∀ π : ProofOracle, V.accProb x π ≤ s

/-- Logarithmic randomness as an upper bound: at most `a * ⌈log₂ (n + 2)⌉ + b` fair bits on
inputs of length `n`.

**This is too weak to be an efficiency hypothesis on its own.**  An upper bound does not make
`randomness` computable, and `Verifier.randomness` is an unrestricted function `ℕ → ℕ`.  Take
`randomness n = if f n then 1 else 0` for arbitrary `f`: the
bound `LogRandomness 0 1` holds, yet the budget smuggles in an arbitrary Boolean function of the
input length, which an algorithm recovers just by measuring the length of the random string it is
handed.  Use `CanonicalRandomness` wherever efficiency is at stake. -/
def LogRandomness (a b : ℕ) : Prop :=
  ∀ n : ℕ, V.randomness n ≤ a * Nat.clog 2 (n + 2) + b

/-- The randomness budget is **exactly** `a * ⌈log₂ (n + 2)⌉ + b`.

Two constants determine the whole budget, so it is computable by construction and carries no
information of its own.  This is the "canonical computable budget" repair: it closes the hole that
`LogRandomness` leaves open, and it is without loss of generality because a verifier that wants
fewer bits can ignore the surplus. -/
def CanonicalRandomness (a b : ℕ) : Prop :=
  ∀ n : ℕ, V.randomness n = a * Nat.clog 2 (n + 2) + b

theorem CanonicalRandomness.logRandomness {a b : ℕ} (h : V.CanonicalRandomness a b) :
    V.LogRandomness a b := fun n => (h n).le

/-- A canonical budget *is* the closed-form function of the two constants.

Named for what it says. It is an equality of functions, not a proposition of type
`Computable V.randomness`. None is needed downstream: the closed form is evidently computable, and
the verifier's efficiency is certified separately through `Verifier.ImplementedBy` and the machine
predicates of `PCP/Complexity/Machine.lean`. -/
theorem CanonicalRandomness.eq_closedForm {a b : ℕ} (h : V.CanonicalRandomness a b) :
    V.randomness = fun n => a * Nat.clog 2 (n + 2) + b := funext h

/-- Acceptance probability is exactly `1` precisely when *every* random string accepts.  This is
the bridge between the probabilistic statement of perfect completeness and the finite, decidable
condition used by the NP witness checker below. -/
theorem accProb_eq_one_iff :
    V.accProb x π = 1 ↔ ∀ r, (V.run x r).eval π = true := by
  have hpos : ((2 : ℚ) ^ V.randomness x.length) ≠ 0 := by positivity
  rw [accProb, div_eq_iff hpos, one_mul]
  have hcard : ((2 : ℚ) ^ V.randomness x.length)
      = ((Finset.univ : Finset (Fin (2 ^ V.randomness x.length))).card : ℚ) := by simp
  rw [hcard, Nat.cast_inj]
  constructor
  · intro h r
    have huniv : V.acceptingRandomness x π = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using h)
    have hr : r ∈ V.acceptingRandomness x π := huniv ▸ Finset.mem_univ r
    simpa [acceptingRandomness] using hr
  · intro h
    have huniv : V.acceptingRandomness x π = Finset.univ :=
      Finset.eq_univ_of_forall fun r => by simp [acceptingRandomness, h r]
    rw [huniv]

end Verifier

/-! ## From a verifier to an NP witness checker

These are the pieces the reverse inclusion needs.  A proof of polynomial length is a finite bit
string; reading it as an oracle and asking whether *every* random string accepts is a decidable
condition, so it is an honest candidate NP checking relation. -/

/-- The proof oracle determined by a finite witness: address `j` holds `w[j]`, and `false` at every
address beyond `w`.  Padding with `false` is harmless exactly because a verifier satisfying
`Verifier.ReadsBelow x N` never looks past address `N`. -/
def oracleOfWitness (w : List Bool) : ProofOracle := fun j => w.getD j false

/-- The NP checking relation induced by a verifier: accept `(x, w)` when the finite witness `w`,
read as a proof, makes `V` accept on *every* random string.

This is decidable because the random space `Fin (2 ^ randomness)` is finite, which is the whole
point: perfect completeness turns into a finite check.  Whether it is *polynomial-time* decidable
is a separate question, answered by `CostModel.polyTimeRel_finiteWitnessCheck`. -/
def finiteWitnessCheck (V : Verifier) : List Bool → List Bool → Bool :=
  fun x w => decide (∀ r, (V.run x r).eval (oracleOfWitness w) = true)

theorem finiteWitnessCheck_eq_true_iff (V : Verifier) (x w : List Bool) :
    finiteWitnessCheck V x w = true ↔ ∀ r, (V.run x r).eval (oracleOfWitness w) = true := by
  simp [finiteWitnessCheck]

/-- Reading the first `N` bits of an oracle back out reproduces it below `N`. -/
theorem oracleOfWitness_prefix (π : ProofOracle) (N : ℕ) {j : ℕ} (hj : j < N) :
    oracleOfWitness ((List.range N).map π) j = π j := by
  simp [oracleOfWitness, List.getD_eq_getElem?_getD, hj]

theorem length_witness_of_oracle (π : ProofOracle) (N : ℕ) :
    ((List.range N).map π).length = N := by simp
end PCP
