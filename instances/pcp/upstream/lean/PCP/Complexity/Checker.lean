import PCP.Complexity.CostModel

/-!
# The finite witness checker, semantically

The closure field of NP-1 is `polyTimeRel_finiteWitnessCheck`, and it is **quantitative**: it
needs an actual `TM2ComputableInPolyTime` certificate for `finiteWitnessCheck V`, which
`CheckerFinal.lean` supplies. This module does the part that comes first — saying exactly *what*
a machine would have to execute, and counting the calls and reads it makes — with no cost claim
of its own.

## One path per random seed

`QueryTree.ofStep` builds the whole tree, both branches at every query. A machine does not: given a
witness it follows only the branch the witness selects. `runAdaptive` is that direct evaluator, and
`runAdaptive_eq_eval` says the two agree.

## The two counts are different, and the difference is `+1`

At depth `0` the recurrence **still calls the algorithm** — it has to, because the algorithm may
halt there with a decision. So a `q`-query verifier makes at most `q` oracle reads but up to
**`q + 1`** algorithm calls. `readCount_le` and `callCount_le` prove both, and the fixtures show
both are attained.

## The discarded address

At depth `0` a query `.inr addr` is *discarded*: `ofStep` produces `leaf false`, and `addr` never
enters the tree's address set. So `ReadsBelow` does **not** bound it, and the planned implementation
must reject on the query tag alone — without indexing the witness at `addr` or even expanding the
numeral.

`runAdaptive_zero_of_inr` and `runAdaptive_zero_oracle_irrelevant` record only that the depth-zero
**result** is oracle-independent. That is a statement about values, not about executions: a function
returning a pair `(false, [(addr, π addr)])` has an oracle-independent first component and still
performs a lookup, so even a `rfl` proof certifies no absence of work. That no query-lookup
subroutine is *invoked* is an obligation of the eventual machine's execution and cost proof, and is
not claimed here.

## Scope

Everything below is a semantic equality or a counting bound in Lean's ambient logic. None of it is a
polynomial-time claim, and completing this module does not discharge any part of the closure field.

`readCount` and `callCount` are separate recursive functions, not observations read off a proved
machine execution. Their bounds become usable in a time proof only once an implementation is
connected to them — either through an instrumented evaluator with projection theorems identifying
all three functions, or directly in the machine simulation. Defining an "instrumented" evaluator as
the tuple of these three functions would prove nothing operational.

The oracle reads counted here are *logical* lookups. They are not the only tape work a checker does:
scanning or draining witness storage during setup and cleanup is separate, and is charged
separately.
-/

namespace PCP

open Verifier

/-! ## The direct adaptive evaluator -/

/-- Run the step function `f` against the oracle `π`, following only the answers actually received:
one path, not a tree. -/
def runAdaptive (f : List Bool → Bool ⊕ ℕ) (π : ProofOracle) : ℕ → List Bool → Bool
  | 0, as => match f as with
      | .inl b => b
      | .inr _ => false
  | d + 1, as => match f as with
      | .inl b => b
      | .inr addr => runAdaptive f π d (as ++ [π addr])

/-- Oracle reads along the path actually taken. -/
def readCount (f : List Bool → Bool ⊕ ℕ) (π : ProofOracle) : ℕ → List Bool → ℕ
  | 0, _ => 0
  | d + 1, as => match f as with
      | .inl _ => 0
      | .inr addr => readCount f π d (as ++ [π addr]) + 1

/-- Algorithm calls along the path actually taken.  Note the depth-`0` case is `1`, not `0`. -/
def callCount (f : List Bool → Bool ⊕ ℕ) (π : ProofOracle) : ℕ → List Bool → ℕ
  | 0, _ => 1
  | d + 1, as => match f as with
      | .inl _ => 1
      | .inr addr => callCount f π d (as ++ [π addr]) + 1

/-! ### The depth-zero behaviour, stated on its own

The implementation must reject a discarded address on its tag, without indexing the witness there or
expanding the numeral.  These two lemmas do **not** say that: they constrain the returned *value*,
and an execution property is not a value property.  Establishing that no lookup subroutine runs is
owed by the machine's execution and cost proof. -/

@[simp] theorem runAdaptive_zero_of_inl {f : List Bool → Bool ⊕ ℕ} {π : ProofOracle}
    {as : List Bool} {b : Bool} (h : f as = .inl b) : runAdaptive f π 0 as = b := by
  rw [runAdaptive, h]

theorem runAdaptive_zero_of_inr {f : List Bool → Bool ⊕ ℕ} {π : ProofOracle} {as : List Bool}
    {addr : ℕ} (h : f as = .inr addr) : runAdaptive f π 0 as = false := by
  rw [runAdaptive, h]

/-- The depth-zero **result** does not depend on the oracle.

This constrains the value, not the execution: it does not say that no read is performed, and no
`rfl` proof could.  The implementation is intended to reject on the query tag, and establishing that
no query-lookup subroutine runs belongs to its execution proof. -/
theorem runAdaptive_zero_oracle_irrelevant (f : List Bool → Bool ⊕ ℕ) (π π' : ProofOracle)
    (as : List Bool) : runAdaptive f π 0 as = runAdaptive f π' 0 as := rfl

/-! ### Agreement with the tree semantics -/

/-- **One path is enough.**  For arbitrary remaining depth, answer history, and oracle. -/
theorem runAdaptive_eq_eval (f : List Bool → Bool ⊕ ℕ) (π : ProofOracle) :
    ∀ (d : ℕ) (as : List Bool), runAdaptive f π d as = (QueryTree.ofStep f d as).eval π
  | 0, as => by
      rw [runAdaptive, QueryTree.ofStep]
      cases f as <;> rfl
  | d + 1, as => by
      rw [runAdaptive, QueryTree.ofStep]
      cases h : f as with
      | inl b => rfl
      | inr addr =>
          change runAdaptive f π d (as ++ [π addr]) = QueryTree.eval _ π
          rw [QueryTree.eval]
          cases hπ : π addr
          · simpa [hπ] using runAdaptive_eq_eval f π d (as ++ [false])
          · simpa [hπ] using runAdaptive_eq_eval f π d (as ++ [true])

/-! ### The two counts -/

/-- At most `d` oracle reads. -/
theorem readCount_le (f : List Bool → Bool ⊕ ℕ) (π : ProofOracle) :
    ∀ (d : ℕ) (as : List Bool), readCount f π d as ≤ d
  | 0, _ => le_refl 0
  | d + 1, as => by
      rw [readCount]
      cases f as with
      | inl _ => exact Nat.zero_le _
      | inr addr => exact Nat.succ_le_succ (readCount_le f π d (as ++ [π addr]))

/-- At most `d + 1` algorithm calls — **one more** than the read bound, because the algorithm is
still called at depth zero. -/
theorem callCount_le (f : List Bool → Bool ⊕ ℕ) (π : ProofOracle) :
    ∀ (d : ℕ) (as : List Bool), callCount f π d as ≤ d + 1
  | 0, _ => le_refl 1
  | d + 1, as => by
      rw [callCount]
      cases f as with
      | inl _ => exact Nat.succ_le_succ (Nat.zero_le _)
      | inr addr => exact Nat.succ_le_succ (callCount_le f π d (as ++ [π addr]))

/-- An algorithm that never halts attains both bounds exactly: `d` reads and `d + 1` calls. -/
theorem readCount_alwaysQuery (addr : ℕ) (π : ProofOracle) :
    ∀ (d : ℕ) (as : List Bool), readCount (fun _ => .inr addr) π d as = d
  | 0, _ => rfl
  | d + 1, as => congrArg (· + 1) (readCount_alwaysQuery addr π d (as ++ [π addr]))

theorem callCount_alwaysQuery (addr : ℕ) (π : ProofOracle) :
    ∀ (d : ℕ) (as : List Bool), callCount (fun _ => .inr addr) π d as = d + 1
  | 0, _ => rfl
  | d + 1, as => congrArg (· + 1) (callCount_alwaysQuery addr π d (as ++ [π addr]))

/-! ## The checker as an explicit finite conjunction -/

/-- What a machine would execute: for each seed index below `2 ^ k`, build the seed's bit string,
run the algorithm adaptively against the witness, and conjoin. -/
def checkAll (alg : VerifierAlg) (q k : ℕ) (x w : List Bool) : Bool :=
  (List.finRange (2 ^ k)).all fun r =>
    runAdaptive (alg x (bitsOfFin k r)) (oracleOfWitness w) q []

theorem checkAll_eq_true_iff (alg : VerifierAlg) (q k : ℕ) (x w : List Bool) :
    checkAll alg q k x w = true ↔
      ∀ r : Fin (2 ^ k), runAdaptive (alg x (bitsOfFin k r)) (oracleOfWitness w) q [] = true := by
  rw [checkAll, List.all_eq_true]
  exact ⟨fun h r => h r (List.mem_finRange r), fun h r _ => h r⟩

/-- **The checker equation.**  For every input and *every* witness — no length restriction, since
the closure field does not assume one and a short witness is still a legitimate input, its missing
bits read as `false` through `oracleOfWitness`. -/
theorem checkAll_eq_finiteWitnessCheck {V : Verifier} {alg : VerifierAlg}
    (himp : V.ImplementedBy alg) (x w : List Bool) :
    checkAll alg V.queries (V.randomness x.length) x w = finiteWitnessCheck V x w := by
  rw [finiteWitnessCheck]
  refine Bool.eq_iff_iff.2 ?_
  rw [checkAll_eq_true_iff, decide_eq_true_iff]
  constructor <;> intro h r
  · rw [← himp x r, ← runAdaptive_eq_eval]; exact h r
  · rw [runAdaptive_eq_eval, himp x r]; exact h r

/-- With a canonical budget the seed width is a closed-form function of `x.length`, which is what a
machine can compute.  Stated as a `ℕ` equation so no dependent `Fin` transport is needed. -/
theorem randomness_eq_closedForm {V : Verifier} {a b : ℕ} (h : V.CanonicalRandomness a b)
    (n : ℕ) : V.randomness n = a * Nat.clog 2 (n + 2) + b := h n

/-! ## The seed count is polynomial

The logarithm must be kept **exact** until after exponentiation: replacing `⌈log₂ (n+2)⌉` by a
linear upper bound first would make the seed count exponential. -/

theorem two_pow_clog_le (m : ℕ) (hm : 2 ≤ m) : 2 ^ Nat.clog 2 m ≤ 2 * m := by
  have h1 : 1 < m := hm
  have hlt : 2 ^ (Nat.clog 2 m - 1) < m := Nat.pow_pred_clog_lt_self (by norm_num) h1
  have hpos : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by norm_num) hm
  calc 2 ^ Nat.clog 2 m = 2 ^ (Nat.clog 2 m - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hpos]
    _ ≤ m * 2 := Nat.mul_le_mul_right 2 hlt.le
    _ = 2 * m := Nat.mul_comm _ _

/-- **The seed-count bound.**  `a`, `b` are the verifier's fixed constants, so the right-hand side
is a fixed polynomial in `n`. -/
theorem two_pow_canonical_le (a b n : ℕ) :
    2 ^ (a * Nat.clog 2 (n + 2) + b) ≤ 2 ^ (a + b) * (n + 2) ^ a := by
  have hm : 2 ≤ n + 2 := Nat.le_add_left 2 n
  calc 2 ^ (a * Nat.clog 2 (n + 2) + b)
      = (2 ^ Nat.clog 2 (n + 2)) ^ a * 2 ^ b := by rw [pow_add, ← pow_mul, Nat.mul_comm a]
    _ ≤ (2 * (n + 2)) ^ a * 2 ^ b :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (two_pow_clog_le _ hm) a)
    _ = 2 ^ (a + b) * (n + 2) ^ a := by rw [Nat.mul_pow, pow_add]; ring

/-! ## Acceptance

Boundary cases: both zero-query outcomes, the discarded address, the `q + 1` call count, and the
zero-width seed space. -/

/-- A zero-query verifier that **accepts**. -/
example (x w : List Bool) (k : ℕ) : checkAll (fun _ _ _ => .inl true) 0 k x w = true := by
  rw [checkAll_eq_true_iff]; intro _; rfl

/-- …and one that **rejects**.  `q = 0` does not collapse the two. -/
example (x w : List Bool) (k : ℕ) : checkAll (fun _ _ _ => .inl false) 0 k x w = false := by
  have h : ¬ (checkAll (fun _ _ _ => (.inl false : Bool ⊕ ℕ)) 0 k x w = true) := by
    rw [checkAll_eq_true_iff]
    intro h
    exact absurd (h ⟨0, Nat.two_pow_pos k⟩) (by simp [runAdaptive])
  simpa using h

/-- A zero-depth **query** rejects on the tag… -/
example (w : List Bool) (addr : ℕ) :
    runAdaptive (fun _ => .inr addr) (oracleOfWitness w) 0 [] = false := rfl

/-- …and gives the same answer for every witness, including one long enough to contain `addr`.
`ReadsBelow` does not bound a discarded address, so an implementation must not index it. -/
example (w w' : List Bool) (addr : ℕ) :
    runAdaptive (fun _ => .inr addr) (oracleOfWitness w) 0 []
      = runAdaptive (fun _ => .inr addr) (oracleOfWitness w') 0 [] := rfl

/-- `q + 1` calls against `q` reads, at `q = 3`. -/
example (w : List Bool) : callCount (fun _ => .inr 0) (oracleOfWitness w) 3 [] = 4 :=
  callCount_alwaysQuery 0 _ 3 []

example (w : List Bool) : readCount (fun _ => .inr 0) (oracleOfWitness w) 3 [] = 3 :=
  readCount_alwaysQuery 0 _ 3 []

/-- **A zero-width seed space has one seed, not none**: `2 ^ 0 = 1`, and its bit string is empty. -/
example : (List.finRange (2 ^ 0)).length = 1 := rfl

example (r : Fin (2 ^ 0)) : bitsOfFin 0 r = [] := rfl

/-- So at `k = 0` the checker is exactly one run. -/
example (alg : VerifierAlg) (q : ℕ) (x w : List Bool) :
    checkAll alg q 0 x w = true ↔ runAdaptive (alg x []) (oracleOfWitness w) q [] = true := by
  rw [checkAll_eq_true_iff]
  exact ⟨fun h => h ⟨0, Nat.two_pow_pos 0⟩, fun h _ => h⟩

end PCP
