import PCP.Complexity.AdaptiveTurn

/-!
# Bounded depth, concretely, and the two terminal rounds

`AdaptiveTurn.lean` closes the loop for a *positive* query but promises nothing about the next
iteration: the depth may be zero, or the algorithm may decide.  This module supplies the two things
the path induction needs before it can be written — a depth representation whose zero test and
predecessor are provably related, and a certificate for each way a round can end without looping.

## Depth is a `Fin (q + 1)`

`dzero` and `ddec` are *unrelated* parameters of the turnaround, deliberately: the machine's step is
proved without assuming anything about them.  That is exactly why the laws below are real work.
`R := Fin (q + 1) × U` instantiates them as a bounded counter beside the caller's own finite data,
with a **saturating** predecessor, and the laws say what the induction will need: the test fires
exactly at zero, the predecessor loses exactly one unit when there is one to lose, and `U` never
moves.

`q` is fixed once. Shrinking the counter's type inside the induction would change the machine and
obstruct composition, so the induction generalises over the *value* `d`, not over the type.

## Both terminal rounds still call the algorithm

Depth zero is **not** an unconditional rejection taken before the call.  Both certificates below run
preparation and the actual algorithm call first, and only then read the answer tag — because a
decision answer at zero depth still has to be returned.  That is why a depth-`d` run makes up to
`d + 1` algorithm calls while making at most `d` lookups: `PCP.callCount_le` and `PCP.readCount_le`
are the semantic side of the same `+1`.

## What the terminal endpoints keep

Neither endpoint is a `haltList`, and they are deliberately different from each other.  A decision
leaves the destination empty; a rejected query leaves `ofBits (Nat.bits addr)` on it, untouched,
for a later cleanup route that must not visit `lookup`.  Both leave the spent tuple on the call
input.  Replacing the two by a common "storage empty" claim would be unsupported.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-! ## A concrete bounded depth -/

section Depth

variable (q : ℕ) (U : Type) [Fintype U]

/-- Remaining depth, bounded by the verifier's query budget `q`, beside the caller's own finite
data. -/
abbrev DepthPay : Type := Fin (q + 1) × U

/-- The zero test dispatch reads. -/
def depthZero : DepthPay q U → Bool := fun r => decide ((r.1 : ℕ) = 0)

/-- Saturating predecessor: zero stays zero, and `U` is untouched. -/
def depthPred : DepthPay q U → DepthPay q U :=
  fun r => (⟨(r.1 : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.1.isLt⟩, r.2)

variable {q U}

@[simp] theorem depthZero_eq_true_iff (i : Fin (q + 1)) (u : U) :
    depthZero q U (i, u) = true ↔ (i : ℕ) = 0 := by
  simp [depthZero]

/-- The test fires at zero… -/
theorem depthZero_zero (u : U) : depthZero q U (0, u) = true := by
  simp [depthZero]

/-- …and only there. -/
theorem depthZero_of_pos {i : Fin (q + 1)} (h : 0 < (i : ℕ)) (u : U) :
    depthZero q U (i, u) = false := by
  simp only [depthZero, decide_eq_false_iff_not]
  omega

@[simp] theorem depthPred_fst (i : Fin (q + 1)) (u : U) :
    ((depthPred q U (i, u)).1 : ℕ) = (i : ℕ) - 1 := rfl

/-- The caller's own data rides through the depth step. -/
@[simp] theorem depthPred_snd (i : Fin (q + 1)) (u : U) :
    (depthPred q U (i, u)).2 = u := rfl

/-- **The positive predecessor equation.**  One turnaround step spends exactly one unit of
budget. -/
theorem depthPred_succ {i : Fin (q + 1)} (h : 0 < (i : ℕ)) (u : U) :
    ((depthPred q U (i, u)).1 : ℕ) + 1 = (i : ℕ) := by
  simp only [depthPred_fst]
  omega

/-- Saturation, stated rather than hidden: at zero the predecessor does nothing.

This is a fact about the counter, **not** about control flow — on its own it would not stop
turnaround steps or history growth if control were placed at `lkDone` by hand.  What stops them is
the branch: from a valid loop entry a zero-depth query dispatches to `rejected`, so `lookup`, the
search and the turnaround are never entered.  See `aRejectEvals`, and `pathCert`'s base case. -/
theorem depthPred_zero (u : U) : depthPred q U (0, u) = ((0 : Fin (q + 1)), u) := by
  simp only [depthPred]
  ext <;> simp

/-- **The size-accounting invariant of a positive round.**  History length plus remaining depth is
constant, so every history along a path is bounded by its initial length plus `q` — without ever
measuring an address. -/
theorem depth_budget {i : Fin (q + 1)} (h : 0 < (i : ℕ)) (u : U) (a : List Bool) (b : Bool)
    {N : ℕ} (hinv : a.length + (i : ℕ) = N) :
    (a ++ [b]).length + ((depthPred q U (i, u)).1 : ℕ) = N := by
  simp only [List.length_append, List.length_cons, List.length_nil, depthPred_fst]
  omega

end Depth

/-! ## The two terminal rounds -/

section Terminal

variable {tm : FinTM2} {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {R : Type} [Fintype R] {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- **A decision round.**  Preparation, the actual algorithm call, and one dispatch step to the
active `decided` boundary — at **any** remaining depth, since a decision is returned whether or not
budget is left.

Starting from an empty destination, the canonical decision tape `[Sym.bit b]` is consumed whole, so
the destination is empty at the endpoint.  The spent tuple is still on the call input, the source
tapes and the witness storage are untouched, and the depth component of `r` is unchanged — nothing
here spends budget. -/
noncomputable def aDecideEvals
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × R)) (dzero : R → Bool) (ddec : R → R)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))
    (x rs a : List Bool) (b : Bool) (hans : f (x, rs, a) = .inl b)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (aTM hw.inputAlphabet hw.outputAlphabet p₀ dzero ddec rest).step
      (tuCfg hw.inputAlphabet hw.outputAlphabet p₀ dzero ddec rest
        (some (.inr CallLabel.prepA1)) v temp (flag, (res, r)) (fun _ => []) [] [] []
        (ofBits x) (ofBits rs) (ofBits a) wit pre g)
      (some (tuCfg hw.inputAlphabet hw.outputAlphabet p₀ dzero ddec rest
        (some (.inr CallLabel.decided)) hw.tm.initialState none (flag, (b, r)) (fun _ => [])
        (encodeTriple (x, rs, a)) [] [] (ofBits x) (ofBits rs) (ofBits a) wit pre g))
      (((2 * (x.length + rs.length + a.length) + 8)
          + (callPoly hw.tm hw.time).eval (encodeTriple (x, rs, a)).length) + 1) where
  steps := (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
      (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
      (flag, (res, r)) (lkFrame G Γg wit pre g)).steps + 1
  evals_in_steps := by
    simp only [aTM, qTM, tuCfg, qCfg, ← tripleTapes_eq]
    have hc : (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
          (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
          (flag, (res, r)) (lkFrame G Γg wit pre g)).steps + 1
        = 1 + (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
            (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
            (flag, (res, r)) (lkFrame G Γg wit pre g)).steps := Nat.add_comm _ _
    rw [hc, Function.iterate_add_apply, Function.iterate_one,
      (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
        (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
        (flag, (res, r)) (lkFrame G Γg wit pre g)).evals_in_steps, hans, List.append_nil]
    exact q_bind_of_step hw.inputAlphabet hw.outputAlphabet p₀ dzero
      (turnRoute hw.tm G Γg R ddec rest)
      (q_step_decided hw.inputAlphabet hw.outputAlphabet p₀ dzero
        (turnRoute hw.tm G Γg R ddec rest) hw.tm.initialState none flag res b r (fun _ => [])
        (tripleTapes x rs a) (encodeTriple (x, rs, a)) [] [] wit pre g)
  steps_le_m := by
    have := (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
      (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
      (flag, (res, r)) (lkFrame G Γg wit pre g)).steps_le_m
    omega

/-- **A depth-zero rejection round.**  Preparation, the actual algorithm call — *still made*, since
the answer might have been a decision — and one dispatch step to the active `rejected` boundary.

The query numeral is left exactly as the call produced it, `ofBits (Nat.bits addr)`, for a later
cleanup route; `lookup` is never entered, so the search does not run and the address is never
expanded.  The witness storage and the prefix stack are untouched, and the depth is unchanged: this
round spends no budget because there is none to spend. -/
noncomputable def aRejectEvals
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × R)) (dzero : R → Bool) (ddec : R → R)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))
    (x rs a : List Bool) (addr : ℕ) (hans : f (x, rs, a) = .inr addr)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (hd : dzero r = true)
    (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (aTM hw.inputAlphabet hw.outputAlphabet p₀ dzero ddec rest).step
      (tuCfg hw.inputAlphabet hw.outputAlphabet p₀ dzero ddec rest
        (some (.inr CallLabel.prepA1)) v temp (flag, (res, r)) (fun _ => []) [] [] []
        (ofBits x) (ofBits rs) (ofBits a) wit pre g)
      (some (tuCfg hw.inputAlphabet hw.outputAlphabet p₀ dzero ddec rest
        (some (.inr CallLabel.rejected)) hw.tm.initialState none (flag, (false, r)) (fun _ => [])
        (encodeTriple (x, rs, a)) (ofBits (Nat.bits addr)) [] (ofBits x) (ofBits rs) (ofBits a)
        wit pre g))
      (((2 * (x.length + rs.length + a.length) + 8)
          + (callPoly hw.tm hw.time).eval (encodeTriple (x, rs, a)).length) + 1) where
  steps := (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
      (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
      (flag, (res, r)) (lkFrame G Γg wit pre g)).steps + 1
  evals_in_steps := by
    simp only [aTM, qTM, tuCfg, qCfg, ← tripleTapes_eq]
    have hc : (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
          (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
          (flag, (res, r)) (lkFrame G Γg wit pre g)).steps + 1
        = 1 + (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
            (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
            (flag, (res, r)) (lkFrame G Γg wit pre g)).steps := Nat.add_comm _ _
    rw [hc, Function.iterate_add_apply, Function.iterate_one,
      (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
        (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
        (flag, (res, r)) (lkFrame G Γg wit pre g)).evals_in_steps, hans, List.append_nil]
    exact q_bind_of_step hw.inputAlphabet hw.outputAlphabet p₀ dzero
      (turnRoute hw.tm G Γg R ddec rest)
      (q_step_rejected hw.inputAlphabet hw.outputAlphabet p₀ dzero
        (turnRoute hw.tm G Γg R ddec rest) hw.tm.initialState none flag res r (fun _ => [])
        (tripleTapes x rs a) (encodeTriple (x, rs, a)) (ofBits (Nat.bits addr)) [] wit pre g hd)
  steps_le_m := by
    have := (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
      (queryRoute hw.tm G Γg R dzero (turnRoute hw.tm G Γg R ddec rest)) x rs a [] v temp
      (flag, (res, r)) (lkFrame G Γg wit pre g)).steps_le_m
    omega

/-- **The semantic side of a decision round**: at *any* depth, `runAdaptive` returns the decision
immediately. -/
theorem runAdaptive_decide (fstep : List Bool → Bool ⊕ ℕ) (π : ProofOracle) (d : ℕ)
    (a : List Bool) (b : Bool) (h : fstep a = .inl b) :
    runAdaptive fstep π d a = b := by
  cases d <;> rw [runAdaptive, h]

/-- **The semantic side of a depth-zero rejection**: a query at depth zero returns `false`, and the
address is discarded. -/
theorem runAdaptive_reject (fstep : List Bool → Bool ⊕ ℕ) (π : ProofOracle)
    (a : List Bool) (addr : ℕ) (h : fstep a = .inr addr) :
    runAdaptive fstep π 0 a = false := by
  rw [runAdaptive, h]

end Terminal

end PCP.Machine
