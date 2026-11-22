import PCP.Complexity.WitnessLoop
import PCP.Complexity.CallDispatch

/-!
# Dispatch, the handoff, and the search under one program

`CallDispatch.lean` reads the answer tag and selects one of three boundaries; `WitnessLoop.lean`
runs the search from `lkMain` to `lkDone`.  Nothing yet joined them: dispatch reaches `lookup`, the
search starts at `lkMain`.  This module writes that jump, charges it, and proves all three dispatch
branches on the **same** machine as the search.

## The payload

The search's payload `Bool × (Bool × R)` is kept: helper flag, result bit, unrelated caller data.
Remaining depth lives inside `R`, reached by the caller's own `dzero : R → Bool`.  The helper flag
is neither the depth nor the result — it is the counter's scratch, and `lkSetDec` leaves it alone
while writing the result and preserving `R` untouched.

## One program, two nestings

`dispatchRoute`, `handoffRoute` and `lookupRoute` route disjoint label sets, so they commute — but
*not* definitionally on a variable label.  `queryRoute_eq` proves the commutation by function
extensionality and cases on `CallLabel`, and every theorem below names the program it is about.
Coinciding configuration types are not evidence of program equality and are not used as such.

## Counting

```text
resume --1--> lookup --1--> lkMain --searchSteps w (Nat.bits addr)--> lkDone
```

Exactly `2 + searchSteps w (Nat.bits addr)` for a positive-depth query, with the handoff charged.

## What is *not* joined

`lkDone`, `decided` and `rejected` all remain active boundaries dispatching through the caller's
continuation.  Depth decrement, history extension and the cleanup of a rejected query's numeral tail
are later adaptive-loop work: this integration **preserves** the depth rather than charging for
operations it does not perform, and the rejected tail is left as data — its eventual drain must not
route through the search either.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (R : Type) [Fintype R]

/-- Record a decision in the **result** bit, preserving the helper flag and all of `R` — depth
included. -/
def lkSetDec : (Bool × (Bool × R)) → Bool → (Bool × (Bool × R)) := fun p b => (p.1, (b, p.2.2))

/-- Remaining depth is a component of `R`, inspected through the caller's own predicate. -/
def lkDepthZero (dzero : R → Bool) : (Bool × (Bool × R)) → Bool := fun p => dzero p.2.2

/-- **The handoff**: one counted jump from dispatch's `lookup` boundary into the search's loop
head, preserving every field. -/
def lkHandoffStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  goto (fun _ => .inr .lkMain)

/-- Route `lookup` to the handoff; everything else to the supplied continuation. -/
def handoffRoute (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))
  | .lookup => lkHandoffStmt tm G Γg R
  | l => rest l

/-- **The combined program**: dispatch outermost, then the handoff, then the whole search. -/
def queryRoute (dzero : R → Bool)
    (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  dispatchRoute tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) (lkSetDec R)
    (lkDepthZero R dzero) (handoffRoute tm G Γg R (lookupRoute tm G Γg R rest))

/-- **The two nestings agree.**  `dispatchRoute` owns `resume`, `handoffRoute` owns `lookup`, and
`lookupRoute` owns the search and counter labels; every other label falls through all three in
either order.  Proved by cases on the label — not inferred from the programs having the same
configuration type. -/
theorem queryRoute_eq (dzero : R → Bool)
    (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))) :
    queryRoute tm G Γg R dzero rest
      = lookupRoute tm G Γg R
          (dispatchRoute tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) (lkSetDec R)
            (lkDepthZero R dzero) (handoffRoute tm G Γg R rest)) := by
  funext l
  cases l <;> rfl

variable {tm G Γg R}

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × (Bool × R))
  (dzero : R → Bool)
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))

/-- The machine carrying dispatch, the handoff and the search. -/
abbrev qTM : FinTM2 :=
  callTM tm (TripleSlot ⊕ (LookupSlot ⊕ G)) (prepΓ (LookupSlot ⊕ G) (lkΓ G Γg))
    (Bool × (Bool × R)) eIn eOut p₀
    (prepCont tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))
      (queryRoute tm G Γg R dzero rest))

/-- A configuration of that machine. -/
def qCfg (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × R)) (S : ∀ k, List (tm.Γ k)) (inp dst scr : List Sym)
    (t : TripleSlot → List Sym) (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (qTM eIn eOut p₀ dzero rest).Cfg :=
  prepCfg eIn eOut p₀ (queryRoute tm G Γg R dzero rest) l v temp pay S inp dst scr t
    (lkFrame G Γg wit pre g)

/-- Any one-step equation on this machine, restated where `Function.iterate` can use it. -/
theorem q_bind_of_step {c c' : (qTM eIn eOut p₀ dzero rest).Cfg}
    (h : (qTM eIn eOut p₀ dzero rest).step c = some c') :
    (flip Bind.bind (qTM eIn eOut p₀ dzero rest).step) (some c) = some c' := h

/-! ### The three dispatch branches, on this machine

Each is the accepted theorem of `CallDispatch.lean` at `rest := handoffRoute _ (lookupRoute _ rest)`
— which is `queryRoute` by definition, so no transport is involved. -/

/-- A decision answer records its bit in the result component and reaches `decided`.  The helper
flag and all of `R` — depth included — survive. -/
theorem q_step_decided (v : tm.σ) (temp : Option Sym) (flag res b : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp tail scr : List Sym)
    (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (qTM eIn eOut p₀ dzero rest).step
        (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.resume)) v temp (flag, (res, r)) S inp
          (Sym.bit b :: tail) scr t wit pre g)
      = some (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.decided)) v none (flag, (b, r)) S
          inp tail scr t wit pre g) :=
  dispatch_step_decided eIn eOut p₀ (lkSetDec R) (lkDepthZero R dzero)
    (handoffRoute tm G Γg R (lookupRoute tm G Γg R rest)) v temp (flag, (res, r)) b S t inp tail
    scr (lkFrame G Γg wit pre g)

/-- **Depth-zero query rejection, on the combined machine.**  The tag alone decides it: `rejected`
with `false` recorded, for an **arbitrary** numeral tail, which is left exactly where it was.  The
witness, the prefix stack and scratch are untouched, and the handoff to `lkMain` is never taken —
so the search does not run, and the numeral is never expanded. -/
theorem q_step_rejected (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp tail scr : List Sym)
    (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) (h : dzero r = true) :
    (qTM eIn eOut p₀ dzero rest).step
        (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.resume)) v temp (flag, (res, r)) S inp
          (Sym.sep :: tail) scr t wit pre g)
      = some (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.rejected)) v none
          (flag, (false, r)) S inp tail scr t wit pre g) :=
  dispatch_step_rejected eIn eOut p₀ (lkSetDec R) (lkDepthZero R dzero)
    (handoffRoute tm G Γg R (lookupRoute tm G Γg R rest)) v temp (flag, (res, r)) S t inp tail
    scr (lkFrame G Γg wit pre g) h

/-- A query at positive depth reaches `lookup`, with the numeral still on the destination. -/
theorem q_step_lookup (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp tail scr : List Sym)
    (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) (h : dzero r = false) :
    (qTM eIn eOut p₀ dzero rest).step
        (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.resume)) v temp (flag, (res, r)) S inp
          (Sym.sep :: tail) scr t wit pre g)
      = some (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.lookup)) v none (flag, (res, r)) S
          inp tail scr t wit pre g) :=
  dispatch_step_lookup eIn eOut p₀ (lkSetDec R) (lkDepthZero R dzero)
    (handoffRoute tm G Γg R (lookupRoute tm G Γg R rest)) v temp (flag, (res, r)) S t inp tail
    scr (lkFrame G Γg wit pre g) h

/-- **The handoff**, as one counted step of the actual combined program: `lookup` to `lkMain`,
every field preserved. -/
theorem q_step_handoff (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp dst scr : List Sym)
    (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (qTM eIn eOut p₀ dzero rest).step
        (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.lookup)) v temp pay S inp dst scr t
          wit pre g)
      = some (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.lkMain)) v temp pay S inp dst scr
          t wit pre g) :=
  rfl

/-! ### The search, on this machine

Here the transport is real: `lk_search` is stated for `lookupRoute _ rest'`, and this machine's
program is `queryRoute`.  `queryRoute_eq` reconciles them. -/

/-- `lk_search`, transported to the combined program. -/
theorem q_search (w bs : List Bool) (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (qTM eIn eOut p₀ dzero rest).step)^[searchSteps w bs]
        (some (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.lkMain)) v temp (flag, (res, r))
          S inp (ofBits bs) [] t (ofBits w) [] g))
      = some (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.lkDone)) v none
          (false, (oracleOfWitness w (bitsValue bs), r)) S inp [] [] t (ofBits w) [] g) := by
  simp only [qCfg, qTM]
  rw [queryRoute_eq]
  exact lk_search eIn eOut p₀
    (dispatchRoute tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) (lkSetDec R)
      (lkDepthZero R dzero) (handoffRoute tm G Γg R rest))
    w bs v temp flag res r S t inp g

/-! ### The positive query, end to end -/

/-- **A positive-depth query, from `resume` to `lkDone`**, in exactly `2 + searchSteps w
(Nat.bits addr)` steps: the dispatch pop, the handoff jump, then the search.

The destination carries exactly `encodeAnswer (.inr addr)` — no suffix is allowed, because a binary
query numeral has no terminator and nothing here could find its boundary.  The result is
`oracleOfWitness w addr` on the nose, by `bitsValue_bits`; the witness comes back in its original
order; destination, prefix stack and scratch are all empty; and `r` — depth included — is preserved
rather than decremented, which is the adaptive loop's job. -/
theorem q_query (w : List Bool) (addr : ℕ) (v : tm.σ) (temp : Option Sym) (flag res : Bool)
    (r : R) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) (h : dzero r = false) :
    (flip Bind.bind (qTM eIn eOut p₀ dzero rest).step)^[2 + searchSteps w (Nat.bits addr)]
        (some (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.resume)) v temp (flag, (res, r))
          S inp (encodeAnswer (.inr addr)) [] t (ofBits w) [] g))
      = some (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.lkDone)) v none
          (false, (oracleOfWitness w addr, r)) S inp [] [] t (ofBits w) [] g) := by
  have hsplit : 2 + searchSteps w (Nat.bits addr) = searchSteps w (Nat.bits addr) + (1 + 1) := by
    omega
  rw [hsplit,
    Function.iterate_add_apply (flip Bind.bind (qTM eIn eOut p₀ dzero rest).step)
      (searchSteps w (Nat.bits addr)) (1 + 1),
    Function.iterate_add_apply (flip Bind.bind (qTM eIn eOut p₀ dzero rest).step) 1 1,
    Function.iterate_one,
    show encodeAnswer (.inr addr) = Sym.sep :: ofBits (Nat.bits addr) from rfl,
    q_bind_of_step eIn eOut p₀ dzero rest
      (q_step_lookup eIn eOut p₀ dzero rest v temp flag res r S t inp (ofBits (Nat.bits addr)) []
        (ofBits w) [] g h),
    q_bind_of_step eIn eOut p₀ dzero rest
      (q_step_handoff eIn eOut p₀ dzero rest v none (flag, (res, r)) S t inp
        (ofBits (Nat.bits addr)) [] (ofBits w) [] g),
    q_search eIn eOut p₀ dzero rest w (Nat.bits addr) v none flag res r S t inp g,
    bitsValue_bits]

/-- The query certificate, with its actual count written out. -/
def qQueryEvals (w : List Bool) (addr : ℕ) (v : tm.σ) (temp : Option Sym) (flag res : Bool)
    (r : R) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) (h : dzero r = false) :
    EvalsToInTime (qTM eIn eOut p₀ dzero rest).step
      (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.resume)) v temp (flag, (res, r)) S inp
        (encodeAnswer (.inr addr)) [] t (ofBits w) [] g)
      (some (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.lkDone)) v none
        (false, (oracleOfWitness w addr, r)) S inp [] [] t (ofBits w) [] g))
      (2 + searchSteps w (Nat.bits addr)) where
  steps := 2 + searchSteps w (Nat.bits addr)
  evals_in_steps := q_query eIn eOut p₀ dzero rest w addr v temp flag res r S t inp g h
  steps_le_m := le_refl _

@[simp] theorem qQueryEvals_steps (w : List Bool) (addr : ℕ) (v : tm.σ) (temp : Option Sym)
    (flag res : Bool) (r : R) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp : List Sym) (g : ∀ j : G, List (Γg j)) (h : dzero r = false) :
    (qQueryEvals eIn eOut p₀ dzero rest w addr v temp flag res r S t inp g h).steps
      = 2 + searchSteps w (Nat.bits addr) := rfl

/-- **The same certificate under its polynomial-shaped bound.**  The recorded count is still the
actual one — the bound is enlarged in `steps_le_m` alone, field by field, so nothing is buried
behind a cast.  It is a subroutine certificate between caller configurations, not a whole-machine
polynomial-time witness. -/
def qQueryEvalsBound (w : List Bool) (addr : ℕ) (v : tm.σ) (temp : Option Sym)
    (flag res : Bool) (r : R) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp : List Sym) (g : ∀ j : G, List (Γg j)) (h : dzero r = false) :
    EvalsToInTime (qTM eIn eOut p₀ dzero rest).step
      (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.resume)) v temp (flag, (res, r)) S inp
        (encodeAnswer (.inr addr)) [] t (ofBits w) [] g)
      (some (qCfg eIn eOut p₀ dzero rest (some (.inr CallLabel.lkDone)) v none
        (false, (oracleOfWitness w addr, r)) S inp [] [] t (ofBits w) [] g))
      (w.length * (4 * (Nat.bits addr).length + 10) + 3 * (Nat.bits addr).length + 10) where
  steps := 2 + searchSteps w (Nat.bits addr)
  evals_in_steps := q_query eIn eOut p₀ dzero rest w addr v temp flag res r S t inp g h
  steps_le_m := by have := lk_search_steps_le w (Nat.bits addr); omega

@[simp] theorem qQueryEvalsBound_steps (w : List Bool) (addr : ℕ) (v : tm.σ) (temp : Option Sym)
    (flag res : Bool) (r : R) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp : List Sym) (g : ∀ j : G, List (Γg j)) (h : dzero r = false) :
    (qQueryEvalsBound eIn eOut p₀ dzero rest w addr v temp flag res r S t inp g h).steps
      = 2 + searchSteps w (Nat.bits addr) := rfl

end Steps

/-! ## One complete query round trip

Preparation, the call to the actual algorithm witness, dispatch, the handoff and the search — all on
the same machine, with the same alphabet equivalences and the same continuation.

The destination starts **empty**, so the call leaves exactly `encodeAnswer (f (x, r, a))` on it and
the full-decoding precondition of `q_query` is met with nothing to spare.  No answer-correctness
assumption is bolted on: what the answer *is* comes from the witness's own output certificate, and
the only hypothesis here is that this particular answer is the query `addr`. -/

section Round

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type} {R : Type} [Fintype R]
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- **Prepare, call, dispatch, hand off, search.**

From the preparation label with three canonical bit tapes, every callee stack empty and an empty
destination, to the search's active completion boundary with the oracle bit recorded.  The recorded
count is preparation's, plus the call's, plus `2 + searchSteps w (Nat.bits addr)`; the bound keeps
the call polynomial apart from the search's exact cost. -/
noncomputable def qRoundEvals
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × R)) (dzero : R → Bool)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))
    (x rs a : List Bool) (addr : ℕ) (hans : f (x, rs, a) = .inr addr) (w : List Bool)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (g : ∀ j : G, List (Γg j))
    (hd : dzero r = false) :
    EvalsToInTime (qTM hw.inputAlphabet hw.outputAlphabet p₀ dzero rest).step
      (qCfg hw.inputAlphabet hw.outputAlphabet p₀ dzero rest (some (.inr CallLabel.prepA1)) v temp
        (flag, (res, r)) (fun _ => []) [] [] [] (tripleTapes x rs a) (ofBits w) [] g)
      (some (qCfg hw.inputAlphabet hw.outputAlphabet p₀ dzero rest (some (.inr CallLabel.lkDone))
        hw.tm.initialState none (false, (oracleOfWitness w addr, r)) (fun _ => [])
        (encodeTriple (x, rs, a)) [] [] (tripleTapes x rs a) (ofBits w) [] g))
      (((2 * (x.length + rs.length + a.length) + 8)
          + (callPoly hw.tm hw.time).eval (encodeTriple (x, rs, a)).length)
        + (2 + searchSteps w (Nat.bits addr))) where
  steps := (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
      (queryRoute hw.tm G Γg R dzero rest) x rs a [] v temp (flag, (res, r))
      (lkFrame G Γg (ofBits w) [] g)).steps
    + (2 + searchSteps w (Nat.bits addr))
  evals_in_steps := by
    simp only [qTM, qCfg]
    have hc : (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
          (queryRoute hw.tm G Γg R dzero rest) x rs a [] v temp (flag, (res, r))
          (lkFrame G Γg (ofBits w) [] g)).steps + (2 + searchSteps w (Nat.bits addr))
        = (2 + searchSteps w (Nat.bits addr))
          + (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
              (queryRoute hw.tm G Γg R dzero rest) x rs a [] v temp (flag, (res, r))
              (lkFrame G Γg (ofBits w) [] g)).steps := Nat.add_comm _ _
    rw [hc, Function.iterate_add_apply, (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg)
        (Bool × (Bool × R)) hw p₀ (queryRoute hw.tm G Γg R dzero rest) x rs a [] v temp
        (flag, (res, r)) (lkFrame G Γg (ofBits w) [] g)).evals_in_steps, hans, List.append_nil]
    exact q_query hw.inputAlphabet hw.outputAlphabet p₀ dzero rest w addr hw.tm.initialState none
      flag res r (fun _ => []) (tripleTapes x rs a) (encodeTriple (x, rs, a)) g hd
  steps_le_m := by
    have := (prepCallEvals (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) hw p₀
      (queryRoute hw.tm G Γg R dzero rest) x rs a [] v temp (flag, (res, r))
      (lkFrame G Γg (ofBits w) [] g)).steps_le_m
    omega

end Round

end

end PCP.Machine
