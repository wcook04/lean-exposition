import PCP.Complexity.LookupDispatch
import PCP.Complexity.Checker

/-!
# The adaptive turnaround: one complete iteration of the checker's loop

`LookupDispatch.lean` ends a positive query at an active `lkDone` with the oracle bit in the result
component.  This module supplies `lkDone`'s continuation: it records that bit in the answer history,
clears the spent tuple, decrements the depth and returns to `prepA1` — closing the loop, so one
whole adaptive iteration runs on one machine.

## The history grows at the *far* end

`runAdaptive` appends: `as ++ [π addr]`.  A stack pushes at the near end, so recording an answer is
**not** one step.  The turnaround scans the history onto the call scratch, pushes the new bit onto
the emptied tape, and scans back — two passes, `2 * a.length + 2` steps plus the push.  Reversing
the stored order instead would only move the reversal into preparation, whose block copy is
order-preserving by construction.

## The spent tuple

The call leaves `encodeTriple (x, r, a)` on the call input, and preparation's precondition wants it
empty.  `tuClear` drains it and charges its length.  Nothing reuses those symbols: the next
iteration re-assembles the tuple from the three preserved source tapes, which is why they are
preserved.

## Depth

Remaining depth lives in `R` and moves only through the caller's own `ddec : R → R` — one counted
step of finite control, on a finite type.  `dzero` and `ddec` are unrelated parameters here: this
module proves the *machine* takes the step, not that the caller's depth encoding is well-founded.

## Counting

```text
lkDone --1--> tuScan --a+1--> tuPush --1--> tuBack --a+1--> tuClear
       --|inp|+1--> tuDepth --1--> prepA1
```

`turnSteps a inp = 2 * a.length + inp.length + 6`.  The six constant steps are three standalone
ones — the entry jump, the answer push and the depth step — and the three empty exits already
counted inside the three scans.  With `inp = encodeTriple (x, r, a)` the total is
`x.length + r.length + 3 * a.length + 8`.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-- The three source tapes, named individually — the turnaround rewrites one of them, so the
endpoint has to be able to say which. -/
def tripleOf (xt rt at' : List Sym) : TripleSlot → List Sym
  | .xs => xt
  | .rs => rt
  | .as => at'

theorem tripleTapes_eq (x r a : List Bool) :
    tripleTapes x r a = tripleOf (ofBits x) (ofBits r) (ofBits a) := by
  funext s; cases s <;> rfl

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (R : Type) [Fintype R]

/-- `lkDone`'s continuation: one counted jump into the turnaround. -/
def tuEnterStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  goto (fun _ => .inr .tuScan)

/-- Pass one: drain the answer history onto the call scratch. -/
def tuScanStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inr (.inl TripleSlot.as))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inl CallSlot.scratch)) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .tuScan))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .tuPush)))

/-- The new answer, onto the emptied history tape — so the scan back puts it at the far end. -/
def tuPushStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  push (.inr (.inr (.inl TripleSlot.as))) (fun p => Sym.bit p.2.2.2.1)
    (goto (fun _ => .inr .tuBack))

/-- Pass two: scan the history back, restoring its order above the new answer. -/
def tuBackStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.scratch)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inr (.inl TripleSlot.as))) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .tuBack))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .tuClear)))

/-- Drain the spent tuple off the call input. -/
def tuClearStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.input)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .tuClear)))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .tuDepth)))

/-- One counted step of finite control: decrement the depth, and begin the next iteration. -/
def tuDepthStmt (ddec : R → R) : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  load (fun p => (p.1, (none, (p.2.2.1, (p.2.2.2.1, ddec p.2.2.2.2)))))
    (goto (fun _ => .inr .prepA1))

/-- The turnaround's labels, and `lkDone`'s continuation. -/
def turnRoute (ddec : R → R)
    (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))
  | .lkDone => tuEnterStmt tm G Γg R
  | .tuScan => tuScanStmt tm G Γg R
  | .tuPush => tuPushStmt tm G Γg R
  | .tuBack => tuBackStmt tm G Γg R
  | .tuClear => tuClearStmt tm G Γg R
  | .tuDepth => tuDepthStmt tm G Γg R ddec
  | l => rest l

variable {tm G Γg R}

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × (Bool × R))
  (dzero : R → Bool) (ddec : R → R)
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))

/-- The whole loop on one machine: preparation, the call, dispatch, the handoff, the search and the
turnaround.  Every earlier theorem applies here **unchanged**, at `rest := turnRoute _ ddec rest` —
the turnaround's labels are disjoint from all of theirs, so no transport is involved. -/
abbrev aTM : FinTM2 := qTM eIn eOut p₀ dzero (turnRoute tm G Γg R ddec rest)

/-- A configuration with the three source tapes named separately. -/
def tuCfg (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × R)) (S : ∀ k, List (tm.Γ k)) (inp dst scr : List Sym)
    (xt rt at' : List Sym) (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (aTM eIn eOut p₀ dzero ddec rest).Cfg :=
  qCfg eIn eOut p₀ dzero (turnRoute tm G Γg R ddec rest) l v temp pay S inp dst scr
    (tripleOf xt rt at') wit pre g

/-- Any one-step equation on this machine, where `Function.iterate` can use it. -/
theorem tu_bind_of_step {c c' : (aTM eIn eOut p₀ dzero ddec rest).Cfg}
    (h : (aTM eIn eOut p₀ dzero ddec rest).step c = some c') :
    (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step) (some c) = some c' := h

/-! ### The one-step equations -/

/-- `lkDone`'s continuation, which the search's own contract deliberately left unrun. -/
theorem tu_step_enter (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (aTM eIn eOut p₀ dzero ddec rest).step
        (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.lkDone)) v temp pay S inp dst scr
          xt rt at' wit pre g)
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuScan)) v temp pay S inp
          dst scr xt rt at' wit pre g) :=
  rfl

/-- Pass one, one symbol. -/
theorem tu_step_scan_cons (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (c : Sym) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (aTM eIn eOut p₀ dzero ddec rest).step
        (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuScan)) v temp pay S inp dst scr
          xt rt (c :: at') wit pre g)
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuScan)) v none pay S inp
          dst (c :: scr) xt rt at' wit pre g) := by
  simp only [aTM, qTM, qCfg, tuCfg, callTM, parentTM, callProgram, prepCont, queryRoute,
    dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute,
    tuScanStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.tuScan), (v, (none, pay)), T⟩ :
      (aTM eIn eOut p₀ dzero ddec rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-- Pass one's empty exit. -/
theorem tu_step_scan_nil (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (aTM eIn eOut p₀ dzero ddec rest).step
        (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuScan)) v temp pay S inp dst scr
          xt rt [] wit pre g)
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuPush)) v none pay S inp
          dst scr xt rt [] wit pre g) := by
  simp only [aTM, qTM, qCfg, tuCfg, callTM, parentTM, callProgram, prepCont, queryRoute,
    dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute,
    tuScanStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.tuPush), (v, (none, pay)), T⟩ :
      (aTM eIn eOut p₀ dzero ddec rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-- The new answer goes on the emptied history tape. -/
theorem tu_step_push (v : tm.σ) (temp : Option Sym) (flag b : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (aTM eIn eOut p₀ dzero ddec rest).step
        (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuPush)) v temp (flag, (b, r)) S
          inp dst scr xt rt at' wit pre g)
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuBack)) v temp
          (flag, (b, r)) S inp dst scr xt rt (Sym.bit b :: at') wit pre g) := by
  simp only [aTM, qTM, qCfg, tuCfg, callTM, parentTM, callProgram, prepCont, queryRoute,
    dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute,
    tuPushStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.tuBack), (v, (temp, (flag, (b, r)))), T⟩ :
      (aTM eIn eOut p₀ dzero ddec rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-- Pass two, one symbol. -/
theorem tu_step_back_cons (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (c : Sym) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (aTM eIn eOut p₀ dzero ddec rest).step
        (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuBack)) v temp pay S inp dst
          (c :: scr) xt rt at' wit pre g)
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuBack)) v none pay S inp
          dst scr xt rt (c :: at') wit pre g) := by
  simp only [aTM, qTM, qCfg, tuCfg, callTM, parentTM, callProgram, prepCont, queryRoute,
    dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute,
    tuBackStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.tuBack), (v, (none, pay)), T⟩ :
      (aTM eIn eOut p₀ dzero ddec rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-- Pass two's empty exit. -/
theorem tu_step_back_nil (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (inp dst xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (aTM eIn eOut p₀ dzero ddec rest).step
        (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuBack)) v temp pay S inp dst []
          xt rt at' wit pre g)
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuClear)) v none pay S inp
          dst [] xt rt at' wit pre g) := by
  simp only [aTM, qTM, qCfg, tuCfg, callTM, parentTM, callProgram, prepCont, queryRoute,
    dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute,
    tuBackStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.tuClear), (v, (none, pay)), T⟩ :
      (aTM eIn eOut p₀ dzero ddec rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-- The spent tuple, one symbol. -/
theorem tu_step_clear_cons (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (c : Sym) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (aTM eIn eOut p₀ dzero ddec rest).step
        (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuClear)) v temp pay S
          (c :: inp) dst scr xt rt at' wit pre g)
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuClear)) v none pay S inp
          dst scr xt rt at' wit pre g) := by
  simp only [aTM, qTM, qCfg, tuCfg, callTM, parentTM, callProgram, prepCont, queryRoute,
    dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute,
    tuClearStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.tuClear), (v, (none, pay)), T⟩ :
      (aTM eIn eOut p₀ dzero ddec rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-- The spent tuple's empty exit. -/
theorem tu_step_clear_nil (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (aTM eIn eOut p₀ dzero ddec rest).step
        (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuClear)) v temp pay S [] dst scr
          xt rt at' wit pre g)
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuDepth)) v none pay S []
          dst scr xt rt at' wit pre g) := by
  simp only [aTM, qTM, qCfg, tuCfg, callTM, parentTM, callProgram, prepCont, queryRoute,
    dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute,
    tuClearStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.tuDepth), (v, (none, pay)), T⟩ :
      (aTM eIn eOut p₀ dzero ddec rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ts <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame, tripleOf]

/-- The depth step: one counted move of finite control, and the next iteration begins. -/
theorem tu_step_depth (v : tm.σ) (temp : Option Sym) (flag b : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (aTM eIn eOut p₀ dzero ddec rest).step
        (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuDepth)) v temp (flag, (b, r)) S
          inp dst scr xt rt at' wit pre g)
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.prepA1)) v none
          (flag, (b, ddec r)) S inp dst scr xt rt at' wit pre g) :=
  rfl

/-! ### The three scans -/

/-- Pass one, with an arbitrary scratch accumulator. -/
theorem tu_scan (at' : List Sym) :
    ∀ (scr : List Sym) (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
      (S : ∀ k, List (tm.Γ k)) (inp dst xt rt wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)^[at'.length + 1]
        (some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuScan)) v temp pay S inp
          dst scr xt rt at' wit pre g))
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuPush)) v none pay S inp
          dst (at'.reverse ++ scr) xt rt [] wit pre g) := by
  induction at' with
  | nil =>
    intro scr v temp pay S inp dst xt rt wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      tu_bind_of_step eIn eOut p₀ dzero ddec rest
        (tu_step_scan_nil eIn eOut p₀ dzero ddec rest v temp pay S inp dst scr xt rt wit pre g)]
    simp
  | cons c at' ih =>
    intro scr v temp pay S inp dst xt rt wit pre g
    change (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)^[(at'.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)
        (at'.length + 1) 1,
      Function.iterate_one,
      tu_bind_of_step eIn eOut p₀ dzero ddec rest
        (tu_step_scan_cons eIn eOut p₀ dzero ddec rest v temp pay S c inp dst scr xt rt at' wit
          pre g),
      ih (c :: scr) v none pay S inp dst xt rt wit pre g]
    simp

/-- Pass two, with an arbitrary history accumulator — which is what puts the new answer at the far
end. -/
theorem tu_back (scr : List Sym) :
    ∀ (at' : List Sym) (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
      (S : ∀ k, List (tm.Γ k)) (inp dst xt rt wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)^[scr.length + 1]
        (some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuBack)) v temp pay S inp
          dst scr xt rt at' wit pre g))
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuClear)) v none pay S inp
          dst [] xt rt (scr.reverse ++ at') wit pre g) := by
  induction scr with
  | nil =>
    intro at' v temp pay S inp dst xt rt wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      tu_bind_of_step eIn eOut p₀ dzero ddec rest
        (tu_step_back_nil eIn eOut p₀ dzero ddec rest v temp pay S inp dst xt rt at' wit pre g)]
    simp
  | cons c scr ih =>
    intro at' v temp pay S inp dst xt rt wit pre g
    change (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)^[(scr.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)
        (scr.length + 1) 1,
      Function.iterate_one,
      tu_bind_of_step eIn eOut p₀ dzero ddec rest
        (tu_step_back_cons eIn eOut p₀ dzero ddec rest v temp pay S c inp dst scr xt rt at' wit
          pre g),
      ih (c :: at') v none pay S inp dst xt rt wit pre g]
    simp

/-- The spent tuple's drain, charged by its length. -/
theorem tu_clear (inp : List Sym) :
    ∀ (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R)) (S : ∀ k, List (tm.Γ k))
      (dst scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)^[inp.length + 1]
        (some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuClear)) v temp pay S inp
          dst scr xt rt at' wit pre g))
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.tuDepth)) v none pay S []
          dst scr xt rt at' wit pre g) := by
  induction inp with
  | nil =>
    intro v temp pay S dst scr xt rt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      tu_bind_of_step eIn eOut p₀ dzero ddec rest
        (tu_step_clear_nil eIn eOut p₀ dzero ddec rest v temp pay S dst scr xt rt at' wit pre g)]
  | cons c inp ih =>
    intro v temp pay S dst scr xt rt at' wit pre g
    change (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)^[(inp.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)
        (inp.length + 1) 1,
      Function.iterate_one,
      tu_bind_of_step eIn eOut p₀ dzero ddec rest
        (tu_step_clear_cons eIn eOut p₀ dzero ddec rest v temp pay S c inp dst scr xt rt at' wit
          pre g),
      ih v none pay S dst scr xt rt at' wit pre g]

/-! ### The turnaround -/

/-- Its exact cost: two passes over the history, the drain of the spent tuple, and six constant
steps — the entry jump, the answer push and the depth step, plus the three empty exits already
counted inside the three scans. -/
def turnSteps (a : List Bool) (inp : List Sym) : ℕ := 2 * a.length + inp.length + 6

/-- **The adaptive turnaround**, from the search's completion boundary back to the preparation
label.

The answer is recorded at the **far** end of the history — `ofBits (a ++ [b])`, matching
`runAdaptive`'s `as ++ [π addr]` — the spent tuple is gone, the call scratch is empty again, and the
depth has taken exactly one `ddec` step.  Two different tapes must be kept apart here: the **call
input** `inp` is deliberately *drained*, while the **source input tape** `xt` and the source seed
tape `rt` are preserved, along with the witness, the prefix stack and the unrelated frame. -/
theorem tu_trace (a : List Bool) (b : Bool) (inp : List Sym) (v : tm.σ) (temp : Option Sym)
    (flag : Bool) (r : R) (S : ∀ k, List (tm.Γ k)) (dst xt rt wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)^[turnSteps a inp]
        (some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.lkDone)) v temp
          (flag, (b, r)) S inp dst [] xt rt (ofBits a) wit pre g))
      = some (tuCfg eIn eOut p₀ dzero ddec rest (some (.inr CallLabel.prepA1)) v none
          (flag, (b, ddec r)) S [] dst [] xt rt (ofBits (a ++ [b])) wit pre g) := by
  have hsplit : turnSteps a inp
      = 1 + ((inp.length + 1) + (((ofBits a).reverse.length + 1)
          + (1 + (((ofBits a).length + 1) + 1)))) := by
    simp only [turnSteps, List.length_reverse, length_ofBits]; omega
  rw [hsplit,
    Function.iterate_add_apply (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step) 1
      ((inp.length + 1) + (((ofBits a).reverse.length + 1)
        + (1 + (((ofBits a).length + 1) + 1)))),
    Function.iterate_add_apply (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)
      (inp.length + 1) (((ofBits a).reverse.length + 1) + (1 + (((ofBits a).length + 1) + 1))),
    Function.iterate_add_apply (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)
      ((ofBits a).reverse.length + 1) (1 + (((ofBits a).length + 1) + 1)),
    Function.iterate_add_apply (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step) 1
      (((ofBits a).length + 1) + 1),
    Function.iterate_add_apply (flip Bind.bind (aTM eIn eOut p₀ dzero ddec rest).step)
      ((ofBits a).length + 1) 1,
    Function.iterate_one,
    tu_bind_of_step eIn eOut p₀ dzero ddec rest
      (tu_step_enter eIn eOut p₀ dzero ddec rest v temp (flag, (b, r)) S inp dst [] xt rt
        (ofBits a) wit pre g),
    tu_scan eIn eOut p₀ dzero ddec rest (ofBits a) [] v temp (flag, (b, r)) S inp dst xt rt wit
      pre g,
    List.append_nil,
    tu_bind_of_step eIn eOut p₀ dzero ddec rest
      (tu_step_push eIn eOut p₀ dzero ddec rest v none flag b r S inp dst
        (ofBits a).reverse xt rt [] wit pre g),
    tu_back eIn eOut p₀ dzero ddec rest (ofBits a).reverse [Sym.bit b] v none
      (flag, (b, r)) S inp dst xt rt wit pre g,
    tu_clear eIn eOut p₀ dzero ddec rest inp v none (flag, (b, r)) S dst []
      xt rt ((ofBits a).reverse.reverse ++ [Sym.bit b]) wit pre g,
    tu_bind_of_step eIn eOut p₀ dzero ddec rest
      (tu_step_depth eIn eOut p₀ dzero ddec rest v none flag b r S [] dst [] xt rt
        ((ofBits a).reverse.reverse ++ [Sym.bit b]) wit pre g)]
  simp [ofBits]

end Steps

/-! ## One complete adaptive iteration

`qRoundEvals` runs `prepA1` to `lkDone`; the turnaround runs `lkDone` back to `prepA1`.  Composing
them closes the loop: one iteration of the checker's adaptive path, on one machine, with one
continuation, and with the answer history advanced exactly as `runAdaptive` advances it. -/

section Iteration

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type} {R : Type} [Fintype R]
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- **One adaptive iteration**, `prepA1` back to `prepA1`.

Preparation, the call to the actual algorithm witness, dispatch, the handoff, the search and the
turnaround.  The history becomes `a ++ [oracleOfWitness w addr]` — the same append `runAdaptive`
performs — the depth takes one `ddec` step, the spent tuple is drained off the **call input**, and
the destination, the call scratch and every callee stack are empty.  The **source** input and seed
tapes, the witness, the prefix stack and the unrelated frame come back untouched.  So the endpoint
satisfies the *starting* precondition again, with `a` one longer.

What it does **not** promise is that the next iteration is another positive query: the depth may now
be zero, or the algorithm may decide.  Those are the terminal rounds.

The recorded count is the round trip's plus the turnaround's; the bound keeps the call polynomial
apart from the two exact costs. -/
noncomputable def aIterEvals
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × R)) (dzero : R → Bool) (ddec : R → R)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))
    (x rs a : List Bool) (addr : ℕ) (hans : f (x, rs, a) = .inr addr) (w : List Bool)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (g : ∀ j : G, List (Γg j))
    (hd : dzero r = false) :
    EvalsToInTime (aTM hw.inputAlphabet hw.outputAlphabet p₀ dzero ddec rest).step
      (tuCfg hw.inputAlphabet hw.outputAlphabet p₀ dzero ddec rest
        (some (.inr CallLabel.prepA1)) v temp (flag, (res, r)) (fun _ => []) [] [] []
        (ofBits x) (ofBits rs) (ofBits a) (ofBits w) [] g)
      (some (tuCfg hw.inputAlphabet hw.outputAlphabet p₀ dzero ddec rest
        (some (.inr CallLabel.prepA1)) hw.tm.initialState none
        (false, (oracleOfWitness w addr, ddec r)) (fun _ => []) [] [] []
        (ofBits x) (ofBits rs) (ofBits (a ++ [oracleOfWitness w addr])) (ofBits w) [] g))
      ((((2 * (x.length + rs.length + a.length) + 8)
            + (callPoly hw.tm hw.time).eval (encodeTriple (x, rs, a)).length)
          + (2 + searchSteps w (Nat.bits addr)))
        + turnSteps a (encodeTriple (x, rs, a))) where
  steps := (qRoundEvals hw p₀ dzero (turnRoute hw.tm G Γg R ddec rest) x rs a addr hans w v temp
      flag res r g hd).steps
    + turnSteps a (encodeTriple (x, rs, a))
  evals_in_steps := by
    have hround := (qRoundEvals hw p₀ dzero (turnRoute hw.tm G Γg R ddec rest) x rs a addr hans w
      v temp flag res r g hd).evals_in_steps
    have hturn := tu_trace hw.inputAlphabet hw.outputAlphabet p₀ dzero ddec rest a
      (oracleOfWitness w addr) (encodeTriple (x, rs, a)) hw.tm.initialState none false r
      (fun _ => []) [] (ofBits x) (ofBits rs) (ofBits w) [] g
    have hc : (qRoundEvals hw p₀ dzero (turnRoute hw.tm G Γg R ddec rest) x rs a addr hans w v
            temp flag res r g hd).steps + turnSteps a (encodeTriple (x, rs, a))
        = turnSteps a (encodeTriple (x, rs, a))
          + (qRoundEvals hw p₀ dzero (turnRoute hw.tm G Γg R ddec rest) x rs a addr hans w v temp
              flag res r g hd).steps := Nat.add_comm _ _
    simp only [tuCfg, ← tripleTapes_eq]
    rw [hc, Function.iterate_add_apply, hround]
    simpa only [tuCfg, ← tripleTapes_eq] using hturn
  steps_le_m := by
    have := (qRoundEvals hw p₀ dzero (turnRoute hw.tm G Γg R ddec rest) x rs a addr hans w v temp
      flag res r g hd).steps_le_m
    omega

@[simp] theorem aIterEvals_steps
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × R)) (dzero : R → Bool) (ddec : R → R)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))
    (x rs a : List Bool) (addr : ℕ) (hans : f (x, rs, a) = .inr addr) (w : List Bool)
    (v : hw.tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (g : ∀ j : G, List (Γg j))
    (hd : dzero r = false) :
    (aIterEvals hw p₀ dzero ddec rest x rs a addr hans w v temp flag res r g hd).steps
      = (qRoundEvals hw p₀ dzero (turnRoute hw.tm G Γg R ddec rest) x rs a addr hans w v temp
          flag res r g hd).steps + turnSteps a (encodeTriple (x, rs, a)) := rfl

/-- The turnaround's share of that count, written out: two passes over the history, the spent
tuple's length, and the six constant steps. -/
theorem turnSteps_encodeTriple (x rs a : List Bool) :
    turnSteps a (encodeTriple (x, rs, a)) = x.length + rs.length + 3 * a.length + 8 := by
  simp only [turnSteps, length_encodeTriple]
  omega

/-- **The semantic unfolding the correspondence proof will use.**

This is a fact about `runAdaptive` alone, quantified over an arbitrary `fstep`: it mentions neither
`aIterEvals` nor its machine, nor `dzero` or `ddec`.  It is *not* a regression tying the machine to
the semantics.  The correspondence proof has to specialise `fstep := fun a => f (x, rs, a)` and
relate the machine's payload depth to the semantic depth `d` — and since `dzero` and `ddec` are
unrelated parameters, that relation is a real obligation, not bookkeeping over an already-certified
decreasing counter. -/
theorem aIter_history (fstep : List Bool → Bool ⊕ ℕ) (w : List Bool) (d : ℕ) (a : List Bool)
    (addr : ℕ) (h : fstep a = .inr addr) :
    runAdaptive fstep (oracleOfWitness w) (d + 1) a
      = runAdaptive fstep (oracleOfWitness w) d (a ++ [oracleOfWitness w addr]) := by
  rw [runAdaptive, h]

end Iteration

end

end PCP.Machine
