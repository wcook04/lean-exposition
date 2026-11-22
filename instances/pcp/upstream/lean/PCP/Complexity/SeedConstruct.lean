import PCP.Complexity.CanonicalWidth

/-!
# Building the canonical-width seed tape: the program, and one halving pass

This module supplies the program, every one-step equation, the phase traces, and one complete
halving pass with its invariant.  The loop over passes is assembled in `SeedConstructLoop.lean`.

## The route

```text
cwCopy ──|x|+1──→ cwBack ──|x|+1──→ cwTest
cwTest ──(unary tape empty; emit b cells)──1──→ cwDone
cwTest ──(nonempty; emit a cells)──1──→ cwHalf ──m+1──→ cwMove ──m/2+1──→ cwTest
```

* `cwCopy` pops the source input onto the call scratch, pushing one unary marker onto the call
  destination per symbol and **one more** at the empty exit — so the unary tape has length `n + 1`.
  `cwBack` restores the source input.
* `cwTest` peeks at the unary tape.  Nonempty: emit `a` seed cells, clear the parity, halve.
  Empty: emit `b` seed cells and stop.
* `cwHalf` pops the unary tape, pushing a marker onto scratch on every *second* pop — the parity is
  the helper flag, and it starts cleared, so the result has `⌊m / 2⌋` markers.  `cwMove` moves them
  back.

## One program, whatever the input

`a` and `b` are fixed constants of the program; `n` and the width never enter control.  Each
emission of `a` (or `b`) cells is **one statement** — a fixed batch of pushes, `pushBatch` — and
therefore one counted step.  All markers are `Sym.sep` and all emitted cells are `Sym.bit false`,
so no order is at stake in either.

## The pass

From `cwTest` with the unary tape holding `m + 1` markers and scratch empty, one pass takes
`1 + (m + 2) + ((m + 1) / 2 + 1)` steps, emits `a` cells, and returns to `cwTest` with `(m + 1) / 2`
markers — `halvings`' recursion, executed.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-! ## A fixed batch of pushes -/

section Batch

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- `n` pushes of one fixed symbol, as a single statement — so a single counted step. -/
def pushBatch (n : ℕ) (k : K) (c : Γ k) (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  match n with
  | 0 => q
  | n + 1 => TM2.Stmt.push k (fun _ => c) (pushBatch n k c q)

/-- What a batch does.  The decidable-equality instance is an ordinary implicit argument, so this
rewrites under whatever instance the machine at hand carries. -/
theorem stepAux_pushBatch {inst : DecidableEq K} (n : ℕ) (k : K) (c : Γ k) (q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    @TM2.stepAux K Γ Λ σ inst (pushBatch n k c q) v S
      = @TM2.stepAux K Γ Λ σ inst q v (Function.update S k (List.replicate n c ++ S k)) := by
  induction n generalizing S with
  | zero => simp [pushBatch]
  | succ n ih =>
    simp only [pushBatch, TM2.stepAux]
    rw [ih, Function.update_self, Function.update_idem, List.replicate_succ', List.append_assoc]
    rfl

end Batch

/-! ## Halving, as the scan performs it -/

/-- Markers pushed by `m` halving pops starting from parity `p`: every pop taken at parity `true`
pushes one. -/
def halfCount : ℕ → Bool → ℕ
  | 0, _ => 0
  | m + 1, true => halfCount m false + 1
  | m + 1, false => halfCount m true

/-- The parity left after `m` halving pops starting from parity `p`. -/
def halfParity : ℕ → Bool → Bool
  | 0, p => p
  | m + 1, p => halfParity m (!p)

theorem halfCount_both : ∀ m : ℕ, halfCount m false = m / 2 ∧ halfCount m true = (m + 1) / 2
  | 0 => ⟨rfl, rfl⟩
  | m + 1 => by
      obtain ⟨h0, h1⟩ := halfCount_both m
      refine ⟨?_, ?_⟩
      · change halfCount m true = (m + 1) / 2
        exact h1
      · change halfCount m false + 1 = (m + 1 + 1) / 2
        rw [h0]; omega

/-- **From a cleared parity, `m` pops push `⌊m / 2⌋` markers.** -/
theorem halfCount_false (m : ℕ) : halfCount m false = m / 2 := (halfCount_both m).1

theorem halfParity_both : ∀ m : ℕ,
    halfParity m false = decide (m % 2 = 1) ∧ halfParity m true = decide ((m + 1) % 2 = 1)
  | 0 => ⟨rfl, rfl⟩
  | m + 1 => by
      obtain ⟨h0, h1⟩ := halfParity_both m
      refine ⟨?_, ?_⟩
      · change halfParity m true = decide ((m + 1) % 2 = 1)
        exact h1
      · change halfParity m false = decide ((m + 1 + 1) % 2 = 1)
        rw [h0, decide_eq_decide]; omega

theorem halfParity_false (m : ℕ) : halfParity m false = decide (m % 2 = 1) :=
  (halfParity_both m).1

/-! ## The program -/

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (R : Type) [Fintype R] (a b : ℕ)

/-- Copy the input's **length** into unary on the call destination, the input itself onto scratch;
one extra marker at the empty exit makes the unary length `n + 1`. -/
def cwCopyStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inr (.inl TripleSlot.xs))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inl CallSlot.scratch)) (fun p => p.2.1.getD Sym.sep)
        (push (.inr (.inl CallSlot.dst)) (fun _ => Sym.sep)
          (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .cwCopy)))))
      (push (.inr (.inl CallSlot.dst)) (fun _ => Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .cwBack))))

/-- Restore the source input from scratch. -/
def cwBackStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.scratch)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inr (.inl TripleSlot.xs))) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .cwBack))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .cwTest)))

/-- The pass test: a nonempty unary tape earns `a` seed cells and a halving; an empty one earns the
final `b` cells. -/
def cwTestStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  peek (.inr (.inl CallSlot.dst)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (pushBatch a (.inr (.inr (.inl TripleSlot.rs))) (Sym.bit false)
        (load (fun p => (p.1, (none, (false, p.2.2.2)))) (goto (fun _ => .inr .cwHalf))))
      (pushBatch b (.inr (.inr (.inl TripleSlot.rs))) (Sym.bit false)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .cwDone))))

/-- Halving: one marker to scratch on every second pop.  The parity is the helper flag. -/
def cwHalfStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.dst)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (branch (fun p => p.2.2.1)
        (push (.inr (.inl CallSlot.scratch)) (fun _ => Sym.sep)
          (load (fun p => (p.1, (none, (!p.2.2.1, p.2.2.2)))) (goto (fun _ => .inr .cwHalf))))
        (load (fun p => (p.1, (none, (!p.2.2.1, p.2.2.2)))) (goto (fun _ => .inr .cwHalf))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .cwMove)))

/-- Move the halved tape back. -/
def cwMoveStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.scratch)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inl CallSlot.dst)) (fun _ => Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .cwMove))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .cwTest)))

/-- The construction's labels.  `cwDone` is its active boundary, dispatching through `rest`. -/
def cwRoute (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))
  | .cwCopy => cwCopyStmt tm G Γg R
  | .cwBack => cwBackStmt tm G Γg R
  | .cwTest => cwTestStmt tm G Γg R a b
  | .cwHalf => cwHalfStmt tm G Γg R
  | .cwMove => cwMoveStmt tm G Γg R
  | l => rest l

variable {tm G Γg R}

section Steps

variable {q : ℕ} {U₀ : Type} [Fintype U₀]
  (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg)
    (Bool × (Bool × DepthPay q (Bool × U₀))))

/-- The whole machine, with the construction in its continuation. -/
abbrev wTM : FinTM2 := eTM eIn eOut p₀ (cwRoute tm G Γg (DepthPay q (Bool × U₀)) a b rest)

/-- A configuration of it. -/
def wCfg (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp dst scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).Cfg :=
  enCfg eIn eOut p₀ (cwRoute tm G Γg (DepthPay q (Bool × U₀)) a b rest) l v temp pay S inp dst scr
    xt rt at' wit pre g

theorem cw_bind_of_step {c c' : (wTM a b eIn eOut p₀ rest).Cfg}
    (h : (wTM a b eIn eOut p₀ rest).step c = some c') :
    (flip Bind.bind (wTM a b eIn eOut p₀ rest).step) (some c) = some c' := h

/-! ### The one-step equations -/

/-- Copying one input symbol: onto scratch, and one unary marker onto the destination. -/
theorem cw_step_copy_cons (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
    (S : ∀ k, List (tm.Γ k)) (c : Sym) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwCopy)) v temp pay S inp dst scr (c :: xt)
          rt at' wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwCopy)) v none pay S inp
          (Sym.sep :: dst) (c :: scr) xt rt at' wit pre g) := by
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwCopyStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwCopy), (v, (none, pay)), T⟩ : (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- The input exhausted: one more marker, so the unary length is `n + 1`. -/
theorem cw_step_copy_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
    (S : ∀ k, List (tm.Γ k)) (inp dst scr rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwCopy)) v temp pay S inp dst scr [] rt
          at' wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwBack)) v none pay S inp
          (Sym.sep :: dst) scr [] rt at' wit pre g) := by
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwCopyStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwBack), (v, (none, pay)), T⟩ : (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Restoring the input, one symbol. -/
theorem cw_step_back_cons (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
    (S : ∀ k, List (tm.Γ k)) (c : Sym) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwBack)) v temp pay S inp dst (c :: scr) xt
          rt at' wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwBack)) v none pay S inp dst scr
          (c :: xt) rt at' wit pre g) := by
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwBackStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwBack), (v, (none, pay)), T⟩ : (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Restoring's empty exit. -/
theorem cw_step_back_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
    (S : ∀ k, List (tm.Γ k)) (inp dst xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwBack)) v temp pay S inp dst [] xt rt at'
          wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v none pay S inp dst [] xt
          rt at' wit pre g) := by
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwBackStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwTest), (v, (none, pay)), T⟩ : (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- **A nonempty pass test**: `a` seed cells in one step, parity cleared, halving begins.  The peek
leaves the unary tape alone. -/
theorem cw_step_test_some (v : tm.σ) (temp : Option Sym) (flag res : Bool)
    (r : DepthPay q (Bool × U₀)) (S : ∀ k, List (tm.Γ k)) (c : Sym)
    (inp dst scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v temp (flag, (res, r)) S inp
          (c :: dst) scr xt rt at' wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwHalf)) v none (false, (res, r)) S
          inp (c :: dst) scr xt (List.replicate a (Sym.bit false) ++ rt) at' wit pre g) := by
  change some (TM2.stepAux ((wTM a b eIn eOut p₀ rest).m (Sum.inr CallLabel.cwTest))
      (v, (temp, (flag, (res, r))))
      (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v temp (flag, (res, r)) S inp
        (c :: dst) scr xt rt at' wit pre g).stk) = _
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwTestStmt, prepCfg, callCfg, TM2.stepAux, embedStacks_inr,
    callFrame, List.head?_cons, Option.isSome_some, Bool.cond_true]
  -- `erw`: the statement's decidable-equality instance is the machine's own field, equal to the
  -- synthesised one only up to unfolding the machine.
  erw [stepAux_pushBatch]
  simp only [TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwHalf), (v, (none, (false, (res, r)))), T⟩ :
      (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- **The empty pass test**: the final `b` cells, in one step, and the construction's boundary. -/
theorem cw_step_test_none (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
    (S : ∀ k, List (tm.Γ k)) (inp scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v temp pay S inp [] scr xt rt at'
          wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwDone)) v none pay S inp [] scr xt
          (List.replicate b (Sym.bit false) ++ rt) at' wit pre g) := by
  change some (TM2.stepAux ((wTM a b eIn eOut p₀ rest).m (Sum.inr CallLabel.cwTest))
      (v, (temp, pay))
      (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v temp pay S inp [] scr xt rt at'
        wit pre g).stk) = _
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwTestStmt, prepCfg, callCfg, TM2.stepAux, embedStacks_inr,
    callFrame, List.head?_nil, Option.isSome_none, Bool.cond_false]
  erw [stepAux_pushBatch]
  simp only [TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwDone), (v, (none, pay)), T⟩ : (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Halving, parity set: this pop earns a marker, and the parity flips. -/
theorem cw_step_half_true (v : tm.σ) (temp : Option Sym) (res : Bool)
    (r : DepthPay q (Bool × U₀)) (S : ∀ k, List (tm.Γ k)) (c : Sym)
    (inp dst scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwHalf)) v temp (true, (res, r)) S inp
          (c :: dst) scr xt rt at' wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwHalf)) v none (false, (res, r)) S
          inp dst (Sym.sep :: scr) xt rt at' wit pre g) := by
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwHalfStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwHalf), (v, (none, (false, (res, r)))), T⟩ :
      (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Halving, parity clear: this pop earns nothing, and the parity flips. -/
theorem cw_step_half_false (v : tm.σ) (temp : Option Sym) (res : Bool)
    (r : DepthPay q (Bool × U₀)) (S : ∀ k, List (tm.Γ k)) (c : Sym)
    (inp dst scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwHalf)) v temp (false, (res, r)) S inp
          (c :: dst) scr xt rt at' wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwHalf)) v none (true, (res, r)) S
          inp dst scr xt rt at' wit pre g) := by
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwHalfStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwHalf), (v, (none, (true, (res, r)))), T⟩ :
      (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Halving's empty exit. -/
theorem cw_step_half_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
    (S : ∀ k, List (tm.Γ k)) (inp scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwHalf)) v temp pay S inp [] scr xt rt at'
          wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwMove)) v none pay S inp [] scr xt
          rt at' wit pre g) := by
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwHalfStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwMove), (v, (none, pay)), T⟩ : (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Moving the halved tape back, one marker. -/
theorem cw_step_move_cons (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
    (S : ∀ k, List (tm.Γ k)) (c : Sym) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwMove)) v temp pay S inp dst (c :: scr) xt
          rt at' wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwMove)) v none pay S inp
          (Sym.sep :: dst) scr xt rt at' wit pre g) := by
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwMoveStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwMove), (v, (none, pay)), T⟩ : (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Moving's empty exit, back at the pass test. -/
theorem cw_step_move_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
    (S : ∀ k, List (tm.Γ k)) (inp dst xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (wTM a b eIn eOut p₀ rest).step
        (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwMove)) v temp pay S inp dst [] xt rt at'
          wit pre g)
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v none pay S inp dst [] xt
          rt at' wit pre g) := by
  simp only [wTM, eTM, iTM, cTM, aTM, qTM, wCfg, enCfg, inCfg, clCfg, tuCfg,
    qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, cwMoveStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwTest), (v, (none, pay)), T⟩ : (wTM a b eIn eOut p₀ rest).Cfg)) ?_)
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


/-! ### The phases -/

/-- **Copying the input's length into unary**, with arbitrary accumulators: the input lands
reversed on scratch, and the unary tape gains one marker per symbol plus one. -/
theorem cw_copy (xs0 : List Sym) :
    ∀ (scr dst : List Sym) (v : tm.σ) (temp : Option Sym)
      (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
      (inp rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[xs0.length + 1]
        (some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwCopy)) v temp pay S inp dst scr xs0
          rt at' wit pre g))
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwBack)) v none pay S inp
          (List.replicate (xs0.length + 1) Sym.sep ++ dst) (xs0.reverse ++ scr) [] rt at' wit pre
          g) := by
  induction xs0 with
  | nil =>
    intro scr dst v temp pay S inp rt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      cw_bind_of_step a b eIn eOut p₀ rest
        (cw_step_copy_nil a b eIn eOut p₀ rest v temp pay S inp dst scr rt at' wit pre g)]
    simp
  | cons c xs0 ih =>
    intro scr dst v temp pay S inp rt at' wit pre g
    change (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[(xs0.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)
        (xs0.length + 1) 1, Function.iterate_one,
      cw_bind_of_step a b eIn eOut p₀ rest
        (cw_step_copy_cons a b eIn eOut p₀ rest v temp pay S c inp dst scr xs0 rt at' wit pre g),
      ih (c :: scr) (Sym.sep :: dst) v none pay S inp rt at' wit pre g]
    simp [List.replicate_succ']

/-- **Restoring the input**, with an arbitrary accumulator. -/
theorem cw_back (scr0 : List Sym) :
    ∀ (xt dst : List Sym) (v : tm.σ) (temp : Option Sym)
      (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
      (inp rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[scr0.length + 1]
        (some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwBack)) v temp pay S inp dst scr0 xt
          rt at' wit pre g))
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v none pay S inp dst []
          (scr0.reverse ++ xt) rt at' wit pre g) := by
  induction scr0 with
  | nil =>
    intro xt dst v temp pay S inp rt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      cw_bind_of_step a b eIn eOut p₀ rest
        (cw_step_back_nil a b eIn eOut p₀ rest v temp pay S inp dst xt rt at' wit pre g)]
    simp
  | cons c scr0 ih =>
    intro xt dst v temp pay S inp rt at' wit pre g
    change (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[(scr0.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)
        (scr0.length + 1) 1, Function.iterate_one,
      cw_bind_of_step a b eIn eOut p₀ rest
        (cw_step_back_cons a b eIn eOut p₀ rest v temp pay S c inp dst scr0 xt rt at' wit pre g),
      ih (c :: xt) dst v none pay S inp rt at' wit pre g]
    simp

/-- **The halving scan and its invariant**, with an arbitrary scratch accumulator: `m` pops from
parity `p` push `halfCount m p` markers and leave parity `halfParity m p`.  `halfCount_false` and
`halfParity_false` then read these as `⌊m / 2⌋` and `m mod 2`. -/
theorem cw_half (m : ℕ) :
    ∀ (p : Bool) (scr : List Sym) (v : tm.σ) (temp : Option Sym) (res : Bool)
      (r : DepthPay q (Bool × U₀)) (S : ∀ k, List (tm.Γ k)) (inp xt rt at' wit pre : List Sym)
      (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[m + 1]
        (some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwHalf)) v temp (p, (res, r)) S inp
          (List.replicate m Sym.sep) scr xt rt at' wit pre g))
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwMove)) v none
          (halfParity m p, (res, r)) S inp [] (List.replicate (halfCount m p) Sym.sep ++ scr) xt rt
          at' wit pre g) := by
  induction m with
  | zero =>
    intro p scr v temp res r S inp xt rt at' wit pre g
    rw [Nat.zero_add, Function.iterate_one, List.replicate_zero,
      cw_bind_of_step a b eIn eOut p₀ rest
        (cw_step_half_nil a b eIn eOut p₀ rest v temp (p, (res, r)) S inp scr xt rt at' wit pre g)]
    simp [halfCount, halfParity]
  | succ m ih =>
    intro p scr v temp res r S inp xt rt at' wit pre g
    change (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[(m + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (wTM a b eIn eOut p₀ rest).step) (m + 1) 1,
      Function.iterate_one, List.replicate_succ]
    cases p with
    | true =>
      rw [cw_bind_of_step a b eIn eOut p₀ rest
          (cw_step_half_true a b eIn eOut p₀ rest v temp res r S Sym.sep inp
            (List.replicate m Sym.sep) scr xt rt at' wit pre g),
        ih false (Sym.sep :: scr) v none res r S inp xt rt at' wit pre g]
      simp [halfCount, halfParity, List.replicate_succ']
    | false =>
      rw [cw_bind_of_step a b eIn eOut p₀ rest
          (cw_step_half_false a b eIn eOut p₀ rest v temp res r S Sym.sep inp
            (List.replicate m Sym.sep) scr xt rt at' wit pre g),
        ih true scr v none res r S inp xt rt at' wit pre g]
      simp [halfCount, halfParity]

/-- **Moving the halved tape back**, with an arbitrary accumulator. -/
theorem cw_move (L : List Sym) :
    ∀ (dst : List Sym) (v : tm.σ) (temp : Option Sym)
      (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
      (inp xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[L.length + 1]
        (some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwMove)) v temp pay S inp dst L xt rt
          at' wit pre g))
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v none pay S inp
          (List.replicate L.length Sym.sep ++ dst) [] xt rt at' wit pre g) := by
  induction L with
  | nil =>
    intro dst v temp pay S inp xt rt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      cw_bind_of_step a b eIn eOut p₀ rest
        (cw_step_move_nil a b eIn eOut p₀ rest v temp pay S inp dst xt rt at' wit pre g)]
    simp
  | cons c L ih =>
    intro dst v temp pay S inp xt rt at' wit pre g
    change (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[(L.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)
        (L.length + 1) 1, Function.iterate_one,
      cw_bind_of_step a b eIn eOut p₀ rest
        (cw_step_move_cons a b eIn eOut p₀ rest v temp pay S c inp dst L xt rt at' wit pre g),
      ih (Sym.sep :: dst) v none pay S inp xt rt at' wit pre g]
    simp [List.replicate_succ']

/-! ### One halving pass -/

/-- **One complete halving pass** — the statement to review before the loop is assembled.

From `cwTest` with `m + 1` unary markers and empty scratch: the pass emits exactly `a` seed cells,
halves the unary tape to `(m + 1) / 2` markers — `halvings`' own recursion — leaves scratch empty,
and returns to `cwTest`.  It costs `(m + 1) + (m + 1) / 2 + 3` steps: the test, the halving scan
with its empty exit, and the move back with its empty exit.  The source input, the witness, the
history, the call input and the unrelated frame are untouched.  The parity is left in the helper
flag: only a **nonempty** next test clears it — the final, empty test preserves it. -/
theorem cw_pass (m : ℕ) (v : tm.σ) (temp : Option Sym) (flag res : Bool)
    (r : DepthPay q (Bool × U₀)) (S : ∀ k, List (tm.Γ k)) (inp xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[(m + 1) + (m + 1) / 2 + 3]
        (some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v temp (flag, (res, r)) S
          inp (List.replicate (m + 1) Sym.sep) [] xt rt at' wit pre g))
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v none
          (decide ((m + 1) % 2 = 1), (res, r)) S inp (List.replicate ((m + 1) / 2) Sym.sep) [] xt
          (List.replicate a (Sym.bit false) ++ rt) at' wit pre g) := by
  have hhalf := cw_half a b eIn eOut p₀ rest (m + 1) false [] v none res r S inp xt
    (List.replicate a (Sym.bit false) ++ rt) at' wit pre g
  rw [halfCount_false, halfParity_false, List.append_nil] at hhalf
  have hmove := cw_move a b eIn eOut p₀ rest (List.replicate ((m + 1) / 2) Sym.sep) [] v none
    (decide ((m + 1) % 2 = 1), (res, r)) S inp xt (List.replicate a (Sym.bit false) ++ rt) at' wit
    pre g
  simp only [List.length_replicate, List.append_nil] at hmove
  have hsplit : (m + 1) + (m + 1) / 2 + 3 = ((m + 1) / 2 + 1) + ((m + 1 + 1) + 1) := by omega
  rw [hsplit,
    Function.iterate_add_apply (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)
      ((m + 1) / 2 + 1) ((m + 1 + 1) + 1),
    Function.iterate_add_apply (flip Bind.bind (wTM a b eIn eOut p₀ rest).step) (m + 1 + 1) 1,
    Function.iterate_one, List.replicate_succ,
    cw_bind_of_step a b eIn eOut p₀ rest
      (cw_step_test_some a b eIn eOut p₀ rest v temp flag res r S Sym.sep inp
        (List.replicate m Sym.sep) [] xt rt at' wit pre g),
    ← List.replicate_succ, hhalf, hmove]

/-- **The final test**: an empty unary tape earns the last `b` cells and ends the construction. -/
theorem cw_final (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
    (S : ∀ k, List (tm.Γ k)) (inp xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[1]
        (some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v temp pay S inp [] [] xt rt
          at' wit pre g))
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwDone)) v none pay S inp [] [] xt
          (List.replicate b (Sym.bit false) ++ rt) at' wit pre g) := by
  rw [Function.iterate_one]
  exact cw_bind_of_step a b eIn eOut p₀ rest
    (cw_step_test_none a b eIn eOut p₀ rest v temp pay S inp [] xt rt at' wit pre g)

/-- **Building the unary tape**: copy and restore, `2 · x.length + 2` steps from `cwCopy` to the
first `cwTest`, the source input back in place and the unary tape holding `x.length + 1`
markers. -/
theorem cw_unary (xs0 : List Sym) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (wTM a b eIn eOut p₀ rest).step)^[2 * xs0.length + 2]
        (some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwCopy)) v temp pay S inp [] [] xs0
          rt at' wit pre g))
      = some (wCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwTest)) v none pay S inp
          (List.replicate (xs0.length + 1) Sym.sep) [] xs0 rt at' wit pre g) := by
  have hsplit : 2 * xs0.length + 2 = (xs0.reverse.length + 1) + (xs0.length + 1) := by
    simp only [List.length_reverse]; omega
  rw [hsplit, Function.iterate_add_apply,
    cw_copy a b eIn eOut p₀ rest xs0 [] [] v temp pay S inp rt at' wit pre g, List.append_nil,
    List.append_nil,
    cw_back a b eIn eOut p₀ rest xs0.reverse [] (List.replicate (xs0.length + 1) Sym.sep) v none
      pay S inp rt at' wit pre g]
  simp

end Steps

end

end PCP.Machine
