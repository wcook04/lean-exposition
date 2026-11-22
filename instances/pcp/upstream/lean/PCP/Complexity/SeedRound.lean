import PCP.Complexity.AdaptiveRun

/-!
# Terminal cleanup, and one reusable seed round

`pathCert` stops at an *active* `decided` or `rejected`, with the spent tuple, the answer history
and — after a rejection — the untouched query numeral still in place.  This module supplies the
continuation of both boundaries and runs them into a common drain, ending at an active
seed-completion label with only the result bit and the data the next seed needs.

## The path is built **on** this program

`pathCert` takes its continuation as a parameter, so the cleanup route is supplied *before* the
certificate is constructed: `rest := cleanRoute _ dreset rest'`.  A certificate built against some
other continuation would not be a certificate for this program merely because the configuration
types agree, and nothing below relies on such an inference.

## The route

```text
decided  ─┐
          ├─1─→ clDst ──|dst|+1──→ clInp ──|inp|+1──→ clHist ──|hist|+1──→ clNorm ─1─→ clDone
rejected ─┘
```

A rejected query's numeral is drained by its encoded length — `lookup` and the turnaround are never
entered, and **no answer is appended to the history**, since this is a terminal result and not
another round.  A decision arrives with an empty destination and still pays its empty exit.

## What `clNorm` does, and the depth convention

One counted step of finite control: clear the temporary, clear the helper flag, keep the result, and
put `R` through the caller's `dreset`.  The concrete `depthReset` below **restores the full budget
`q`**, so the endpoint is immediately reusable by the next seed; that convention is the next seed's
initialization to honour.  Keeping the residual depth instead would be equally sound, and equally in
need of saying so.

## What the endpoint is *not*

It is deliberately not a `haltList`: the source input tape, the current seed, the witness and the
unrelated frame are all retained, because seed iteration needs them.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-! ## Restoring the budget -/

section Reset

variable (q : ℕ) (U : Type)

/-- Restore the full query budget for the next seed, leaving the caller's own data alone. -/
def depthReset : DepthPay q U → DepthPay q U := fun r => (Fin.last q, r.2)

variable {q U}

@[simp] theorem depthReset_fst (r : DepthPay q U) : ((depthReset q U r).1 : ℕ) = q := rfl

@[simp] theorem depthReset_snd (r : DepthPay q U) : (depthReset q U r).2 = r.2 := rfl

/-- The restored counter is zero exactly when the budget itself is. -/
theorem depthZero_reset (r : DepthPay q U) : depthZero q U (depthReset q U r) = true ↔ q = 0 :=
  decide_eq_true_iff

end Reset

/-! ## The cleanup program -/

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (R : Type) [Fintype R]

/-- Both terminal boundaries jump into the common drain. -/
def clEnterStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  goto (fun _ => .inr .clDst)

/-- Drain the destination: a rejected query's numeral, or nothing after a decision. -/
def clDstStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.dst)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .clDst)))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .clInp)))

/-- Drain the spent tuple. -/
def clInpStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.input)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .clInp)))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .clHist)))

/-- Drain the answer history. -/
def clHistStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inr (.inl TripleSlot.as))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .clHist)))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .clNorm)))

/-- One counted step of finite control: temporary cleared, helper flag cleared, **result kept**,
and `R` put through the caller's reset. -/
def clNormStmt (dreset : R → R) : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  load (fun p => (p.1, (none, (false, (p.2.2.2.1, dreset p.2.2.2.2)))))
    (goto (fun _ => .inr .clDone))

/-- The cleanup route: both terminal boundaries and the drain. `clDone` is the seed-completion
boundary and dispatches through `rest`, so reaching it active is this contract's end. -/
def cleanRoute (dreset : R → R)
    (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))
  | .decided => clEnterStmt tm G Γg R
  | .rejected => clEnterStmt tm G Γg R
  | .clDst => clDstStmt tm G Γg R
  | .clInp => clInpStmt tm G Γg R
  | .clHist => clHistStmt tm G Γg R
  | .clNorm => clNormStmt tm G Γg R dreset
  | l => rest l

variable {tm G Γg R}

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × (Bool × R))
  (dzero : R → Bool) (ddec : R → R) (dreset : R → R)
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))

/-- The machine with cleanup supplied. -/
abbrev cTM : FinTM2 :=
  aTM eIn eOut p₀ dzero ddec (cleanRoute tm G Γg R dreset rest)

/-- A configuration of it. -/
def clCfg (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × R)) (S : ∀ k, List (tm.Γ k)) (inp dst scr : List Sym)
    (xt rt at' : List Sym) (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (cTM eIn eOut p₀ dzero ddec dreset rest).Cfg :=
  tuCfg eIn eOut p₀ dzero ddec (cleanRoute tm G Γg R dreset rest) l v temp pay S inp dst scr
    xt rt at' wit pre g

/-- Any one-step equation on this machine, where `Function.iterate` can use it. -/
theorem cl_bind_of_step {c c' : (cTM eIn eOut p₀ dzero ddec dreset rest).Cfg}
    (h : (cTM eIn eOut p₀ dzero ddec dreset rest).step c = some c') :
    (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step) (some c) = some c' := h

/-! ### The one-step equations -/

/-- **Either terminal boundary** enters the common drain in one counted step. -/
theorem cl_step_enter (ans : Bool ⊕ ℕ) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × R)) (S : ∀ k, List (tm.Γ k))
    (inp dst scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (cTM eIn eOut p₀ dzero ddec dreset rest).step
        (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr (terminalLabel ans))) v temp pay S
          inp dst scr xt rt at' wit pre g)
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clDst)) v temp pay S
          inp dst scr xt rt at' wit pre g) := by
  cases ans <;> rfl

/-- The destination drain, one symbol. -/
theorem cl_step_dst_cons (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (c : Sym) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (cTM eIn eOut p₀ dzero ddec dreset rest).step
        (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clDst)) v temp pay S inp
          (c :: dst) scr xt rt at' wit pre g)
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clDst)) v none pay S
          inp dst scr xt rt at' wit pre g) := by
  simp only [cTM, aTM, qTM, clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont,
    queryRoute, dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute,
    turnRoute, cleanRoute, clDstStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.clDst), (v, (none, pay)), T⟩ :
      (cTM eIn eOut p₀ dzero ddec dreset rest).Cfg)) ?_)
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

/-- The destination drain's empty exit — paid even by a decision, which arrives empty. -/
theorem cl_step_dst_nil (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (inp scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (cTM eIn eOut p₀ dzero ddec dreset rest).step
        (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clDst)) v temp pay S inp
          [] scr xt rt at' wit pre g)
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clInp)) v none pay S
          inp [] scr xt rt at' wit pre g) := by
  simp only [cTM, aTM, qTM, clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont,
    queryRoute, dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute,
    turnRoute, cleanRoute, clDstStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.clInp), (v, (none, pay)), T⟩ :
      (cTM eIn eOut p₀ dzero ddec dreset rest).Cfg)) ?_)
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

/-- The spent tuple's drain, one symbol. -/
theorem cl_step_inp_cons (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (c : Sym) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (cTM eIn eOut p₀ dzero ddec dreset rest).step
        (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clInp)) v temp pay S
          (c :: inp) dst scr xt rt at' wit pre g)
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clInp)) v none pay S
          inp dst scr xt rt at' wit pre g) := by
  simp only [cTM, aTM, qTM, clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont,
    queryRoute, dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute,
    turnRoute, cleanRoute, clInpStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.clInp), (v, (none, pay)), T⟩ :
      (cTM eIn eOut p₀ dzero ddec dreset rest).Cfg)) ?_)
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
theorem cl_step_inp_nil (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (cTM eIn eOut p₀ dzero ddec dreset rest).step
        (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clInp)) v temp pay S []
          dst scr xt rt at' wit pre g)
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clHist)) v none pay
          S [] dst scr xt rt at' wit pre g) := by
  simp only [cTM, aTM, qTM, clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont,
    queryRoute, dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute,
    turnRoute, cleanRoute, clInpStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.clHist), (v, (none, pay)), T⟩ :
      (cTM eIn eOut p₀ dzero ddec dreset rest).Cfg)) ?_)
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

/-- The history drain, one symbol. -/
theorem cl_step_hist_cons (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (c : Sym) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (cTM eIn eOut p₀ dzero ddec dreset rest).step
        (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clHist)) v temp pay S inp
          dst scr xt rt (c :: at') wit pre g)
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clHist)) v none pay
          S inp dst scr xt rt at' wit pre g) := by
  simp only [cTM, aTM, qTM, clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont,
    queryRoute, dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute,
    turnRoute, cleanRoute, clHistStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.clHist), (v, (none, pay)), T⟩ :
      (cTM eIn eOut p₀ dzero ddec dreset rest).Cfg)) ?_)
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

/-- The history's empty exit. -/
theorem cl_step_hist_nil (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R))
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (cTM eIn eOut p₀ dzero ddec dreset rest).step
        (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clHist)) v temp pay S inp
          dst scr xt rt [] wit pre g)
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clNorm)) v none pay
          S inp dst scr xt rt [] wit pre g) := by
  simp only [cTM, aTM, qTM, clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont,
    queryRoute, dispatchRoute, handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute,
    turnRoute, cleanRoute, clHistStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.clNorm), (v, (none, pay)), T⟩ :
      (cTM eIn eOut p₀ dzero ddec dreset rest).Cfg)) ?_)
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

/-- Normalisation: temporary and helper flag cleared, **result kept**, `R` reset. -/
theorem cl_step_norm (v : tm.σ) (temp : Option Sym) (flag b : Bool) (r : R)
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (cTM eIn eOut p₀ dzero ddec dreset rest).step
        (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clNorm)) v temp
          (flag, (b, r)) S inp dst scr xt rt at' wit pre g)
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clDone)) v none
          (false, (b, dreset r)) S inp dst scr xt rt at' wit pre g) :=
  rfl

/-! ### The three drains -/

/-- The destination drain, charged by its length. -/
theorem cl_dst (dst : List Sym) :
    ∀ (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R)) (S : ∀ k, List (tm.Γ k))
      (inp scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)^[dst.length + 1]
        (some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clDst)) v temp pay S
          inp dst scr xt rt at' wit pre g))
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clInp)) v none pay S
          inp [] scr xt rt at' wit pre g) := by
  induction dst with
  | nil =>
    intro v temp pay S inp scr xt rt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      cl_bind_of_step eIn eOut p₀ dzero ddec dreset rest
        (cl_step_dst_nil eIn eOut p₀ dzero ddec dreset rest v temp pay S inp scr xt rt at' wit pre
          g)]
  | cons c dst ih =>
    intro v temp pay S inp scr xt rt at' wit pre g
    change (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)^[(dst.length + 1) + 1]
      _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)
        (dst.length + 1) 1,
      Function.iterate_one,
      cl_bind_of_step eIn eOut p₀ dzero ddec dreset rest
        (cl_step_dst_cons eIn eOut p₀ dzero ddec dreset rest v temp pay S c inp dst scr xt rt at'
          wit pre g),
      ih v none pay S inp scr xt rt at' wit pre g]

/-- The spent tuple's drain, charged by its length. -/
theorem cl_inp (inp : List Sym) :
    ∀ (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R)) (S : ∀ k, List (tm.Γ k))
      (dst scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)^[inp.length + 1]
        (some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clInp)) v temp pay S
          inp dst scr xt rt at' wit pre g))
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clHist)) v none pay S
          [] dst scr xt rt at' wit pre g) := by
  induction inp with
  | nil =>
    intro v temp pay S dst scr xt rt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      cl_bind_of_step eIn eOut p₀ dzero ddec dreset rest
        (cl_step_inp_nil eIn eOut p₀ dzero ddec dreset rest v temp pay S dst scr xt rt at' wit pre
          g)]
  | cons c inp ih =>
    intro v temp pay S dst scr xt rt at' wit pre g
    change (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)^[(inp.length + 1) + 1]
      _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)
        (inp.length + 1) 1,
      Function.iterate_one,
      cl_bind_of_step eIn eOut p₀ dzero ddec dreset rest
        (cl_step_inp_cons eIn eOut p₀ dzero ddec dreset rest v temp pay S c inp dst scr xt rt at'
          wit pre g),
      ih v none pay S dst scr xt rt at' wit pre g]

/-- The history drain, charged by its length. -/
theorem cl_hist (at' : List Sym) :
    ∀ (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × R)) (S : ∀ k, List (tm.Γ k))
      (inp dst scr xt rt wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)^[at'.length + 1]
        (some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clHist)) v temp pay
          S inp dst scr xt rt at' wit pre g))
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clNorm)) v none pay S
          inp dst scr xt rt [] wit pre g) := by
  induction at' with
  | nil =>
    intro v temp pay S inp dst scr xt rt wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      cl_bind_of_step eIn eOut p₀ dzero ddec dreset rest
        (cl_step_hist_nil eIn eOut p₀ dzero ddec dreset rest v temp pay S inp dst scr xt rt wit
          pre g)]
  | cons c at' ih =>
    intro v temp pay S inp dst scr xt rt wit pre g
    change (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)^[(at'.length + 1) + 1]
      _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)
        (at'.length + 1) 1,
      Function.iterate_one,
      cl_bind_of_step eIn eOut p₀ dzero ddec dreset rest
        (cl_step_hist_cons eIn eOut p₀ dzero ddec dreset rest v temp pay S c inp dst scr xt rt at'
          wit pre g),
      ih v none pay S inp dst scr xt rt wit pre g]

/-! ### Terminal cleanup -/

/-- Its exact cost: the three drains, the entry jump and the normalisation step.  An empty
destination or history still pays its exit. -/
def cleanupSteps (dst inp at' : List Sym) : ℕ :=
  dst.length + inp.length + at'.length + 5

/-- **Terminal cleanup**, from either terminal boundary to the active seed-completion label.

Stated for an arbitrary destination, spent tuple and history, so it is tied to no particular address
and no particular run: a rejected query's numeral is just the destination here.  The result bit
survives; the source input tape, the seed tape, the witness, the prefix stack and the unrelated
frame are all preserved, because seed iteration needs them. -/
theorem cl_trace (ans : Bool ⊕ ℕ) (dst inp at' : List Sym) (v : tm.σ) (temp : Option Sym)
    (flag b : Bool) (r : R) (S : ∀ k, List (tm.Γ k)) (scr xt rt wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)^[cleanupSteps dst inp at']
        (some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr (terminalLabel ans))) v temp
          (flag, (b, r)) S inp dst scr xt rt at' wit pre g))
      = some (clCfg eIn eOut p₀ dzero ddec dreset rest (some (.inr CallLabel.clDone)) v none
          (false, (b, dreset r)) S [] [] scr xt rt [] wit pre g) := by
  have hsplit : cleanupSteps dst inp at'
      = 1 + ((at'.length + 1) + ((inp.length + 1) + ((dst.length + 1) + 1))) := by
    simp only [cleanupSteps]; omega
  rw [hsplit,
    Function.iterate_add_apply (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step) 1
      ((at'.length + 1) + ((inp.length + 1) + ((dst.length + 1) + 1))),
    Function.iterate_add_apply (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)
      (at'.length + 1) ((inp.length + 1) + ((dst.length + 1) + 1)),
    Function.iterate_add_apply (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)
      (inp.length + 1) ((dst.length + 1) + 1),
    Function.iterate_add_apply (flip Bind.bind (cTM eIn eOut p₀ dzero ddec dreset rest).step)
      (dst.length + 1) 1,
    Function.iterate_one,
    cl_bind_of_step eIn eOut p₀ dzero ddec dreset rest
      (cl_step_enter eIn eOut p₀ dzero ddec dreset rest ans v temp (flag, (b, r)) S inp dst scr xt
        rt at' wit pre g),
    cl_dst eIn eOut p₀ dzero ddec dreset rest dst v temp (flag, (b, r)) S inp scr xt rt at' wit
      pre g,
    cl_inp eIn eOut p₀ dzero ddec dreset rest inp v none (flag, (b, r)) S [] scr xt rt at' wit pre
      g,
    cl_hist eIn eOut p₀ dzero ddec dreset rest at' v none (flag, (b, r)) S [] [] scr xt rt wit pre
      g,
    cl_bind_of_step eIn eOut p₀ dzero ddec dreset rest
      (cl_step_norm eIn eOut p₀ dzero ddec dreset rest v none flag b r S [] [] scr xt rt [] wit
        pre g)]

end Steps

end

/-! ## One reusable seed round

The path is constructed **on the cleanup program**: `pathCert` is instantiated at
`rest := cleanRoute _ (depthReset q U) rest`, and `cl_trace` then runs on that same machine from
the path's own terminal configuration. -/

section Round

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- The seed-completion configuration: only the result bit, the source input and seed tapes, the
witness and the unrelated frame remain, with the budget restored to `q`. -/
noncomputable def seedStop (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U)))
    (x rs w : List Bool) (u : U) (g : ∀ j : G, List (Γg j)) (res : Bool) :
    (pathTM q U hw p₀ (cleanRoute hw.tm G Γg (DepthPay q U) (depthReset q U) rest)).Cfg :=
  tuCfg hw.inputAlphabet hw.outputAlphabet p₀ (depthZero q U) (depthPred q U)
    (cleanRoute hw.tm G Γg (DepthPay q U) (depthReset q U) rest)
    (some (.inr CallLabel.clDone)) hw.tm.initialState none (false, (res, (Fin.last q, u)))
    (fun _ => []) [] [] [] (ofBits x) (ofBits rs) [] (ofBits w) [] g

/-- The adaptive path, constructed on the program that already carries cleanup. -/
noncomputable abbrev seedPath (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U)))
    (x rs w : List Bool) (u : U) (g : ∀ j : G, List (Γg j))
    (d : ℕ) (i : Fin (q + 1)) (hi : (i : ℕ) = d) (a : List Bool) (v : hw.tm.σ)
    (temp : Option Sym) (flag res : Bool) :=
  pathCert q U hw p₀ (cleanRoute hw.tm G Γg (DepthPay q U) (depthReset q U) rest) x rs w u g d i
    hi a v temp flag res

/-- The cleanup share of a seed round, read off the path's own terminal data. -/
noncomputable def seedCleanupSteps (x rs : List Bool) (ans : Bool ⊕ ℕ) (hist : List Bool) : ℕ :=
  cleanupSteps (terminalResid ans) (encodeTriple (x, rs, hist)) (ofBits hist)

/-- **One reusable seed round.**

From `prepA1` with canonical storage at depth `i` and history `a`, through the whole adaptive path
and its terminal cleanup, to an active `clDone` carrying exactly

```text
runAdaptive (fun c => f (x, rs, c)) (oracleOfWitness w) i.val a
```

with the call input, destination, scratch, history, prefix stack and every callee stack empty, the
temporary and helper flag cleared, and the budget restored to `q`.  The source input and seed tapes,
the witness and the unrelated frame are retained for the next seed, so this is deliberately not a
`haltList`.

The recorded count is the path's own plus cleanup's own. -/
noncomputable def seedRoundEvals (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U)))
    (x rs w : List Bool) (u : U) (g : ∀ j : G, List (Γg j))
    (d : ℕ) (i : Fin (q + 1)) (hi : (i : ℕ) = d) (a : List Bool) (v : hw.tm.σ)
    (temp : Option Sym) (flag res : Bool) :
    EvalsToInTime
      (pathTM q U hw p₀ (cleanRoute hw.tm G Γg (DepthPay q U) (depthReset q U) rest)).step
      (pathStart q U hw p₀ (cleanRoute hw.tm G Γg (DepthPay q U) (depthReset q U) rest) x rs w u g
        i a v temp flag res)
      (some (seedStop q U hw p₀ rest x rs w u g
        (runAdaptive (fun c => f (x, rs, c)) (oracleOfWitness w) (i : ℕ) a)))
      ((seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).steps
        + seedCleanupSteps x rs (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).answer
          (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).hist) where
  steps := (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).steps
    + seedCleanupSteps x rs (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).answer
      (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).hist
  evals_in_steps := by
    have hc : (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).steps
          + seedCleanupSteps x rs
            (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).answer
            (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).hist
        = seedCleanupSteps x rs (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).answer
            (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).hist
          + (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).steps := Nat.add_comm _ _
    rw [hc, Function.iterate_add_apply,
      (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).run,
      ← (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).semantics]
    exact cl_trace hw.inputAlphabet hw.outputAlphabet p₀ (depthZero q U) (depthPred q U)
      (depthReset q U) rest (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).answer
      (terminalResid (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).answer)
      (encodeTriple (x, rs, (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).hist))
      (ofBits (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).hist)
      hw.tm.initialState none (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).flagOut
      (terminalBit (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).answer)
      ((seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).depth, u) (fun _ => []) []
      (ofBits x) (ofBits rs) (ofBits w) [] g
  steps_le_m := le_refl _

@[simp] theorem seedRoundEvals_steps (q : ℕ) (U : Type) [Fintype U]
    (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (p₀ : Bool × (Bool × DepthPay q U))
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q U)))
    (x rs w : List Bool) (u : U) (g : ∀ j : G, List (Γg j))
    (d : ℕ) (i : Fin (q + 1)) (hi : (i : ℕ) = d) (a : List Bool) (v : hw.tm.σ)
    (temp : Option Sym) (flag res : Bool) :
    (seedRoundEvals q U hw p₀ rest x rs w u g d i hi a v temp flag res).steps
      = (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).steps
        + seedCleanupSteps x rs (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).answer
          (seedPath q U hw p₀ rest x rs w u g d i hi a v temp flag res).hist := rfl

/-- The cleanup share, written out: the residual destination, the spent tuple, the history twice
over — once inside the tuple, once on its own tape — and the five constant steps. -/
theorem seedCleanupSteps_eq (x rs : List Bool) (ans : Bool ⊕ ℕ) (hist : List Bool) :
    seedCleanupSteps x rs ans hist
      = (terminalResid ans).length + (x.length + rs.length + hist.length + 2) + hist.length
        + 5 := by
  simp [seedCleanupSteps, cleanupSteps]

end Round

end PCP.Machine
