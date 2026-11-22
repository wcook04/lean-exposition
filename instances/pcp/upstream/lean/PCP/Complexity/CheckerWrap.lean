import PCP.Complexity.SeedConstructLoop

/-!
# The checker's wrapper: handoff, identity, and the pair parser

## One program for the whole checker

`wrapRoute` supplies the last continuation labels the checker needs before finalisation:
`cwDone`'s handoff to `prepA1`, and the four statements of the pair parser.  Every certificate
below — construction, enumeration, parser — is instantiated at `rest := wrapRoute _ rest'`, so they
all run on **one** program.

## The wrapper's identity

The internal machine's designated stacks and main label are the *callee's*: they belong to the
subroutine calls, not to the checker.  `wrapTM` keeps the internal machine's stack family, states,
equality instance, labels and program — so its transition function is the same, `wrapTM_step` —
and changes only what `initList` and `haltList` read:

* the external **input** stack is the caller's `CallSlot.input`, and the external **output** stack
  is `CallSlot.dst`, both over `Sym` and both distinct from every callee stack, whether or not the
  callee's own input and output stacks coincide;
* the **main label** is the parser's entry `pdSplit`;
* the initial payload has **full depth** `Fin.last q` and **aggregate `true`**, so neither needs a
  counted initialisation step.

## The parser

```text
pdSplit ──n+1──→ pdBackX ──n+1──→ pdRest ──W+1──→ pdBackW ──W+1──→ cwCopy
```

`pdSplit` moves the input component onto scratch and consumes the separator; `pdBackX` restores it
onto the source input tape in order; `pdRest` moves the witness component onto scratch; `pdBackW`
restores it onto the witness stack.  On `encodePair (x, w)` that is `2L + 2` steps with
`L = x.length + w.length + 1`.  A malformed input with no separator is sent on to `pdBackX` all the
same: the program is total, and nothing is claimed about such inputs.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (R : Type) [Fintype R]

/-- The handoff: construction done, the first seed's round begins. -/
def hoStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  goto (fun _ => .inr .prepA1)

/-- Split: move input-component bits onto scratch; the separator ends the phase.  (A missing
separator ends it too — the program is total.) -/
def pdSplitStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.input)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => decide (p.2.1 = some Sym.sep))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .pdBackX)))
      (branch (fun p => p.2.1.isSome)
        (push (.inr (.inl CallSlot.scratch)) (fun p => p.2.1.getD Sym.sep)
          (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .pdSplit))))
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .pdBackX))))

/-- Restore the input component onto the source input tape. -/
def pdBackXStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.scratch)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inr (.inl TripleSlot.xs))) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .pdBackX))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .pdRest)))

/-- Move the witness component onto scratch. -/
def pdRestStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.input)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inl CallSlot.scratch)) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .pdRest))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .pdBackW)))

/-- Restore the witness component onto the witness stack, then construct the seed. -/
def pdBackWStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl CallSlot.scratch)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inr (.inr (.inl LookupSlot.witness)))) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .pdBackW))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .cwCopy)))

/-- The wrapper's labels before finalisation: the handoff and the parser. -/
def wrapRoute (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))
  | .cwDone => hoStmt tm G Γg R
  | .pdSplit => pdSplitStmt tm G Γg R
  | .pdBackX => pdBackXStmt tm G Γg R
  | .pdRest => pdRestStmt tm G Γg R
  | .pdBackW => pdBackWStmt tm G Γg R
  | l => rest l

variable {tm G Γg R}

section Steps

variable {q : ℕ} {U₀ : Type} [Fintype U₀] (a b : ℕ)
  (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × (Bool × DepthPay q (Bool × U₀)))
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg)
    (Bool × (Bool × DepthPay q (Bool × U₀))))

/-- The internal machine: everything, on one program. -/
abbrev xTM : FinTM2 := wTM a b eIn eOut p₀ (wrapRoute tm G Γg (DepthPay q (Bool × U₀)) rest)

/-- A configuration of it. -/
def xCfg (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp dst scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).Cfg :=
  wCfg a b eIn eOut p₀ (wrapRoute tm G Γg (DepthPay q (Bool × U₀)) rest) l v temp pay S inp dst
    scr xt rt at' wit pre g

theorem x_bind_of_step {c c' : (xTM a b eIn eOut p₀ rest).Cfg}
    (h : (xTM a b eIn eOut p₀ rest).step c = some c') :
    (flip Bind.bind (xTM a b eIn eOut p₀ rest).step) (some c) = some c' := h

/-- **The handoff**, one counted step preserving every field and stack. -/
theorem x_step_handoff (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).step
        (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwDone)) v temp pay S inp dst scr xt rt at'
          wit pre g)
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.prepA1)) v temp pay S inp dst scr xt
          rt at' wit pre g) :=
  rfl

/-! ### The parser's one-step equations -/

/-- Split, a bit of the input component: onto scratch. -/
theorem x_step_split_bit (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k)) (bit : Bool)
    (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).step
        (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdSplit)) v temp pay S
          (Sym.bit bit :: inp) dst scr xt rt at' wit pre g)
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdSplit)) v none pay S
          inp dst (Sym.bit bit :: scr) xt rt at' wit pre g) := by
  simp only [xTM, wTM, eTM, iTM, cTM, aTM, qTM, xCfg, wCfg, enCfg, inCfg, clCfg,
    tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, wrapRoute, pdSplitStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.pdSplit), (v, (none, pay)), T⟩ : (xTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Split, the separator: consumed, and the phase ends. -/
theorem x_step_split_sep (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).step
        (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdSplit)) v temp pay S
          (Sym.sep :: inp) dst scr xt rt at' wit pre g)
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackX)) v none pay S
          inp dst scr xt rt at' wit pre g) := by
  simp only [xTM, wTM, eTM, iTM, cTM, aTM, qTM, xCfg, wCfg, enCfg, inCfg, clCfg,
    tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, wrapRoute, pdSplitStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.pdBackX), (v, (none, pay)), T⟩ : (xTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Split, no separator at all: the phase ends too — the program is total. -/
theorem x_step_split_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).step
        (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdSplit)) v temp pay S
          [] dst scr xt rt at' wit pre g)
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackX)) v none pay S
          [] dst scr xt rt at' wit pre g) := by
  simp only [xTM, wTM, eTM, iTM, cTM, aTM, qTM, xCfg, wCfg, enCfg, inCfg, clCfg,
    tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, wrapRoute, pdSplitStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.pdBackX), (v, (none, pay)), T⟩ : (xTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Restoring the input component, one symbol. -/
theorem x_step_backX_cons (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k)) (c : Sym)
    (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).step
        (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackX)) v temp pay S
          inp dst (c :: scr) xt rt at' wit pre g)
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackX)) v none pay S
          inp dst scr (c :: xt) rt at' wit pre g) := by
  simp only [xTM, wTM, eTM, iTM, cTM, aTM, qTM, xCfg, wCfg, enCfg, inCfg, clCfg,
    tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, wrapRoute, pdBackXStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.pdBackX), (v, (none, pay)), T⟩ : (xTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Restoring the input component, the empty exit. -/
theorem x_step_backX_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp dst xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).step
        (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackX)) v temp pay S
          inp dst [] xt rt at' wit pre g)
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdRest)) v none pay S
          inp dst [] xt rt at' wit pre g) := by
  simp only [xTM, wTM, eTM, iTM, cTM, aTM, qTM, xCfg, wCfg, enCfg, inCfg, clCfg,
    tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, wrapRoute, pdBackXStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.pdRest), (v, (none, pay)), T⟩ : (xTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Moving the witness component, one symbol. -/
theorem x_step_rest_cons (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k)) (c : Sym)
    (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).step
        (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdRest)) v temp pay S
          (c :: inp) dst scr xt rt at' wit pre g)
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdRest)) v none pay S
          inp dst (c :: scr) xt rt at' wit pre g) := by
  simp only [xTM, wTM, eTM, iTM, cTM, aTM, qTM, xCfg, wCfg, enCfg, inCfg, clCfg,
    tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, wrapRoute, pdRestStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.pdRest), (v, (none, pay)), T⟩ : (xTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Moving the witness component, the empty exit. -/
theorem x_step_rest_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).step
        (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdRest)) v temp pay S
          [] dst scr xt rt at' wit pre g)
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackW)) v none pay S
          [] dst scr xt rt at' wit pre g) := by
  simp only [xTM, wTM, eTM, iTM, cTM, aTM, qTM, xCfg, wCfg, enCfg, inCfg, clCfg,
    tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, wrapRoute, pdRestStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.pdBackW), (v, (none, pay)), T⟩ : (xTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Restoring the witness component, one symbol. -/
theorem x_step_backW_cons (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k)) (c : Sym)
    (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).step
        (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackW)) v temp pay S
          inp dst (c :: scr) xt rt at' wit pre g)
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackW)) v none pay S
          inp dst scr xt rt at' (c :: wit) pre g) := by
  simp only [xTM, wTM, eTM, iTM, cTM, aTM, qTM, xCfg, wCfg, enCfg, inCfg, clCfg,
    tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, wrapRoute, pdBackWStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.pdBackW), (v, (none, pay)), T⟩ : (xTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-- Restoring the witness component, the empty exit — into the construction. -/
theorem x_step_backW_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp dst xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (xTM a b eIn eOut p₀ rest).step
        (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackW)) v temp pay S
          inp dst [] xt rt at' wit pre g)
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwCopy)) v none pay S
          inp dst [] xt rt at' wit pre g) := by
  simp only [xTM, wTM, eTM, iTM, cTM, aTM, qTM, xCfg, wCfg, enCfg, inCfg, clCfg,
    tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute, handoffRoute,
    lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute, incRoute,
    enumRoute, cwRoute, wrapRoute, pdBackWStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.cwCopy), (v, (none, pay)), T⟩ : (xTM a b eIn eOut p₀ rest).Cfg)) ?_)
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

/-! ### The parser's phases -/

/-- **Split**, with an arbitrary scratch accumulator: the input component lands reversed on
scratch, and the separator is consumed. -/
theorem x_split (bs : List Bool) :
    ∀ (tail scr : List Sym) (v : tm.σ) (temp : Option Sym)
      (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
      (dst xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)^[bs.length + 1]
        (some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdSplit)) v temp pay S
          (ofBits bs ++ Sym.sep :: tail) dst scr xt rt at' wit pre g))
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackX)) v none pay S tail dst
          ((ofBits bs).reverse ++ scr) xt rt at' wit pre g) := by
  induction bs with
  | nil =>
    intro tail scr v temp pay S dst xt rt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one, ofBits_nil, List.nil_append,
      x_bind_of_step a b eIn eOut p₀ rest
        (x_step_split_sep a b eIn eOut p₀ rest v temp pay S tail dst scr xt rt at' wit pre g)]
    simp
  | cons c bs ih =>
    intro tail scr v temp pay S dst xt rt at' wit pre g
    change (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)^[(bs.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)
        (bs.length + 1) 1, Function.iterate_one, ofBits_cons, List.cons_append,
      x_bind_of_step a b eIn eOut p₀ rest
        (x_step_split_bit a b eIn eOut p₀ rest v temp pay S c (ofBits bs ++ Sym.sep :: tail) dst
          scr xt rt at' wit pre g),
      ih tail (Sym.bit c :: scr) v none pay S dst xt rt at' wit pre g]
    simp

/-- **Restoring the input component**, with an arbitrary accumulator. -/
theorem x_backX (L : List Sym) :
    ∀ (xt : List Sym) (v : tm.σ) (temp : Option Sym)
      (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
      (inp dst rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)^[L.length + 1]
        (some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackX)) v temp pay S inp dst L xt
          rt at' wit pre g))
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdRest)) v none pay S inp dst []
          (L.reverse ++ xt) rt at' wit pre g) := by
  induction L with
  | nil =>
    intro xt v temp pay S inp dst rt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      x_bind_of_step a b eIn eOut p₀ rest
        (x_step_backX_nil a b eIn eOut p₀ rest v temp pay S inp dst xt rt at' wit pre g)]
    simp
  | cons c L ih =>
    intro xt v temp pay S inp dst rt at' wit pre g
    change (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)^[(L.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)
        (L.length + 1) 1, Function.iterate_one,
      x_bind_of_step a b eIn eOut p₀ rest
        (x_step_backX_cons a b eIn eOut p₀ rest v temp pay S c inp dst L xt rt at' wit pre g),
      ih (c :: xt) v none pay S inp dst rt at' wit pre g]
    simp

/-- **Moving the witness component**, with an arbitrary scratch accumulator. -/
theorem x_rest (L : List Sym) :
    ∀ (scr : List Sym) (v : tm.σ) (temp : Option Sym)
      (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
      (dst xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)^[L.length + 1]
        (some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdRest)) v temp pay S L dst scr xt
          rt at' wit pre g))
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackW)) v none pay S [] dst
          (L.reverse ++ scr) xt rt at' wit pre g) := by
  induction L with
  | nil =>
    intro scr v temp pay S dst xt rt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      x_bind_of_step a b eIn eOut p₀ rest
        (x_step_rest_nil a b eIn eOut p₀ rest v temp pay S dst scr xt rt at' wit pre g)]
    simp
  | cons c L ih =>
    intro scr v temp pay S dst xt rt at' wit pre g
    change (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)^[(L.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)
        (L.length + 1) 1, Function.iterate_one,
      x_bind_of_step a b eIn eOut p₀ rest
        (x_step_rest_cons a b eIn eOut p₀ rest v temp pay S c L dst scr xt rt at' wit pre g),
      ih (c :: scr) v none pay S dst xt rt at' wit pre g]
    simp

/-- **Restoring the witness component**, with an arbitrary accumulator; its empty exit enters the
construction. -/
theorem x_backW (L : List Sym) :
    ∀ (wit : List Sym) (v : tm.σ) (temp : Option Sym)
      (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
      (inp dst xt rt at' pre : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)^[L.length + 1]
        (some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdBackW)) v temp pay S inp dst L xt
          rt at' wit pre g))
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwCopy)) v none pay S inp dst [] xt
          rt at' (L.reverse ++ wit) pre g) := by
  induction L with
  | nil =>
    intro wit v temp pay S inp dst xt rt at' pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      x_bind_of_step a b eIn eOut p₀ rest
        (x_step_backW_nil a b eIn eOut p₀ rest v temp pay S inp dst xt rt at' wit pre g)]
    simp
  | cons c L ih =>
    intro wit v temp pay S inp dst xt rt at' pre g
    change (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)^[(L.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)
        (L.length + 1) 1, Function.iterate_one,
      x_bind_of_step a b eIn eOut p₀ rest
        (x_step_backW_cons a b eIn eOut p₀ rest v temp pay S c inp dst L xt rt at' wit pre g),
      ih (c :: wit) v none pay S inp dst xt rt at' pre g]
    simp

/-- **Parsing the production pair encoding.**  From `pdSplit` with `encodePair (x, w)` on the call
input and every work stack empty, `2L + 2` steps reach `cwCopy` with the source input `ofBits x`
and the witness `ofBits w`, both **in order**, and the call input and scratch empty again. -/
theorem x_parse (x w : List Bool) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (dst rt at' pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)^[2 * (x.length + w.length + 1) + 2]
        (some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.pdSplit)) v temp pay S
          (encodePair (x, w)) dst [] [] rt at' [] pre g))
      = some (xCfg a b eIn eOut p₀ rest (some (.inr CallLabel.cwCopy)) v none pay S [] dst []
          (ofBits x) rt at' (ofBits w) pre g) := by
  have hsplit : 2 * (x.length + w.length + 1) + 2
      = (((ofBits w).reverse.length + 1) + ((ofBits w).length + 1))
        + (((ofBits x).reverse.length + 1) + (x.length + 1)) := by
    simp only [List.length_reverse, length_ofBits]; omega
  have h1 := x_split a b eIn eOut p₀ rest x (ofBits w) [] v temp pay S dst [] rt at' [] pre g
  have h2 := x_backX a b eIn eOut p₀ rest (ofBits x).reverse [] v none pay S (ofBits w) dst rt at'
    [] pre g
  have h3 := x_rest a b eIn eOut p₀ rest (ofBits w) [] v none pay S dst (ofBits x) rt at' [] pre g
  have h4 := x_backW a b eIn eOut p₀ rest (ofBits w).reverse [] v none pay S [] dst (ofBits x) rt
    at' pre g
  simp only [List.append_nil, List.reverse_reverse] at h1 h2 h3 h4
  rw [hsplit,
    Function.iterate_add_apply (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)
      (((ofBits w).reverse.length + 1) + ((ofBits w).length + 1))
      (((ofBits x).reverse.length + 1) + (x.length + 1)),
    Function.iterate_add_apply (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)
      ((ofBits x).reverse.length + 1) (x.length + 1),
    show encodePair (x, w) = ofBits x ++ Sym.sep :: ofBits w from rfl, h1, h2,
    Function.iterate_add_apply (flip Bind.bind (xTM a b eIn eOut p₀ rest).step)
      ((ofBits w).reverse.length + 1) ((ofBits w).length + 1), h3, h4]

end Steps

end


/-! ## The wrapper -/

section Wrapper

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- The initial payload: helper flag and result cleared, **full depth**, **aggregate `true`**. -/
def wrapP₀ (q : ℕ) {U₀ : Type} (u₀ : U₀) : Bool × (Bool × DepthPay q (Bool × U₀)) :=
  (false, (false, (Fin.last q, (true, u₀))))

/-- The checker's internal machine: every certificate runs on this one program. -/
noncomputable abbrev chkTM (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) : FinTM2 :=
  xTM a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) rest

/-- **The wrapper.**  The internal machine with its designated stacks and main label replaced:
external input on `CallSlot.input`, external output on `CallSlot.dst`, entry at the parser.  Every
other field — stack family, equality instance, labels, states, initial state and program — is the
internal machine's own. -/
noncomputable def wrapTM (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) : FinTM2 :=
  { chkTM hw a b q U₀ u₀ rest with
    k₀ := (Sum.inr (Sum.inl CallSlot.input) :
      hw.tm.K ⊕ (CallSlot ⊕ (TripleSlot ⊕ (LookupSlot ⊕ G))))
    k₁ := (Sum.inr (Sum.inl CallSlot.dst) :
      hw.tm.K ⊕ (CallSlot ⊕ (TripleSlot ⊕ (LookupSlot ⊕ G))))
    Γk₀Fin := inferInstanceAs (Fintype Sym)
    main := (Sum.inr CallLabel.pdSplit : hw.tm.Λ ⊕ CallLabel) }

/-- **The wrapper steps exactly as the internal machine does**: its designated stacks and main
label feed `initList` and `haltList`, never the transition function. -/
theorem wrapTM_step (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) :
    (wrapTM hw a b q U₀ u₀ rest).step = (chkTM hw a b q U₀ u₀ rest).step := rfl

/-- The external alphabets are `Sym` on both sides, so both maps are the identity. -/
def wrapIn (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) :
    (wrapTM hw a b q U₀ u₀ rest).Γ (wrapTM hw a b q U₀ u₀ rest).k₀ ≃ Sym := Equiv.refl Sym

def wrapOut (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) :
    (wrapTM hw a b q U₀ u₀ rest).Γ (wrapTM hw a b q U₀ u₀ rest).k₁ ≃ Sym := Equiv.refl Sym

/-- Encoding through the external input map changes nothing: it is the identity on `Sym`. -/
theorem wrapIn_map (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) (s : List Sym) :
    s.map (wrapIn hw a b q U₀ u₀ rest).invFun = s := by
  simp only [wrapIn]
  exact List.map_id s

/-- **The wrapper's own initial configuration**, named: the raw input on the call input, every
other stack empty — the callee's included — at the parser's entry, with the full initial control
state. -/
theorem wrapTM_initList (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) (s : List Sym) :
    initList (wrapTM hw a b q U₀ u₀ rest) s
      = xCfg a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) rest
          (some (.inr CallLabel.pdSplit)) hw.tm.initialState none (wrapP₀ q u₀) (fun _ => []) s []
          [] [] [] [] [] [] (fun _ => []) := by
  simp only [initList, xCfg, wCfg, enCfg, inCfg, clCfg, tuCfg, qCfg, prepCfg, callCfg]
  congr 1
  funext i
  -- The decidable-equality instance is the machine's own, so each case is split by hand: at the
  -- input stack the condition holds; everywhere else it fails by constructor disjointness.
  rcases i with k | cs | ts | ls | j'
  · split
    · rename_i h; cases h
    · rfl
  · cases cs
    · split
      · rfl
      · rename_i h; exact absurd rfl h
    all_goals split
    all_goals first | rfl | (rename_i h; cases h)
  · cases ts
    all_goals split
    all_goals first | rfl | (rename_i h; cases h)
  · cases ls
    all_goals split
    all_goals first | rfl | (rename_i h; cases h)
  · split
    · rename_i h; cases h
    · rfl

end Wrapper


/-! ## Construction, handoff and enumeration, composed; and the wrapper's run -/

section Run

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- The enumeration certificate, instantiated on the checker's one program at canonical width. -/
noncomputable abbrev chkEnum (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (g : ∀ j : G, List (Γg j)) (v : hw.tm.σ) (temp : Option Sym)
    (flag res : Bool) :=
  enumCert q U₀ hw (wrapP₀ q u₀)
    (cwRoute hw.tm G Γg (DepthPay q (Bool × U₀)) a b
      (wrapRoute hw.tm G Γg (DepthPay q (Bool × U₀)) rest))
    x w u₀ g (canonicalWidth a b x.length) (2 ^ canonicalWidth a b x.length - 1)
    ⟨0, Nat.two_pow_pos _⟩
    (by simp only; have := Nat.two_pow_pos (canonicalWidth a b x.length); omega) true v temp flag
    res

/-- **Construction, the counted handoff, and the whole enumeration, on one program.**

From `cwCopy` with the source input `ofBits x`, the witness `ofBits w`, full depth, aggregate
`true`, and every other storage empty, the machine reaches `enDone` holding exactly `checkAll`.  The
recorded count is the construction's, plus the one handoff step, plus the enumeration's own.  The
flag construction leaves `true` is accepted by the enumeration's entry as it stands. -/
theorem chk_construct_enum (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (g : ∀ j : G, List (Γg j)) (v : hw.tm.σ) (temp : Option Sym)
    (flag res : Bool) :
    (flip Bind.bind (chkTM hw a b q U₀ u₀ rest).step)^[
        cwSteps x.length + 1 + (chkEnum hw a b q U₀ u₀ rest x w g v none true res).steps]
        (some (xCfg a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) rest
          (some (.inr CallLabel.cwCopy)) v temp (flag, (res, (Fin.last q, (true, u₀))))
          (fun _ => []) [] [] [] (ofBits x) [] [] (ofBits w) [] g))
      = some (enStop q U₀ hw (wrapP₀ q u₀)
          (cwRoute hw.tm G Γg (DepthPay q (Bool × U₀)) a b
            (wrapRoute hw.tm G Γg (DepthPay q (Bool × U₀)) rest))
          x w u₀ g (canonicalWidth a b x.length)
          (checkAll (fun x r a => f (x, r, a)) q (canonicalWidth a b x.length) x w)
          (seedRes f q x w (canonicalWidth a b x.length) (2 ^ canonicalWidth a b x.length - 1))) :=
            by
  have hc : (flip Bind.bind (chkTM hw a b q U₀ u₀ rest).step)^[cwSteps x.length]
        (some (xCfg a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) rest
          (some (.inr CallLabel.cwCopy)) v temp (flag, (res, (Fin.last q, (true, u₀))))
          (fun _ => []) [] [] [] (ofBits x) [] [] (ofBits w) [] g))
      = some (xCfg a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) rest
          (some (.inr CallLabel.cwDone)) v none (true, (res, (Fin.last q, (true, u₀))))
          (fun _ => []) [] [] [] (ofBits x)
          (ofBits (bitsOfFin (canonicalWidth a b x.length) ⟨0, Nat.two_pow_pos _⟩)) []
          (ofBits w) [] g) :=
    (cwEvals a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀)
      (wrapRoute hw.tm G Γg (DepthPay q (Bool × U₀)) rest) x v temp flag res
      (Fin.last q, (true, u₀)) (fun _ => []) [] [] (ofBits w) [] g).evals_in_steps
  have he := enum_checkAll q U₀ hw (wrapP₀ q u₀)
    (cwRoute hw.tm G Γg (DepthPay q (Bool × U₀)) a b
      (wrapRoute hw.tm G Γg (DepthPay q (Bool × U₀)) rest))
    x w u₀ g (canonicalWidth a b x.length) v none true res
  have hsplit : cwSteps x.length + 1 + (chkEnum hw a b q U₀ u₀ rest x w g v none true res).steps
      = (chkEnum hw a b q U₀ u₀ rest x w g v none true res).steps + (1 + cwSteps x.length) := by
    omega
  rw [hsplit, Function.iterate_add_apply, Function.iterate_add_apply, hc, Function.iterate_one,
    x_bind_of_step a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) rest
      (x_step_handoff a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) rest v none
        (true, (res, (Fin.last q, (true, u₀)))) (fun _ => []) [] [] [] (ofBits x)
        (ofBits (bitsOfFin (canonicalWidth a b x.length) ⟨0, Nat.two_pow_pos _⟩)) [] (ofBits w) []
        g)]
  exact he

/-- Its bound, in the pair-encoding length `L`: `8L + 10` for construction and handoff, and the
enumeration's polynomial. -/
theorem chk_construct_enum_le (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) (g : ∀ j : G, List (Γg j)) (v : hw.tm.σ) (res : Bool) :
    cwSteps x.length + 1 + (chkEnum hw a b q U₀ u₀ rest x w g v none true res).steps
      ≤ (8 * (x.length + w.length + 1) + 10)
        + (enumPoly hw a b q).eval (x.length + w.length + 1) := by
  have h1 := cwSteps_le x.length
  have h2 : (chkEnum hw a b q U₀ u₀ rest x w g v none true res).steps
      ≤ (enumPoly hw a b q).eval (x.length + w.length + 1) :=
    enum_steps_le_poly q U₀ hw (wrapP₀ q u₀)
      (cwRoute hw.tm G Γg (DepthPay q (Bool × U₀)) a b
        (wrapRoute hw.tm G Γg (DepthPay q (Bool × U₀)) rest))
      x w u₀ g a b v none true res
  omega

/-- The wrapper's exact recorded count, up to `enDone`: parsing, construction, the handoff, and
the enumeration. -/
noncomputable def wrapSteps (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) : ℕ :=
  (2 * (x.length + w.length + 1) + 2) + (cwSteps x.length + 1
    + (chkEnum hw a b q U₀ u₀ rest x w (fun _ => []) hw.tm.initialState none true false).steps)

/-- **The wrapper runs from its own `initList`.**  On `encodePair (x, w)`, the wrapper's actual
initial configuration — its own main label, its own external input stack, its full initial control
state — reaches `enDone` holding exactly `checkAll`, in `wrapSteps` steps.  Parsing establishes
every precondition the construction and the enumeration need; full depth and the `true` aggregate
come from the initial state itself and are preserved, not re-initialised. -/
theorem wrap_run (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) :
    (flip Bind.bind (wrapTM hw a b q U₀ u₀ rest).step)^[wrapSteps hw a b q U₀ u₀ rest x w]
        (some (initList (wrapTM hw a b q U₀ u₀ rest) (encodePair (x, w))))
      = some (enStop q U₀ hw (wrapP₀ q u₀)
          (cwRoute hw.tm G Γg (DepthPay q (Bool × U₀)) a b
            (wrapRoute hw.tm G Γg (DepthPay q (Bool × U₀)) rest))
          x w u₀ (fun _ => []) (canonicalWidth a b x.length)
          (checkAll (fun x r a => f (x, r, a)) q (canonicalWidth a b x.length) x w)
          (seedRes f q x w (canonicalWidth a b x.length) (2 ^ canonicalWidth a b x.length - 1))) :=
            by
  have hp := x_parse a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) rest x w
    hw.tm.initialState none (wrapP₀ q u₀) (fun _ => []) [] [] [] [] (fun _ => [])
  have hall : (flip Bind.bind (chkTM hw a b q U₀ u₀ rest).step)^[wrapSteps hw a b q U₀ u₀ rest x w]
        (some (xCfg a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) rest
          (some (.inr CallLabel.pdSplit)) hw.tm.initialState none (wrapP₀ q u₀) (fun _ => [])
          (encodePair (x, w)) [] [] [] [] [] [] [] (fun _ => [])))
      = some (enStop q U₀ hw (wrapP₀ q u₀)
          (cwRoute hw.tm G Γg (DepthPay q (Bool × U₀)) a b
            (wrapRoute hw.tm G Γg (DepthPay q (Bool × U₀)) rest))
          x w u₀ (fun _ => []) (canonicalWidth a b x.length)
          (checkAll (fun x r a => f (x, r, a)) q (canonicalWidth a b x.length) x w)
          (seedRes f q x w (canonicalWidth a b x.length)
            (2 ^ canonicalWidth a b x.length - 1))) := by
    rw [wrapSteps, Nat.add_comm (2 * (x.length + w.length + 1) + 2), Function.iterate_add_apply,
      hp]
    exact chk_construct_enum hw a b q U₀ u₀ rest x w (fun _ => []) hw.tm.initialState none false
      false
  exact (congrArg (fun c => (flip Bind.bind (wrapTM hw a b q U₀ u₀ rest).step)^[
    wrapSteps hw a b q U₀ u₀ rest x w] (some c))
    (wrapTM_initList hw a b q U₀ u₀ rest (encodePair (x, w)))).trans hall

/-- **The wrapper's bound up to `enDone`**, in the pair-encoding length `L`. -/
theorem wrapSteps_le (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) :
    wrapSteps hw a b q U₀ u₀ rest x w
      ≤ (10 * (encodePair (x, w)).length + 12)
        + (enumPoly hw a b q).eval (encodePair (x, w)).length := by
  have h := chk_construct_enum_le hw a b q U₀ u₀ rest x w (fun _ => []) hw.tm.initialState false
  rw [length_encodePair]
  simp only [wrapSteps]
  omega

end Run

end PCP.Machine
