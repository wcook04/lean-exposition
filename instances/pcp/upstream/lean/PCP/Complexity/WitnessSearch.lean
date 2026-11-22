import PCP.Complexity.CounterDecr

/-!
# The witness search: its program, and one positive advance

The witness and the traversed-prefix stack are a further frame layer
(`G := LookupSlot ⊕ G'`), so the accepted counter theorems apply unchanged — they
preserve the whole frame, whatever it happens to contain.

## The payload is concrete

`Q` is instantiated to `Bool × R`: a **result bit** and the unrelated caller data.  The full payload
is therefore `Bool × (Bool × R)` — helper flag, result, rest — exactly as the helpers already see
it.  Making it concrete rather than a setter/getter pair is what lets "the result and the unrelated
data are preserved" be read straight off each statement.

## The loop

```text
lkMain  --witness empty-->  lkExhausted --> lkRestore
        --witness nonempty--> ztInit ... ztZero --> lkSelected --> lkRestore
                                     ... ztPos  --> dcInit ... dcDone --> lkMain
lkRestore --prefix empty--> lkDrain --counter empty--> lkDone
```

Every arrow above is one counted step of the actual program; none is folded into a neighbour.

## The advance, step by step

`lkMain` **peeks** at the witness to test exhaustion and jumps to the zero test.  At `ztPos` a
single counted jump enters the decrement.  At `dcDone` the advance **pops the witness head
again**: the two helpers clear the temporary along the way, so a value peeked before them is gone,
and nothing here relies on it.

## The gap between decrement and advance

After `dc_trace` the counter has decreased but the traversed prefix has *not* grown, so the search
invariant relating the two does not hold at `dcDone`.  It is re-established only by the advance that
follows, which is why `lk_advance` is stated end-to-end from `lkMain` back to `lkMain` rather than
as a chain of label-local claims.

## How the one-step lemmas are proved

A peek, a `goto` and a `load` leave the stack family untouched, so those lemmas are `rfl`.  The
ones that *write* — the advance, the prefix restoration and the counter drain — need the five-way
`rcases` on the stack index `tm.K ⊕ (CallSlot ⊕ (TripleSlot ⊕ (LookupSlot ⊕ G)))`, trying `rfl`
before `simp` in each branch.  A `pop` writes even on an empty stack (`[].tail = []`), so the two
empty-exit lemmas need it too.

## Counting

`1 + (2k + 3) + 1 + (2k + 3) + 1 = 4k + 9` for one positive advance, with every empty exit inside
that count.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-- The search's own two stacks. -/
inductive LookupSlot | witness | prefixStack
  deriving DecidableEq, Inhabited, Repr

instance : Fintype LookupSlot where
  elems := {LookupSlot.witness, LookupSlot.prefixStack}
  complete := by intro x; cases x <;> decide

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (R : Type) [Fintype R]

/-- `Sym` on the search's stacks, the caller's alphabets beyond them. -/
abbrev lkΓ : LookupSlot ⊕ G → Type
  | .inl _ => Sym
  | .inr j => Γg j

/-- The search frame. -/
def lkFrame (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    ∀ j : LookupSlot ⊕ G, List (lkΓ G Γg j)
  | .inl LookupSlot.witness => wit
  | .inl LookupSlot.prefixStack => pre
  | .inr j => g j

/-- The main loop: peek at the witness, and either run the zero test or report exhaustion. -/
def lkMainStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  peek (.inr (.inr (.inr (.inl LookupSlot.witness)))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .ztInit)))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .lkExhausted)))

/-- Exhaustion: the witness ran out before the address did.  Record `false` — every bit past the
end of a witness reads `false` through `oracleOfWitness` — clear the helper flag, and restore. -/
def lkExhaustedStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  load (fun p => (p.1, (none, (false, (false, p.2.2.2.2)))))
    (goto (fun _ => .inr .lkRestore))

/-- A zero counter: one counted jump into selection. -/
def lkZeroStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  goto (fun _ => .inr .lkSelected)

/-- A positive counter: one counted jump into the decrement. -/
def lkPosStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  goto (fun _ => .inr .dcInit)

/-- Selection: **peek** at the addressed symbol, so it stays on the witness stack for restoration
to find, record its bit, clear the helper flag, and restore.  The zero test cleared the temporary,
so this is a fresh read. -/
def lkSelectedStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  peek (.inr (.inr (.inr (.inl LookupSlot.witness)))) (fun p o => (p.1, (o, p.2.2))) <|
    load (fun p => (p.1, (none, (false, (symIsTrue p.2.1, p.2.2.2.2)))))
      (goto (fun _ => .inr .lkRestore))

/-- The advance: pop the witness head **afresh** onto the prefix stack, and loop. -/
def lkAdvanceStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inr (.inr (.inl LookupSlot.witness)))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inr (.inr (.inl LookupSlot.prefixStack)))) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .lkMain))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .lkMain)))

/-- Restoration: pop the traversed prefix back onto the witness, reversing it a second time — so
the witness ends up in its original order — then drain. -/
def lkRestoreStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inr (.inr (.inl LookupSlot.prefixStack)))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (push (.inr (.inr (.inr (.inl LookupSlot.witness)))) (fun p => p.2.1.getD Sym.sep)
        (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .lkRestore))))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .lkDrain)))

/-- The drain: discard whatever is left of the counter, emptying the destination stack. -/
def lkDrainStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  pop (.inr (.inl .dst)) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .lkDrain)))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .lkDone)))

/-- The search's own labels.  `lkDone` is the endpoint and is **not** claimed here: it dispatches
through `rest`, so reaching it active is the contract's end and its continuation has not run. -/
def lkRoute
    (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))
  | .lkMain => lkMainStmt tm G Γg R
  | .lkExhausted => lkExhaustedStmt tm G Γg R
  | .ztZero => lkZeroStmt tm G Γg R
  | .ztPos => lkPosStmt tm G Γg R
  | .lkSelected => lkSelectedStmt tm G Γg R
  | .dcDone => lkAdvanceStmt tm G Γg R
  | .lkRestore => lkRestoreStmt tm G Γg R
  | .lkDrain => lkDrainStmt tm G Γg R
  | l => rest l

/-- Everything: the two counter helpers over the search's labels. -/
def lookupRoute
    (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) :=
  counterRoute tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × R) (lkRoute tm G Γg R rest)

variable {tm G Γg R}

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : Bool × (Bool × R))
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)))

/-- The machine the search runs on: the call machine over the preparation frame, with the
witness layer nested inside it. -/
abbrev lkTM : FinTM2 :=
  callTM tm (TripleSlot ⊕ (LookupSlot ⊕ G)) (prepΓ (LookupSlot ⊕ G) (lkΓ G Γg))
    (Bool × (Bool × R)) eIn eOut p₀
    (prepCont tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × R)) (lookupRoute tm G Γg R rest))

/-- A configuration, with the witness and prefix stacks named. -/
def lkCfg (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × R)) (S : ∀ k, List (tm.Γ k)) (inp dst scr : List Sym)
    (t : TripleSlot → List Sym) (wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).Cfg :=
  prepCfg eIn eOut p₀ (lookupRoute tm G Γg R rest) l v temp pay S inp dst scr t
    (lkFrame G Γg wit pre g)

/-! ### The eleven one-step equations -/

/-- The loop head on a nonempty witness: the peek leaves it alone and the zero test begins. -/
theorem lk_step_main_cons (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (c : Sym)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkMain)) v temp (flag, (res, r)) S inp dst
          scr t (c :: wit) pre g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.ztInit)) v none (flag, (res, r)) S inp
          dst scr t (c :: wit) pre g) :=
  rfl

/-- The loop head on an empty witness: exhaustion, without touching the counter. -/
theorem lk_step_main_nil (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkMain)) v temp (flag, (res, r)) S inp dst
          scr t [] pre g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkExhausted)) v none (flag, (res, r))
          S inp dst scr t [] pre g) :=
  rfl

/-- Exhaustion records `false` and clears the helper flag. -/
theorem lk_step_exhausted (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkExhausted)) v temp (flag, (res, r)) S inp
          dst scr t wit pre g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkRestore)) v none (false, (false, r))
          S inp dst scr t wit pre g) :=
  rfl

/-- A zero counter: one counted jump into selection, touching nothing. -/
theorem lk_step_zero (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.ztZero)) v temp (flag, (res, r)) S inp dst
          scr t wit pre g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkSelected)) v temp (flag, (res, r)) S
          inp dst scr t wit pre g) :=
  rfl

/-- A positive counter: one counted jump into the decrement, touching nothing. -/
theorem lk_step_pos (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.ztPos)) v temp (flag, (res, r)) S inp dst
          scr t wit pre g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.dcInit)) v temp (flag, (res, r)) S inp
          dst scr t wit pre g) :=
  rfl

/-- Selection on a **bit** tape: the addressed bit is recorded and the symbol carrying it stays on
the witness stack.  Stated at `Sym.bit b :: wit`, not at an arbitrary symbol: the lookup contract
concerns a Boolean witness, so no default semantics for a malformed tape is invented here. -/
theorem lk_step_selected (v : tm.σ) (temp : Option Sym) (flag res b : Bool) (r : R)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkSelected)) v temp (flag, (res, r)) S inp
          dst scr t (Sym.bit b :: wit) pre g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkRestore)) v none (false, (b, r)) S
          inp dst scr t (Sym.bit b :: wit) pre g) :=
  rfl

/-- The advance: the witness head is popped **again** — the helpers cleared the temporary — and
moved onto the prefix stack. -/
theorem lk_step_advance (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (c : Sym)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.dcDone)) v temp (flag, (res, r)) S inp dst
          scr t (c :: wit) pre g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkMain)) v none (flag, (res, r)) S inp
          dst scr t wit (c :: pre) g) := by
  simp only [lkTM, callTM, parentTM, callProgram, prepCont, lookupRoute, counterRoute, ztRoute,
    dcRoute, lkRoute, lkAdvanceStmt, lkCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.lkMain), (v, (none, (flag, (res, r)))), T⟩ :
      (lkTM eIn eOut p₀ rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]

/-- Restoration, one symbol: the prefix head goes back onto the witness. -/
theorem lk_step_restore_cons (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (c : Sym)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkRestore)) v temp (flag, (res, r)) S inp
          dst scr t wit (c :: pre) g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkRestore)) v none (flag, (res, r)) S
          inp dst scr t (c :: wit) pre g) := by
  simp only [lkTM, callTM, parentTM, callProgram, prepCont, lookupRoute, counterRoute, ztRoute,
    dcRoute, lkRoute, lkRestoreStmt, lkCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.lkRestore), (v, (none, (flag, (res, r)))), T⟩ :
      (lkTM eIn eOut p₀ rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]

/-- Restoration's empty exit.  The `pop` writes even here — `[].tail = []` — so the endpoint is
still a stack update, and the case split is still needed. -/
theorem lk_step_restore_nil (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (wit : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkRestore)) v temp (flag, (res, r)) S inp
          dst scr t wit [] g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkDrain)) v none (flag, (res, r)) S
          inp dst scr t wit [] g) := by
  simp only [lkTM, callTM, parentTM, callProgram, prepCont, lookupRoute, counterRoute, ztRoute,
    dcRoute, lkRoute, lkRestoreStmt, lkCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.lkDrain), (v, (none, (flag, (res, r)))), T⟩ :
      (lkTM eIn eOut p₀ rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]

/-- The drain, one symbol. -/
theorem lk_step_drain_cons (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R) (c : Sym)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp dst scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkDrain)) v temp (flag, (res, r)) S inp
          (c :: dst) scr t wit pre g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkDrain)) v none (flag, (res, r)) S
          inp dst scr t wit pre g) := by
  simp only [lkTM, callTM, parentTM, callProgram, prepCont, lookupRoute, counterRoute, ztRoute,
    dcRoute, lkRoute, lkDrainStmt, lkCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.lkDrain), (v, (none, (flag, (res, r)))), T⟩ :
      (lkTM eIn eOut p₀ rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]

/-- The drain's empty exit: the search's completion boundary, reached **active**. -/
theorem lk_step_drain_nil (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym)
    (inp scr : List Sym) (g : ∀ j : G, List (Γg j)) :
    (lkTM eIn eOut p₀ rest).step
        (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkDrain)) v temp (flag, (res, r)) S inp []
          scr t wit pre g)
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkDone)) v none (flag, (res, r)) S
          inp [] scr t wit pre g) := by
  simp only [lkTM, callTM, parentTM, callProgram, prepCont, lookupRoute, counterRoute, ztRoute,
    dcRoute, lkRoute, lkDrainStmt, lkCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr CallLabel.lkDone), (v, (none, (flag, (res, r)))), T⟩ :
      (lkTM eIn eOut p₀ rest).Cfg)) ?_)
  funext i
  rcases i with k | cs | ts | ls | j'
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · cases cs <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · cases ls <;>
      first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]
  · first | rfl | simp [Function.update, embedStacks, callFrame, prepFrame, lkFrame]

/-! ### Composing: one step at the iteration level

`Function.iterate` sees `flip Bind.bind step`, and `Option.bind (some c) f` reduces to `f c`.  One
wrapper turns any of the eleven equations above into that form, so none of them needs a twin. -/

/-- Any one-step equation, restated where `Function.iterate` can use it. -/
theorem lk_bind_of_step {c c' : (lkTM eIn eOut p₀ rest).Cfg}
    (h : (lkTM eIn eOut p₀ rest).step c = some c') :
    (flip Bind.bind (lkTM eIn eOut p₀ rest).step) (some c) = some c' := h

/-! ### The two helper traces, in the search's own vocabulary

`lookupRoute` is by definition `ztRoute _ (dcRoute _ (lkRoute _ rest))`, so the accepted counter
traces apply verbatim; each restatement below is the accepted theorem, checked against the search's
configuration shape by definitional unfolding alone.
-/

/-- `zt_trace`, transported to the search machine.  The frame it preserves now contains the
witness and the traversed prefix. -/
theorem lk_zt_trace (bs : List Bool) (v : tm.σ) (temp : Option Sym) (seen res : Bool) (r : R)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (lkTM eIn eOut p₀ rest).step)^[2 * bs.length + 3]
        (some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.ztInit)) v temp (seen, (res, r)) S inp
          (ofBits bs) [] t wit pre g))
      = some (lkCfg eIn eOut p₀ rest (some (.inr
          (if bitsValue bs = 0 then CallLabel.ztZero else CallLabel.ztPos))) v none
          (decide (bitsValue bs ≠ 0), (res, r)) S inp (ofBits bs) [] t wit pre g) :=
  zt_trace (rest := dcRoute tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × R) (lkRoute tm G Γg R rest))
    eIn eOut p₀ bs v temp seen (res, r) S t inp (lkFrame G Γg wit pre g)

/-- `dc_trace`, transported to the search machine. -/
theorem lk_dc_trace (bs : List Bool) (v : tm.σ) (temp : Option Sym) (flag res : Bool) (r : R)
    (wit pre : List Sym) (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (lkTM eIn eOut p₀ rest).step)^[2 * bs.length + 3]
        (some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.dcInit)) v temp (flag, (res, r)) S inp
          (ofBits bs) [] t wit pre g))
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.dcDone)) v none
          (finalBorrow true bs, (res, r)) S inp (ofBits (decrBits bs)) [] t wit pre g) :=
  dc_trace (rest := lkRoute tm G Γg R rest)
    eIn eOut p₀ bs v temp flag (res, r) S t inp (lkFrame G Γg wit pre g)

/-! ### One complete positive advance -/

/-- **One positive advance of the search**, from the loop head back to the loop head.

The hypothesis is only that the counter is positive; the witness is nonempty because a head symbol
`c` is supplied.  Along the way the counter is *read* twice — once by the zero test, once by the
decrement — and the witness head is *read* twice: once by the peek at `lkMain`, which leaves it in
place, and once by the pop at `dcDone`.  The second read is a genuine re-read, not a reuse of the
first: `zt_trace` and `dc_trace` both end with the temporary cleared, so the peeked symbol is gone
by the time the advance runs.

The result bit and the unrelated data `r` are carried through untouched; only the helper flag, which
is the counter's own scratch, changes. -/
theorem lk_advance (bs : List Bool) (hpos : 0 < bitsValue bs) (v : tm.σ) (temp : Option Sym)
    (flag res : Bool) (r : R) (c : Sym) (wit pre : List Sym) (S : ∀ k, List (tm.Γ k))
    (t : TripleSlot → List Sym) (inp : List Sym) (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (lkTM eIn eOut p₀ rest).step)^[4 * bs.length + 9]
        (some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkMain)) v temp (flag, (res, r)) S inp
          (ofBits bs) [] t (c :: wit) pre g))
      = some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkMain)) v none
          (finalBorrow true bs, (res, r)) S inp (ofBits (decrBits bs)) [] t wit (c :: pre) g) := by
  have hne : bitsValue bs ≠ 0 := hpos.ne'
  have hsplit : 4 * bs.length + 9
      = 1 + ((2 * bs.length + 3) + (1 + ((2 * bs.length + 3) + 1))) := by omega
  rw [hsplit,
    Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step) 1
      ((2 * bs.length + 3) + (1 + ((2 * bs.length + 3) + 1))),
    Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step)
      (2 * bs.length + 3) (1 + ((2 * bs.length + 3) + 1)),
    Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step) 1
      ((2 * bs.length + 3) + 1),
    Function.iterate_add_apply (flip Bind.bind (lkTM eIn eOut p₀ rest).step)
      (2 * bs.length + 3) 1,
    Function.iterate_one,
    lk_bind_of_step eIn eOut p₀ rest
      (lk_step_main_cons eIn eOut p₀ rest v temp flag res r c wit pre S t inp (ofBits bs) [] g),
    lk_zt_trace eIn eOut p₀ rest bs v none flag res r (c :: wit) pre S t inp g,
    ite_eq_right hne, decide_eq_true hne,
    lk_bind_of_step eIn eOut p₀ rest
      (lk_step_pos eIn eOut p₀ rest v none true res r (c :: wit) pre S t inp (ofBits bs) [] g),
    lk_dc_trace eIn eOut p₀ rest bs v none true res r (c :: wit) pre S t inp g,
    lk_bind_of_step eIn eOut p₀ rest
      (lk_step_advance eIn eOut p₀ rest v none (finalBorrow true bs) res r c wit pre S t inp
        (ofBits (decrBits bs)) [] g)]

/-- The advance certificate, with its count written out. -/
def lkAdvanceEvals (bs : List Bool) (hpos : 0 < bitsValue bs) (v : tm.σ) (temp : Option Sym)
    (flag res : Bool) (r : R) (c : Sym) (wit pre : List Sym) (S : ∀ k, List (tm.Γ k))
    (t : TripleSlot → List Sym) (inp : List Sym) (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (lkTM eIn eOut p₀ rest).step
      (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkMain)) v temp (flag, (res, r)) S inp
        (ofBits bs) [] t (c :: wit) pre g)
      (some (lkCfg eIn eOut p₀ rest (some (.inr CallLabel.lkMain)) v none
        (finalBorrow true bs, (res, r)) S inp (ofBits (decrBits bs)) [] t wit (c :: pre) g))
      (4 * bs.length + 9) where
  steps := 4 * bs.length + 9
  evals_in_steps := lk_advance eIn eOut p₀ rest bs hpos v temp flag res r c wit pre S t inp g
  steps_le_m := le_refl _

@[simp] theorem lkAdvanceEvals_steps (bs : List Bool) (hpos : 0 < bitsValue bs) (v : tm.σ)
    (temp : Option Sym) (flag res : Bool) (r : R) (c : Sym) (wit pre : List Sym)
    (S : ∀ k, List (tm.Γ k)) (t : TripleSlot → List Sym) (inp : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (lkAdvanceEvals eIn eOut p₀ rest bs hpos v temp flag res r c wit pre S t inp g).steps
      = 4 * bs.length + 9 := rfl

end Steps

/-! ### The search invariant across one advance

Two different things are called "the prefix", and keeping them apart is the point of this section.
`done` is the traversed part of the witness **in the witness's own order**; the prefix *stack* holds
`done.reverse`, because the advance pushes onto it.  One advance turns `done` into `done ++ [c]` and
the stack from `done.reverse` into `c :: done.reverse`.  A length-only statement cannot see that
difference, so both equations are proved here. -/

/-- **The invariant between decrement and advance, stated rather than assumed.**

Write `cs` for the counter *entering* the advance and `decrBits cs` for the one leaving it.  The
incoming equation `bitsValue cs + done.length = N` stays true — a number does not change because the
machine moved on — but at `dcDone` it no longer describes the tape: the physical counter is
`decrBits cs`, and with the traversed prefix still `done` the physical reading is
`bitsValue (decrBits cs) + done.length = N - 1`.  It is the advance's push of `c` that makes the
equation describe the tape again.

The three conclusions are the three things the loop needs: the budget still adds up, the counter
keeps its width, so the next zero test scans the same number of cells, and the physical stack is
the reversal of the traversed prefix. -/
theorem lk_advance_invariant {cs : List Bool} {N : ℕ} (hpos : 0 < bitsValue cs)
    (done : List Sym) (c : Sym) (hinv : bitsValue cs + done.length = N) :
    bitsValue (decrBits cs) + (done ++ [c]).length = N
      ∧ (decrBits cs).length = cs.length
      ∧ (done ++ [c]).reverse = c :: done.reverse := by
  refine ⟨?_, length_decrBits cs, by simp⟩
  have hv : bitsValue (decrBits cs) = bitsValue cs - 1 := bitsValue_decrBits cs hpos
  simp only [List.length_append, List.length_cons, List.length_nil, hv]
  omega

/-- The ordered decomposition the advance maintains: the witness is `done ++ remaining`, and moving
one symbol across keeps that shape with the head transferred. -/
theorem lk_advance_decomp (done remaining : List Sym) (c : Sym) :
    done ++ c :: remaining = (done ++ [c]) ++ remaining := by simp


end

end PCP.Machine
