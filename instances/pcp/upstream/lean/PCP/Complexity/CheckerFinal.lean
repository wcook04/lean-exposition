import PCP.Complexity.CheckerWrap

/-!
# The checker's finalisation, and the polynomial-time witness

## The route

```text
enDone ──store the aggregate, 1──→ fnX ──|x|+1──→ fnR ──k+1──→ fnW ──|w|+1──→ halted
```

At `enDone` the **aggregate** — not the last seed's result bit, a different field — is pushed onto
the designated output stack, which is empty there.  The three drains empty the source input, the
wrapped seed tape and the witness; every other stack is already empty by the enumeration's own
endpoint.  The last empty exit loads the wrapper's full initial control state — a constant, so the
program refers to no machine that contains it — and halts, in the same statement.  The output was
stored before the reset: the initial aggregate is `true` whatever was just computed.

`1 + (n + 1) + (k + 1) + (W + 1) = n + k + W + 4` steps.

## The endpoint

Exactly `haltList` of the wrapper on `encodeBool aggregate`, through the actual output map: label
`none`, the whole control state the wrapper's `initialState`, every non-output stack empty.  One
further step would be outer `none`; the certificate stops at the halting configuration.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition Polynomial

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (q : ℕ) (U₀ : Type) [Fintype U₀]

/-- Store the **aggregate** — the running conjunction, not the last result — on the output stack. -/
def fnStoreStmt :
    PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × DepthPay q (Bool × U₀))) :=
  push (.inr (.inl CallSlot.dst)) (fun p => Sym.bit p.2.2.2.2.2.1) (goto (fun _ => .inr .fnX))

/-- Drain the source input. -/
def fnXStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × DepthPay q (Bool × U₀))) :=
  pop (.inr (.inr (.inl TripleSlot.xs))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .fnX)))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .fnR)))

/-- Drain the seed tape. -/
def fnRStmt : PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × DepthPay q (Bool × U₀))) :=
  pop (.inr (.inr (.inl TripleSlot.rs))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .fnR)))
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .fnW)))

/-- Drain the witness; the empty exit resets the whole control state to the constant `pInit` and
halts, in one statement. -/
def fnWStmt (pInit : Bool × (Bool × DepthPay q (Bool × U₀))) :
    PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × DepthPay q (Bool × U₀))) :=
  pop (.inr (.inr (.inr (.inl LookupSlot.witness)))) (fun p o => (p.1, (o, p.2.2))) <|
    branch (fun p => p.2.1.isSome)
      (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .fnW)))
      (load (fun _ => (tm.initialState, (none, pInit))) halt)

/-- The finalisation's labels. -/
def finRoute (pInit : Bool × (Bool × DepthPay q (Bool × U₀)))
    (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) :
    CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg) (Bool × (Bool × DepthPay q (Bool × U₀)))
  | .enDone => fnStoreStmt tm G Γg q U₀
  | .fnX => fnXStmt tm G Γg q U₀
  | .fnR => fnRStmt tm G Γg q U₀
  | .fnW => fnWStmt tm G Γg q U₀ pInit
  | l => rest l

variable {tm G Γg q U₀}

section Steps

variable (a b : ℕ) (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym)
  (p₀ pInit : Bool × (Bool × DepthPay q (Bool × U₀)))
  (rest : CallLabel → PrepStmt tm (LookupSlot ⊕ G) (lkΓ G Γg)
    (Bool × (Bool × DepthPay q (Bool × U₀))))

/-- The whole program, finalisation included. -/
abbrev fTM : FinTM2 := xTM a b eIn eOut p₀ (finRoute tm G Γg q U₀ pInit rest)

/-- A configuration of it. -/
def fCfg (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp dst scr xt rt at' wit pre : List Sym) (g : ∀ j : G, List (Γg j)) :
    (fTM a b eIn eOut p₀ pInit rest).Cfg :=
  xCfg a b eIn eOut p₀ (finRoute tm G Γg q U₀ pInit rest) l v temp pay S inp dst scr xt rt at'
    wit pre g

theorem f_bind_of_step {c c' : (fTM a b eIn eOut p₀ pInit rest).Cfg}
    (h : (fTM a b eIn eOut p₀ pInit rest).step c = some c') :
    (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step) (some c) = some c' := h

/-! ### The one-step equations -/

/-- **The store**: the aggregate `A` — not the last result `res` — onto the output stack. -/
theorem f_step_store (v : tm.σ) (temp : Option Sym) (flag res : Bool) (dep : Fin (q + 1))
    (A : Bool) (u₀ : U₀)
    (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (fTM a b eIn eOut p₀ pInit rest).step
        (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.enDone)) v temp
          (flag, (res, (dep, (A, u₀)))) S
          inp dst scr xt rt at' wit pre g)
      = some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnX)) v temp
          (flag, (res, (dep, (A, u₀)))) S
          inp (Sym.bit A :: dst) scr xt rt at' wit pre g) := by
  simp only [fTM, xTM, wTM, eTM, iTM, cTM, aTM, qTM, fCfg, xCfg, wCfg, enCfg, inCfg,
    clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute,
    handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute,
    incRoute, enumRoute, cwRoute, wrapRoute, finRoute, fnStoreStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨(some (.inr CallLabel.fnX)), (v, (temp, (flag, (res, (dep, (A, u₀)))))), T⟩ :
      (fTM a b eIn eOut p₀ pInit rest).Cfg)) ?_)
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

/-- Draining the source input, one symbol. -/
theorem f_step_x_cons (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k)) (c : Sym)
    (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (fTM a b eIn eOut p₀ pInit rest).step
        (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnX)) v temp pay S
          inp dst scr (c :: xt) rt at' wit pre g)
      = some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnX)) v none pay S
          inp dst scr xt rt at' wit pre g) := by
  simp only [fTM, xTM, wTM, eTM, iTM, cTM, aTM, qTM, fCfg, xCfg, wCfg, enCfg, inCfg,
    clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute,
    handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute,
    incRoute, enumRoute, cwRoute, wrapRoute, finRoute, fnXStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨(some (.inr CallLabel.fnX)), (v, (none, pay)), T⟩ : (fTM a b eIn eOut p₀ pInit rest).Cfg)) ?_)
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

/-- Draining the source input, the empty exit. -/
theorem f_step_x_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp dst scr rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (fTM a b eIn eOut p₀ pInit rest).step
        (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnX)) v temp pay S
          inp dst scr [] rt at' wit pre g)
      = some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnR)) v none pay S
          inp dst scr [] rt at' wit pre g) := by
  simp only [fTM, xTM, wTM, eTM, iTM, cTM, aTM, qTM, fCfg, xCfg, wCfg, enCfg, inCfg,
    clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute,
    handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute,
    incRoute, enumRoute, cwRoute, wrapRoute, finRoute, fnXStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨(some (.inr CallLabel.fnR)), (v, (none, pay)), T⟩ : (fTM a b eIn eOut p₀ pInit rest).Cfg)) ?_)
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

/-- Draining the seed tape, one symbol. -/
theorem f_step_r_cons (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k)) (c : Sym)
    (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (fTM a b eIn eOut p₀ pInit rest).step
        (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnR)) v temp pay S
          inp dst scr xt (c :: rt) at' wit pre g)
      = some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnR)) v none pay S
          inp dst scr xt rt at' wit pre g) := by
  simp only [fTM, xTM, wTM, eTM, iTM, cTM, aTM, qTM, fCfg, xCfg, wCfg, enCfg, inCfg,
    clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute,
    handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute,
    incRoute, enumRoute, cwRoute, wrapRoute, finRoute, fnRStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨(some (.inr CallLabel.fnR)), (v, (none, pay)), T⟩ : (fTM a b eIn eOut p₀ pInit rest).Cfg)) ?_)
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

/-- Draining the seed tape, the empty exit. -/
theorem f_step_r_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp dst scr xt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (fTM a b eIn eOut p₀ pInit rest).step
        (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnR)) v temp pay S
          inp dst scr xt [] at' wit pre g)
      = some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnW)) v none pay S
          inp dst scr xt [] at' wit pre g) := by
  simp only [fTM, xTM, wTM, eTM, iTM, cTM, aTM, qTM, fCfg, xCfg, wCfg, enCfg, inCfg,
    clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute,
    handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute,
    incRoute, enumRoute, cwRoute, wrapRoute, finRoute, fnRStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨(some (.inr CallLabel.fnW)), (v, (none, pay)), T⟩ : (fTM a b eIn eOut p₀ pInit rest).Cfg)) ?_)
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

/-- Draining the witness, one symbol. -/
theorem f_step_w_cons (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k)) (c : Sym)
    (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (fTM a b eIn eOut p₀ pInit rest).step
        (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnW)) v temp pay S
          inp dst scr xt rt at' (c :: wit) pre g)
      = some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnW)) v none pay S
          inp dst scr xt rt at' wit pre g) := by
  simp only [fTM, xTM, wTM, eTM, iTM, cTM, aTM, qTM, fCfg, xCfg, wCfg, enCfg, inCfg,
    clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute,
    handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute,
    incRoute, enumRoute, cwRoute, wrapRoute, finRoute, fnWStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨(some (.inr CallLabel.fnW)), (v, (none, pay)), T⟩ : (fTM a b eIn eOut p₀ pInit rest).Cfg)) ?_)
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

/-- **The last empty exit**: the whole control state reset to the constant, and halt — one
statement. -/
theorem f_step_w_nil (v : tm.σ) (temp : Option Sym)
    (pay : Bool × (Bool × DepthPay q (Bool × U₀))) (S : ∀ k, List (tm.Γ k))
    (inp dst scr xt rt at' pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (fTM a b eIn eOut p₀ pInit rest).step
        (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnW)) v temp pay S
          inp dst scr xt rt at' [] pre g)
      = some (fCfg a b eIn eOut p₀ pInit rest none tm.initialState none pInit S
          inp dst scr xt rt at' [] pre g) := by
  simp only [fTM, xTM, wTM, eTM, iTM, cTM, aTM, qTM, fCfg, xCfg, wCfg, enCfg, inCfg,
    clCfg, tuCfg, qCfg, callTM, parentTM, callProgram, prepCont, queryRoute, dispatchRoute,
    handoffRoute, lookupRoute, counterRoute, ztRoute, dcRoute, lkRoute, turnRoute, cleanRoute,
    incRoute, enumRoute, cwRoute, wrapRoute, finRoute, fnWStmt, prepCfg]
  refine congrArg some (congrArg (fun T =>
    (⟨none, (tm.initialState, (none, pInit)), T⟩ : (fTM a b eIn eOut p₀ pInit rest).Cfg)) ?_)
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


/-! ### The drains -/

/-- Draining the source input, on arbitrary list data. -/
theorem f_drainX (L : List Sym) :
    ∀ (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
      (S : ∀ k, List (tm.Γ k)) (inp dst scr rt at' wit pre : List Sym)
      (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)^[L.length + 1]
        (some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnX)) v temp pay S inp dst scr
          L rt at' wit pre g))
      = some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnR)) v none pay S inp dst scr
          [] rt at' wit pre g) := by
  induction L with
  | nil =>
    intro v temp pay S inp dst scr rt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      f_bind_of_step a b eIn eOut p₀ pInit rest
        (f_step_x_nil a b eIn eOut p₀ pInit rest v temp pay S inp dst scr rt at' wit pre g)]
  | cons c L ih =>
    intro v temp pay S inp dst scr rt at' wit pre g
    change (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)^[(L.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)
        (L.length + 1) 1, Function.iterate_one,
      f_bind_of_step a b eIn eOut p₀ pInit rest
        (f_step_x_cons a b eIn eOut p₀ pInit rest v temp pay S c inp dst scr L rt at' wit pre g),
      ih v none pay S inp dst scr rt at' wit pre g]

/-- Draining the seed tape, on arbitrary list data. -/
theorem f_drainR (L : List Sym) :
    ∀ (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
      (S : ∀ k, List (tm.Γ k)) (inp dst scr xt at' wit pre : List Sym)
      (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)^[L.length + 1]
        (some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnR)) v temp pay S inp dst scr
          xt L at' wit pre g))
      = some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnW)) v none pay S inp dst scr
          xt [] at' wit pre g) := by
  induction L with
  | nil =>
    intro v temp pay S inp dst scr xt at' wit pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      f_bind_of_step a b eIn eOut p₀ pInit rest
        (f_step_r_nil a b eIn eOut p₀ pInit rest v temp pay S inp dst scr xt at' wit pre g)]
  | cons c L ih =>
    intro v temp pay S inp dst scr xt at' wit pre g
    change (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)^[(L.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)
        (L.length + 1) 1, Function.iterate_one,
      f_bind_of_step a b eIn eOut p₀ pInit rest
        (f_step_r_cons a b eIn eOut p₀ pInit rest v temp pay S c inp dst scr xt L at' wit pre g),
      ih v none pay S inp dst scr xt at' wit pre g]

/-- Draining the witness, on arbitrary list data, to the halted, reset configuration. -/
theorem f_drainW (L : List Sym) :
    ∀ (v : tm.σ) (temp : Option Sym) (pay : Bool × (Bool × DepthPay q (Bool × U₀)))
      (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' pre : List Sym)
      (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)^[L.length + 1]
        (some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.fnW)) v temp pay S inp dst scr
          xt rt at' L pre g))
      = some (fCfg a b eIn eOut p₀ pInit rest none tm.initialState none pInit S inp dst scr xt rt
          at' [] pre g) := by
  induction L with
  | nil =>
    intro v temp pay S inp dst scr xt rt at' pre g
    rw [List.length_nil, Nat.zero_add, Function.iterate_one,
      f_bind_of_step a b eIn eOut p₀ pInit rest
        (f_step_w_nil a b eIn eOut p₀ pInit rest v temp pay S inp dst scr xt rt at' pre g)]
  | cons c L ih =>
    intro v temp pay S inp dst scr xt rt at' pre g
    change (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)^[(L.length + 1) + 1] _ = _
    rw [Function.iterate_add_apply (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)
        (L.length + 1) 1, Function.iterate_one,
      f_bind_of_step a b eIn eOut p₀ pInit rest
        (f_step_w_cons a b eIn eOut p₀ pInit rest v temp pay S c inp dst scr xt rt at' L pre g),
      ih v none pay S inp dst scr xt rt at' pre g]

/-- The finalisation's exact cost. -/
def finSteps (n k W : ℕ) : ℕ := 1 + (n + 1) + (k + 1) + (W + 1)

/-- **Finalisation.**  From `enDone`: the aggregate stored on the output stack, the source input,
seed and witness drained, the whole control state reset to the constant, halted.  Stated for
arbitrary tapes, flags, last result and aggregate — the two Booleans are independent here. -/
theorem f_trace (v : tm.σ) (temp : Option Sym) (flag res : Bool) (dep : Fin (q + 1)) (A : Bool)
    (u₀ : U₀) (S : ∀ k, List (tm.Γ k)) (inp dst scr xt rt at' wit pre : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)^[finSteps xt.length rt.length wit.length]
        (some (fCfg a b eIn eOut p₀ pInit rest (some (.inr CallLabel.enDone)) v temp
          (flag, (res, (dep, (A, u₀)))) S inp dst scr xt rt at' wit pre g))
      = some (fCfg a b eIn eOut p₀ pInit rest none tm.initialState none pInit S inp
          (Sym.bit A :: dst) scr [] [] at' [] pre g) := by
  have hsplit : finSteps xt.length rt.length wit.length
      = (wit.length + 1) + ((rt.length + 1) + ((xt.length + 1) + 1)) := by
    simp only [finSteps]; omega
  rw [hsplit,
    Function.iterate_add_apply (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)
      (wit.length + 1) ((rt.length + 1) + ((xt.length + 1) + 1)),
    Function.iterate_add_apply (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)
      (rt.length + 1) ((xt.length + 1) + 1),
    Function.iterate_add_apply (flip Bind.bind (fTM a b eIn eOut p₀ pInit rest).step)
      (xt.length + 1) 1,
    Function.iterate_one,
    f_bind_of_step a b eIn eOut p₀ pInit rest
      (f_step_store a b eIn eOut p₀ pInit rest v temp flag res dep A u₀ S inp dst scr xt rt at' wit
        pre g),
    f_drainX a b eIn eOut p₀ pInit rest xt v temp (flag, (res, (dep, (A, u₀)))) S inp
      (Sym.bit A :: dst) scr rt at' wit pre g,
    f_drainR a b eIn eOut p₀ pInit rest rt v none (flag, (res, (dep, (A, u₀)))) S inp
      (Sym.bit A :: dst) scr [] at' wit pre g,
    f_drainW a b eIn eOut p₀ pInit rest wit v none (flag, (res, (dep, (A, u₀)))) S inp
      (Sym.bit A :: dst) scr [] [] at' pre g]

end Steps

end


/-! ## The whole checker -/

section Whole

variable {G : Type} [DecidableEq G] [Fintype G] {Γg : G → Type}
  {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- The wrapper's own `haltList`, named: the output on `CallSlot.dst`, every other stack empty —
the callee's included — label `none`, the full initial control state. -/
theorem wrapTM_haltList (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) (s : List Sym) :
    haltList (wrapTM hw a b q U₀ u₀ rest) s
      = xCfg a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) rest none hw.tm.initialState none
          (wrapP₀ q u₀) (fun _ => []) [] s [] [] [] [] [] [] (fun _ => []) := by
  simp only [haltList, xCfg, wCfg, enCfg, inCfg, clCfg, tuCfg, qCfg, prepCfg, callCfg]
  congr 1
  funext i
  -- As for `initList`: the machine's own decidable-equality instance, so each case is split by
  -- hand.
  rcases i with k | cs | ts | ls | j'
  · split
    · rename_i h; cases h
    · rfl
  · cases cs
    · split
      · rename_i h; cases h
      · rfl
    · split
      · rfl
      · rename_i h; exact absurd rfl h
    · split
      · rename_i h; cases h
      · rfl
  · cases ts
    all_goals split
    all_goals first | rfl | (rename_i h; cases h)
  · cases ls
    all_goals split
    all_goals first | rfl | (rename_i h; cases h)
  · split
    · rename_i h; cases h
    · rfl

/-- Decoding through the external output map changes nothing: it is the identity on `Sym`. -/
theorem wrapOut_map (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) (s : List Sym) :
    s.map (wrapOut hw a b q U₀ u₀ rest).invFun = s := by
  simp only [wrapOut]
  exact List.map_id s

/-- The checker's continuation below the wrapper's own labels: finalisation, resetting to the
wrapper's initial payload. -/
abbrev chkRest (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f) (q : ℕ) (U₀ : Type)
    [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀)))) :=
  finRoute hw.tm G Γg q U₀ (wrapP₀ q u₀) rest

/-- The whole run's exact recorded count. -/
noncomputable def checkerSteps (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) : ℕ :=
  wrapSteps hw a b q U₀ u₀ (chkRest hw q U₀ u₀ rest) x w
    + finSteps x.length (canonicalWidth a b x.length) w.length

/-- **The whole checker, `initList` to `haltList`.**  On `encodePair (x, w)`, the wrapper — built
on the program that already contains finalisation — halts with exactly
`encodeBool (checkAll …)` on its output stack, every other stack empty, and its full initial
control state restored. -/
theorem final_run (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) :
    (flip Bind.bind (wrapTM hw a b q U₀ u₀ (chkRest hw q U₀ u₀ rest)).step)^[
        checkerSteps hw a b q U₀ u₀ rest x w]
        (some (initList (wrapTM hw a b q U₀ u₀ (chkRest hw q U₀ u₀ rest)) (encodePair (x, w))))
      = some (haltList (wrapTM hw a b q U₀ u₀ (chkRest hw q U₀ u₀ rest))
          (encodeBool
            (checkAll (fun x r a => f (x, r, a)) q (canonicalWidth a b x.length) x w))) := by
  have h1 := wrap_run hw a b q U₀ u₀ (chkRest hw q U₀ u₀ rest) x w
  have h2 := f_trace a b hw.inputAlphabet hw.outputAlphabet (wrapP₀ q u₀) (wrapP₀ q u₀) rest
    hw.tm.initialState none true
    (seedRes f q x w (canonicalWidth a b x.length) (2 ^ canonicalWidth a b x.length - 1))
    (Fin.last q) (checkAll (fun x r a => f (x, r, a)) q (canonicalWidth a b x.length) x w) u₀
    (fun _ => []) [] [] [] (ofBits x)
    (ofBits (bitsOfFin (canonicalWidth a b x.length) ⟨0, Nat.two_pow_pos _⟩)) [] (ofBits w) []
    (fun _ => [])
  simp only [length_ofBits, length_bitsOfFin] at h2
  rw [checkerSteps, Nat.add_comm, Function.iterate_add_apply, h1,
    wrapTM_haltList hw a b q U₀ u₀ (chkRest hw q U₀ u₀ rest)]
  exact h2

/-- The whole checker's polynomial, in the pair-encoding length. -/
noncomputable def checkerPoly (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) : Polynomial ℕ :=
  enumPoly hw a b q + 11 * X + widthPoly a b + 15

/-- **The whole run's recorded count is polynomial in the encoded pair's length.** -/
theorem checkerSteps_le (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) (U₀ : Type) [Fintype U₀] (u₀ : U₀)
    (rest : CallLabel → PrepStmt hw.tm (LookupSlot ⊕ G) (lkΓ G Γg)
      (Bool × (Bool × DepthPay q (Bool × U₀))))
    (x w : List Bool) :
    checkerSteps hw a b q U₀ u₀ rest x w
      ≤ (checkerPoly hw a b q).eval (encodePair (x, w)).length := by
  have h1 := wrapSteps_le hw a b q U₀ u₀ (chkRest hw q U₀ u₀ rest) x w
  have hL : (encodePair (x, w)).length = x.length + w.length + 1 := length_encodePair (x, w)
  have hk : canonicalWidth a b x.length ≤ (widthPoly a b).eval (encodePair (x, w)).length := by
    rw [widthPoly_eval]
    have h₁ := canonicalWidth_le a b x.length
    have h₂ : a * (x.length + 2) ≤ a * ((encodePair (x, w)).length + 2) :=
      Nat.mul_le_mul_left a (by omega)
    omega
  have hpoly : (checkerPoly hw a b q).eval (encodePair (x, w)).length
      = (enumPoly hw a b q).eval (encodePair (x, w)).length + 11 * (encodePair (x, w)).length
        + (widthPoly a b).eval (encodePair (x, w)).length + 15 := by
    simp [checkerPoly]
  rw [hpoly]
  simp only [checkerSteps, finSteps]
  omega

end Whole

/-! ## The polynomial-time witness -/

section Witness

variable {f : List Bool × List Bool × List Bool → Bool ⊕ ℕ}

/-- The fallback below finalisation: nothing is ever routed there on a well-formed run. -/
noncomputable def chkFallback (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f) (q : ℕ) :
    CallLabel → PrepStmt hw.tm (LookupSlot ⊕ Empty) (lkΓ Empty (fun _ => Sym))
      (Bool × (Bool × DepthPay q (Bool × Unit))) := fun _ => .halt

/-- **The checker as a polynomial-time machine**, for the production encoders `encodePair` and
`encodeBool`, with the empty outer frame and unit caller data.  Its machine, alphabet maps and
polynomial are the actual ones; each certificate records the actual count. -/
noncomputable def checkerWitness (hw : TM2ComputableInPolyTime encodeTriple encodeAnswer f)
    (a b q : ℕ) :
    TM2ComputableInPolyTime encodePair encodeBool
      (fun p : List Bool × List Bool =>
        checkAll (fun x r h => f (x, r, h)) q (canonicalWidth a b p.1.length) p.1 p.2) where
  tm := wrapTM hw a b q Unit () (chkRest hw q Unit () (chkFallback hw q))
  inputAlphabet := wrapIn hw a b q Unit () (chkRest hw q Unit () (chkFallback hw q))
  outputAlphabet := wrapOut hw a b q Unit () (chkRest hw q Unit () (chkFallback hw q))
  time := checkerPoly hw a b q
  outputsFun p :=
    { steps := checkerSteps hw a b q Unit () (chkFallback hw q) p.1 p.2
      evals_in_steps := by
        rw [wrapIn_map, wrapOut_map]
        exact final_run hw a b q Unit () (chkFallback hw q) p.1 p.2
      steps_le_m := checkerSteps_le hw a b q Unit () (chkFallback hw q) p.1 p.2 }

end Witness

end PCP.Machine
