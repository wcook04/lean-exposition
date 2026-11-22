import PCP.Complexity.CodeCfg
import PCP.Complexity.BoundedEval

/-!
# The coded statement evaluator and the transition square

## D1: why the callbacks need tables

`C.readHead` returns an `Option (Option ℕ)`, whose successful payload is an `Option ℕ` — `none` for
an empty stack, `some n` for a head code.  Those payload values satisfy a range bound, but the
*type* `Fin C.stateCount × Option ℕ` is infinite, so `Primrec.dom_finite` cannot be applied to a
callback on it.  The fix is the pattern `outputDecode` already uses: build a finite lookup table
indexed by symbol ordinal, and read it with `List.getElem?`, which includes the range check.  This
also avoids claiming anything about the computability of `C.decodeSymbol`, whose codomain is an
arbitrary source type.  (Primitive recursiveness is all that is claimed; no running time for
numerical table lookup is estimated anywhere here.)

The split into `emptyState` and `symbolStates` is one workable design, not the only one: a single
table with `C.size k + 1` entries — slot `0` for the empty-stack callback, slot `n + 1` for symbol
ordinal `n` — would also be defined on an empty alphabet, since `Option Empty` still has its `none`.
What an empty alphabet *does* rule out is any design that manufactures a default symbol.  The split
handles that case without needing one.

The remaining callbacks — push, load, branch, goto — all have domain `tm.σ`, which *is* finite, so
`dom_finite` applies to them directly.

## D2-D3: what the evaluator must keep apart

Executing the source `halt` statement returns a **successful** configuration whose label is `none`,
with the state and stacks left exactly as `halt` found them.  Stepping a configuration that is
*already* terminal returns outer `none`.  These are different, and `codeStep` distinguishes them, as
`Turing.TM2.step` does.  A machine gets its cleanup from the program that ran, never from the
interpreter.

The outer `Option` on `codeStmt` is the interpreter's error channel — an out-of-range head code.
`codeStmt_encode` shows it is never used on an encoded configuration.
-/

namespace PCP.Machine

open Turing Turing.TM2

variable {tm : FinTM2}

/-! ## D1. Numerical adapters for the source callbacks -/

/-- Indexing a finite table built over `List.finRange` always succeeds. -/
theorem getElem?_map_finRange {α : Type*} {n : ℕ} (g : Fin n → α) (i : Fin n) :
    ((List.finRange n).map g)[(i : ℕ)]? = some (g i) := by
  rw [List.getElem?_eq_getElem (by simp)]
  simp

namespace MachineCode

variable (C : MachineCode tm)

/-! ### The peek/pop callback

Its source type is `tm.σ → Option (tm.Γ k) → tm.σ`.  Split into the empty-stack value and a table
indexed by symbol ordinal, both with the finite domain `Fin C.stateCount`. -/

variable (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ)

/-- What the callback does on an empty stack.  Defined even when the alphabet is empty. -/
def emptyState (u : Fin C.stateCount) : Fin C.stateCount :=
  C.stateEquiv (f (C.stateEquiv.symm u) none)

/-- What it does on each symbol, listed in ordinal order.  Empty when the alphabet is. -/
def symbolStates (u : Fin C.stateCount) : List (Fin C.stateCount) :=
  (List.finRange (C.size k)).map fun i =>
    C.stateEquiv (f (C.stateEquiv.symm u) (some ((C.alphabetEquiv k).symm i)))

@[simp] theorem length_symbolStates (u : Fin C.stateCount) :
    (C.symbolStates k f u).length = C.size k := by simp [symbolStates]

/-- The adapter the evaluator calls: total on all numerical inputs, erroring outside the table. -/
def readState (u : Fin C.stateCount) : Option ℕ → Option (Fin C.stateCount)
  | none => some (C.emptyState k f u)
  | some n => (C.symbolStates k f u)[n]?

@[simp] theorem readState_none (u : Fin C.stateCount) :
    C.readState k f u none = some (C.emptyState k f u) := rfl

theorem readState_some (u : Fin C.stateCount) (n : ℕ) :
    C.readState k f u (some n) = (C.symbolStates k f u)[n]? := rfl

/-- Out-of-range codes are rejected here too. -/
theorem readState_of_le {u : Fin C.stateCount} {n : ℕ} (h : C.size k ≤ n) :
    C.readState k f u (some n) = none := by
  rw [readState_some, List.getElem?_eq_none (by simpa using h)]

/-- **The adapter equation.**  This is the single point at which source alphabet values enter the
correctness argument. -/
theorem readState_apply (v : tm.σ) (o : Option (tm.Γ k)) :
    C.readState k f (C.stateEquiv v) (o.map C.symbolCode)
      = some (C.stateEquiv (f v o)) := by
  cases o with
  | none => rw [Option.map_none, readState_none, emptyState, Equiv.symm_apply_apply]
  | some c =>
      rw [Option.map_some, readState_some, symbolStates, symbolCode,
        getElem?_map_finRange (i := C.alphabetEquiv k c)]
      simp [Equiv.symm_apply_apply]

theorem primrec_emptyState : Primrec (C.emptyState k f) := Primrec.dom_finite _

theorem primrec_symbolStates : Primrec (C.symbolStates k f) := Primrec.dom_finite _

theorem primrec_readState : Primrec₂ (C.readState k f) :=
  (Primrec.option_casesOn Primrec.snd
      (Primrec.option_some.comp ((C.primrec_emptyState k f).comp Primrec.fst))
      (Primrec.to₂ (Primrec.list_getElem?.comp
        ((C.primrec_symbolStates k f).comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd))).of_eq
    (by rintro ⟨u, o⟩; cases o <;> rfl)

/-! ### The finite-state callbacks

`push`, `load`, `branch` and `goto` all read only the internal state, whose type is finite. -/

/-- A `push` callback's emitted symbol, as an ordinal. -/
def pushCode (g : tm.σ → tm.Γ k) (u : Fin C.stateCount) : ℕ :=
  C.symbolCode (g (C.stateEquiv.symm u))

@[simp] theorem pushCode_apply (g : tm.σ → tm.Γ k) (v : tm.σ) :
    C.pushCode k g (C.stateEquiv v) = C.symbolCode (g v) := by
  rw [pushCode, Equiv.symm_apply_apply]

theorem primrec_pushCode (g : tm.σ → tm.Γ k) : Primrec (C.pushCode k g) := Primrec.dom_finite _

/-- A `load` callback. -/
def loadCode (a : tm.σ → tm.σ) (u : Fin C.stateCount) : Fin C.stateCount :=
  C.stateEquiv (a (C.stateEquiv.symm u))

@[simp] theorem loadCode_apply (a : tm.σ → tm.σ) (v : tm.σ) :
    C.loadCode a (C.stateEquiv v) = C.stateEquiv (a v) := by
  rw [loadCode, Equiv.symm_apply_apply]

theorem primrec_loadCode (a : tm.σ → tm.σ) : Primrec (C.loadCode a) := Primrec.dom_finite _

/-- A `branch` test. -/
def branchCode (g : tm.σ → Bool) (u : Fin C.stateCount) : Bool := g (C.stateEquiv.symm u)

@[simp] theorem branchCode_apply (g : tm.σ → Bool) (v : tm.σ) :
    C.branchCode g (C.stateEquiv v) = g v := by
  rw [branchCode, Equiv.symm_apply_apply]

theorem primrec_branchCode (g : tm.σ → Bool) : Primrec (C.branchCode g) := Primrec.dom_finite _

/-- A `goto` destination, as a label ordinal. -/
def gotoCode (g : tm.σ → tm.Λ) (u : Fin C.stateCount) : Fin C.labelCount :=
  C.labelEquiv (g (C.stateEquiv.symm u))

@[simp] theorem gotoCode_apply (g : tm.σ → tm.Λ) (v : tm.σ) :
    C.gotoCode g (C.stateEquiv v) = C.labelEquiv (g v) := by
  rw [gotoCode, Equiv.symm_apply_apply]

theorem primrec_gotoCode (g : tm.σ → tm.Λ) : Primrec (C.gotoCode g) := Primrec.dom_finite _

/-! ## D2. The statement evaluator

The outer `Option` is the interpreter's error channel: an out-of-range head code.  Note the two
terminal shapes, which `Turing.TM2` also keeps apart — `halt` *succeeds*, returning a configuration
whose label is `none` and whose state and stacks are untouched.  Cleanup comes from the program that
ran, never from the interpreter. -/

/-- Evaluate one source statement on coded data. -/
def codeStmt : Stmt tm.Γ tm.Λ tm.σ → Fin C.stateCount → (Fin C.stackCount → List ℕ) →
    Option C.CodeCfg
  | .push k g q, u, T =>
      codeStmt q u (C.setStack T (C.stackEquiv k) (C.pushCode k g u :: T (C.stackEquiv k)))
  | .peek k g q, u, T =>
      (C.readHead (C.stackEquiv k) (T (C.stackEquiv k))).bind fun o =>
        (C.readState k g u o).bind fun u' => codeStmt q u' T
  | .pop k g q, u, T =>
      (C.readHead (C.stackEquiv k) (T (C.stackEquiv k))).bind fun o =>
        (C.readState k g u o).bind fun u' =>
          codeStmt q u' (C.setStack T (C.stackEquiv k) (T (C.stackEquiv k)).tail)
  | .load a q, u, T => codeStmt q (C.loadCode a u) T
  | .branch g q₁ q₂, u, T => bif C.branchCode g u then codeStmt q₁ u T else codeStmt q₂ u T
  | .goto g, u, T => some (some (C.gotoCode g u), u, T)
  | .halt, u, T => some (none, u, T)

/-- Executing `halt` returns a **successful** terminal configuration, with the state and stacks as
`halt` found them.  Contrast `codeStep` on an already-terminal configuration, which has no
successor — normal termination, not an interpreter error. -/
@[simp] theorem codeStmt_halt (u : Fin C.stateCount) (T : Fin C.stackCount → List ℕ) :
    C.codeStmt .halt u T = some (none, u, T) := rfl

@[simp] theorem codeStmt_goto (g : tm.σ → tm.Λ) (u : Fin C.stateCount)
    (T : Fin C.stackCount → List ℕ) :
    C.codeStmt (.goto g) u T = some (some (C.gotoCode g u), u, T) := rfl

/-- **The statement-level transition square.**  For every source state and *every* stack family —
no reachability hypothesis — the evaluator succeeds and returns the encoding of the complete
`stepAux` result: label, state, and every stack.  In particular the error channel is unused on
encoded configurations. -/
theorem codeStmt_encode : ∀ (q : Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
    C.codeStmt q (C.stateEquiv v) (C.encodeStacks S) = some (C.encodeCfg (stepAux q v S))
  | .push k g q, v, S => by
      rw [codeStmt, C.pushCode_apply, ← C.encodeStacks_push, stepAux]
      exact codeStmt_encode q v _
  | .peek k g q, v, S => by
      rw [codeStmt, C.readHead_encodeStacks, Option.bind_some, C.readState_apply,
        Option.bind_some, stepAux]
      exact codeStmt_encode q _ S
  | .pop k g q, v, S => by
      rw [codeStmt, C.readHead_encodeStacks, Option.bind_some, C.readState_apply,
        Option.bind_some, ← C.encodeStacks_pop, stepAux]
      exact codeStmt_encode q _ _
  | .load a q, v, S => by
      rw [codeStmt, C.loadCode_apply, stepAux]
      exact codeStmt_encode q _ S
  | .branch g q₁ q₂, v, S => by
      rw [codeStmt, C.branchCode_apply, stepAux]
      cases g v
      · simpa using codeStmt_encode q₂ v S
      · simpa using codeStmt_encode q₁ v S
  | .goto g, v, S => by rw [codeStmt, C.gotoCode_apply]; rfl
  | .halt, _, _ => rfl

/-- And it is primitive recursive, for each fixed statement.  Its input is the pair of coded state
and coded stack family; the statement and its callbacks are parameters of the proof, not runtime
data. -/
theorem primrec_codeStmt : ∀ q : Stmt tm.Γ tm.Λ tm.σ,
    Primrec fun p : Fin C.stateCount × (Fin C.stackCount → List ℕ) => C.codeStmt q p.1 p.2
  | .push k g q => by
      have hstk : Primrec fun p : Fin C.stateCount × (Fin C.stackCount → List ℕ) =>
          C.setStack p.2 (C.stackEquiv k) (C.pushCode k g p.1 :: p.2 (C.stackEquiv k)) :=
        C.primrec_setStack.comp (Primrec.pair Primrec.snd (Primrec.pair
          (Primrec.const (C.stackEquiv k))
          (Primrec.list_cons.comp ((C.primrec_pushCode k g).comp Primrec.fst)
            (Primrec.fin_app.comp Primrec.snd (Primrec.const (C.stackEquiv k))))))
      exact (primrec_codeStmt q).comp (Primrec.pair Primrec.fst hstk)
  | .peek k g q => by
      have hhead : Primrec fun p : Fin C.stateCount × (Fin C.stackCount → List ℕ) =>
          C.readHead (C.stackEquiv k) (p.2 (C.stackEquiv k)) :=
        C.primrec_readHead.comp (Primrec.const (C.stackEquiv k))
          (Primrec.fin_app.comp Primrec.snd (Primrec.const (C.stackEquiv k)))
      have hcont : Primrec₂ fun (x : (Fin C.stateCount × (Fin C.stackCount → List ℕ)) × Option ℕ)
          (u' : Fin C.stateCount) => C.codeStmt q u' x.1.2 :=
        Primrec.to₂ ((primrec_codeStmt q).comp
          (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      exact Primrec.option_bind hhead (Primrec.to₂ (Primrec.option_bind
        ((C.primrec_readState k g).comp (Primrec.fst.comp Primrec.fst) Primrec.snd) hcont))
  | .pop k g q => by
      have hhead : Primrec fun p : Fin C.stateCount × (Fin C.stackCount → List ℕ) =>
          C.readHead (C.stackEquiv k) (p.2 (C.stackEquiv k)) :=
        C.primrec_readHead.comp (Primrec.const (C.stackEquiv k))
          (Primrec.fin_app.comp Primrec.snd (Primrec.const (C.stackEquiv k)))
      have hT : Primrec fun x : (Fin C.stateCount × (Fin C.stackCount → List ℕ)) × Option ℕ =>
          x.1.2 := Primrec.snd.comp Primrec.fst
      have htail : Primrec fun x : (Fin C.stateCount × (Fin C.stackCount → List ℕ)) × Option ℕ =>
          C.setStack x.1.2 (C.stackEquiv k) (x.1.2 (C.stackEquiv k)).tail :=
        C.primrec_setStack.comp (Primrec.pair hT (Primrec.pair (Primrec.const (C.stackEquiv k))
          (Primrec.list_tail.comp (Primrec.fin_app.comp hT (Primrec.const (C.stackEquiv k))))))
      have hcont : Primrec₂ fun (x : (Fin C.stateCount × (Fin C.stackCount → List ℕ)) × Option ℕ)
          (u' : Fin C.stateCount) =>
            C.codeStmt q u' (C.setStack x.1.2 (C.stackEquiv k) (x.1.2 (C.stackEquiv k)).tail) :=
        Primrec.to₂ ((primrec_codeStmt q).comp
          (Primrec.pair Primrec.snd (htail.comp Primrec.fst)))
      exact Primrec.option_bind hhead (Primrec.to₂ (Primrec.option_bind
        ((C.primrec_readState k g).comp (Primrec.fst.comp Primrec.fst) Primrec.snd) hcont))
  | .load a q =>
      (primrec_codeStmt q).comp
        (Primrec.pair ((C.primrec_loadCode a).comp Primrec.fst) Primrec.snd)
  | .branch g q₁ q₂ =>
      Primrec.cond ((C.primrec_branchCode g).comp Primrec.fst)
        (primrec_codeStmt q₁) (primrec_codeStmt q₂)
  | .goto g =>
      Primrec.option_some.comp (Primrec.pair
        (Primrec.option_some.comp ((C.primrec_gotoCode g).comp Primrec.fst)) Primrec.id)
  | .halt =>
      Primrec.option_some.comp (Primrec.pair (Primrec.const none) Primrec.id)

/-! ### The error channel, exercised

`codeStmt_encode` says the outer `Option` is never `none` on an encoded configuration.  These two
lemmas are the other half: on a stack whose head code is out of range it *is*. -/

theorem codeStmt_peek_of_le (k : tm.K) (g : tm.σ → Option (tm.Γ k) → tm.σ)
    (q : Stmt tm.Γ tm.Λ tm.σ) (u : Fin C.stateCount) (T : Fin C.stackCount → List ℕ)
    {n : ℕ} {rest : List ℕ} (hT : T (C.stackEquiv k) = n :: rest)
    (hn : C.sizeCode (C.stackEquiv k) ≤ n) :
    C.codeStmt (.peek k g q) u T = none := by
  rw [codeStmt, hT, C.readHead_cons_of_le hn]
  rfl

theorem codeStmt_pop_of_le (k : tm.K) (g : tm.σ → Option (tm.Γ k) → tm.σ)
    (q : Stmt tm.Γ tm.Λ tm.σ) (u : Fin C.stateCount) (T : Fin C.stackCount → List ℕ)
    {n : ℕ} {rest : List ℕ} (hT : T (C.stackEquiv k) = n :: rest)
    (hn : C.sizeCode (C.stackEquiv k) ≤ n) :
    C.codeStmt (.pop k g q) u T = none := by
  rw [codeStmt, hT, C.readHead_cons_of_le hn]
  rfl

/-! ## D3. The machine step, and transferring B0

`Turing.TM2.step` has no successor for a configuration whose label is `none`.  `codeStep` copies
that exactly, which is what makes the two terminal shapes distinguishable: executing `halt`
*succeeds* with a `none`-labelled configuration, and *stepping* such a configuration has no
successor.  That second outer `none` is normal termination, not an interpreter error — the error
channel is the malformed-code branch, and `codeStep_encodeCfg_eq_none_iff` separates the two on
encoded configurations. -/

/-- One coded machine step. -/
def codeStep : C.CodeCfg → Option C.CodeCfg
  | (none, _, _) => none
  | (some l, u, T) => C.codeStmt (tm.m (C.labelEquiv.symm l)) u T

@[simp] theorem codeStep_none (u : Fin C.stateCount) (T : Fin C.stackCount → List ℕ) :
    C.codeStep (none, u, T) = none := rfl

@[simp] theorem codeStep_some (l : Fin C.labelCount) (u : Fin C.stateCount)
    (T : Fin C.stackCount → List ℕ) :
    C.codeStep (some l, u, T) = C.codeStmt (tm.m (C.labelEquiv.symm l)) u T := rfl

theorem primrec_codeStep : Primrec C.codeStep := by
  have hbody : ∀ l : Fin C.labelCount, Primrec fun c : C.CodeCfg =>
      C.codeStmt (tm.m (C.labelEquiv.symm l)) c.2.1 c.2.2 := fun l =>
    (C.primrec_codeStmt (tm.m (C.labelEquiv.symm l))).comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  have hswap : Primrec₂ fun (c : C.CodeCfg) (l : Fin C.labelCount) =>
      C.codeStmt (tm.m (C.labelEquiv.symm l)) c.2.1 c.2.2 :=
    (Primrec.fin_curry₁.2 hbody).swap
  exact (Primrec.option_casesOn Primrec.fst (Primrec.const none) hswap).of_eq
    (by rintro ⟨l, u, T⟩; cases l <;> rfl)

/-- **The transition square.**  Coded stepping is source stepping, transported.  Holds for every
source configuration, terminal ones included. -/
theorem codeStep_encodeCfg (c : tm.Cfg) :
    C.codeStep (C.encodeCfg c) = Option.map C.encodeCfg (tm.step c) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => rfl
  | some l =>
      change C.codeStmt (tm.m (C.labelEquiv.symm (C.labelEquiv l))) (C.stateEquiv v)
          (C.encodeStacks S) = _
      rw [Equiv.symm_apply_apply, C.codeStmt_encode]
      rfl

/-- On an encoded configuration the interpreter's error channel is therefore **unused**: an outer
`none` from the coded step means the source machine has reached a terminal label, and nothing else.
(On an arbitrary numerical configuration it could also mean a malformed head code; that case is
outside the simulation.  "Terminal label" is weaker than the exact `haltList` cleanup, which stays a
property of a computation certificate.) -/
theorem codeStep_encodeCfg_eq_none_iff (c : tm.Cfg) :
    C.codeStep (C.encodeCfg c) = none ↔ tm.step c = none := by
  rw [C.codeStep_encodeCfg, Option.map_eq_none_iff]

/-- The total steps are semiconjugate, so B0's retention argument transfers rather than being
reproved. -/
theorem semiconj_encodeCfg :
    Function.Semiconj C.encodeCfg (keepStep tm.step) (keepStep C.codeStep) := by
  intro c
  change C.encodeCfg ((tm.step c).getD c) = (C.codeStep (C.encodeCfg c)).getD (C.encodeCfg c)
  rw [C.codeStep_encodeCfg]
  cases tm.step c <;> rfl

theorem iterate_keepStep_codeStep (n : ℕ) (c : tm.Cfg) :
    (keepStep C.codeStep)^[n] (C.encodeCfg c) = C.encodeCfg ((keepStep tm.step)^[n] c) :=
  (C.semiconj_encodeCfg.iterate_right n c).symm

/-- **Bounded evaluation, coded.**  Running the numerical evaluator for any budget gives the
encoding of B0's bounded evaluation for the same budget. -/
theorem iterate_keepStep_codeStep_boundedEval (budget : ℕ) (c : tm.Cfg) :
    (keepStep C.codeStep)^[budget] (C.encodeCfg c) = C.encodeCfg (boundedEval tm budget c) :=
  C.iterate_keepStep_codeStep budget c

theorem primrec_keepStep_codeStep : Primrec (keepStep C.codeStep) :=
  Primrec.option_getD.comp C.primrec_codeStep Primrec.id

/-- …and iterating it for a budget supplied as input is primitive recursive too.  This is the shape
B3 composes with the time polynomial. -/
theorem primrec_iterate_keepStep :
    Primrec₂ fun (budget : ℕ) (c : C.CodeCfg) => (keepStep C.codeStep)^[budget] c :=
  Primrec.nat_iterate Primrec.fst Primrec.snd
    (C.primrec_keepStep_codeStep.comp Primrec.snd).to₂

end MachineCode

end PCP.Machine
