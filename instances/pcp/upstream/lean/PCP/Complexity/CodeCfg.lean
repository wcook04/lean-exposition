import PCP.Complexity.SymbolCode

/-!
# Coded configurations and the coded stack operations

`tm.Cfg` carries a *dependent* stack family `∀ k, List (tm.Γ k)`. The interpreter runs instead on

```text
CodeCfg = Option (Fin labelCount) × Fin stateCount × (Fin stackCount → List ℕ)
```

whose stacks are a uniform `List ℕ`, so its update and lookup operations carry no dependent symbol
type and `Primcodable.finArrow` handles the stack collection without a computability API for
dependent function types.

`encodeCfg` is a **semantic comparison map**, not a coding instance: no `Primcodable (tm.Cfg)` is
claimed or needed. Computability belongs to the numerical operations; `encodeCfg` is what ties them
back to `Turing.TM2.stepAux`.

## The two `DecidableEq`s

The source update uses the machine's own `DecidableEq tm.K`; the coded update uses ordinary `Fin`
equality. `encodeStacks_update` is the theorem that lets one be replaced by the other, and it is
stated once here so that no later proof has to reason about both at the same time.

## Configuration space is not finite

Labels, states, stack indices and each alphabet are finite, but stack *lengths* are unbounded, so
`CodeCfg` is generally infinite. Nothing below assumes otherwise; finiteness is used only for the
tables, never for the configurations.
-/

namespace PCP.Machine

open Turing

variable {tm : FinTM2}

namespace MachineCode

variable (C : MachineCode tm)

/-- Coded configurations: a label ordinal (or none, for halted), a state ordinal, and one numerical
stack per stack index. -/
abbrev CodeCfg : Type :=
  Option (Fin C.labelCount) × Fin C.stateCount × (Fin C.stackCount → List ℕ)

/-! ## The coded stack operations

These are the operations the interpreter performs. They are ordinary functions on `List ℕ`, and
their primitive recursiveness is proved here once. -/

/-- Look up a coded stack. -/
def getStack (T : Fin C.stackCount → List ℕ) (j : Fin C.stackCount) : List ℕ := T j

/-- Replace a coded stack. -/
def setStack (T : Fin C.stackCount → List ℕ) (j : Fin C.stackCount) (xs : List ℕ) :
    Fin C.stackCount → List ℕ := Function.update T j xs

@[simp] theorem setStack_self (T : Fin C.stackCount → List ℕ) (j : Fin C.stackCount)
    (xs : List ℕ) : C.setStack T j xs j = xs := Function.update_self ..

@[simp] theorem setStack_of_ne {T : Fin C.stackCount → List ℕ} {i j : Fin C.stackCount}
    (h : i ≠ j) (xs : List ℕ) : C.setStack T j xs i = T i := Function.update_of_ne h ..

theorem primrec_getStack : Primrec₂ C.getStack := Primrec.fin_app

theorem primrec_setStack :
    Primrec fun q : (Fin C.stackCount → List ℕ) × Fin C.stackCount × List ℕ =>
      C.setStack q.1 q.2.1 q.2.2 := by
  refine Primrec.fin_curry.2 (Primrec.ite (Primrec.eq.comp Primrec.snd
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.fin_app.comp (Primrec.fst.comp Primrec.fst) Primrec.snd) |>.of_eq ?_)
  rintro ⟨⟨T, j, xs⟩, i⟩
  by_cases h : i = j
  · subst h; simp [setStack]
  · rw [ite_eq_right h]; exact (C.setStack_of_ne h xs).symm

/-! ## Encoding a source configuration -/

/-- The coded form of a source stack family. -/
def encodeStacks (S : ∀ k, List (tm.Γ k)) (j : Fin C.stackCount) : List ℕ :=
  C.codeStack (C.stackEquiv.symm j) (S (C.stackEquiv.symm j))

/-- Reading the coded family at a source index.  The `Equiv` round trip is discharged here once;
the motive is type-correct because every occurrence of the index is uniform. -/
@[simp] theorem encodeStacks_stackEquiv (S : ∀ k, List (tm.Γ k)) (k : tm.K) :
    C.encodeStacks S (C.stackEquiv k) = C.codeStack k (S k) := by
  change C.codeStack (C.stackEquiv.symm (C.stackEquiv k)) (S (C.stackEquiv.symm (C.stackEquiv k)))
    = C.codeStack k (S k)
  rw [Equiv.symm_apply_apply]

/-- **The dependent update target.**  A source update at `k` — using the *machine's* `DecidableEq
tm.K` — becomes a coded update at `stackEquiv k` using ordinary `Fin` equality. -/
theorem encodeStacks_update (S : ∀ k, List (tm.Γ k)) (k : tm.K) (xs : List (tm.Γ k)) :
    C.encodeStacks (Function.update S k xs)
      = C.setStack (C.encodeStacks S) (C.stackEquiv k) (C.codeStack k xs) := by
  funext j
  by_cases h : j = C.stackEquiv k
  · subst h
    rw [C.encodeStacks_stackEquiv, Function.update_self, C.setStack_self]
  · have hk : C.stackEquiv.symm j ≠ k := fun hkk => h (by rw [← hkk, Equiv.apply_symm_apply])
    rw [C.setStack_of_ne h]
    change C.codeStack _ (Function.update S k xs (C.stackEquiv.symm j)) = _
    rw [Function.update_of_ne hk]
    rfl

/-- Popping: the coded tail of an encoded stack is the encoding of the source tail. -/
@[simp] theorem codeStack_tail (k : tm.K) (s : List (tm.Γ k)) :
    (C.codeStack k s).tail = C.codeStack k s.tail := by cases s <;> rfl

/-- Pushing: the coded cons of an encoded stack is the encoding of the source cons. -/
theorem codeStack_push (k : tm.K) (c : tm.Γ k) (s : List (tm.Γ k)) :
    C.symbolCode c :: C.codeStack k s = C.codeStack k (c :: s) := rfl

/-! ### The three observations `stepAux` makes

`Turing.TM2.stepAux` touches a stack in exactly three ways: it reads `head?`, it conses, and it
takes `tail`.  Each is transported here, so the statement evaluator can work entirely with coded
stacks. -/

/-- **Head read.**  The interpreter's three-case reader, on an encoded configuration, never reports
an error and reports exactly the source's `head?`. -/
@[simp] theorem readHead_encodeStacks (S : ∀ k, List (tm.Γ k)) (k : tm.K) :
    C.readHead (C.stackEquiv k) (C.encodeStacks S (C.stackEquiv k))
      = some ((S k).head?.map C.symbolCode) := by
  rw [C.encodeStacks_stackEquiv, C.readHead_codeStack]

/-- …and decoding it returns the source head itself, empty stack included. -/
theorem decode_readHead_encodeStacks (S : ∀ k, List (tm.Γ k)) (k : tm.K) :
    (C.readHead (C.stackEquiv k) (C.encodeStacks S (C.stackEquiv k))).map
        (fun o => o.bind (C.decodeSymbol k))
      = some ((S k).head?) := by
  rw [C.encodeStacks_stackEquiv]; exact C.decode_readHead_codeStack k (S k)

/-- **Push**, coded. -/
theorem encodeStacks_push (S : ∀ k, List (tm.Γ k)) (k : tm.K) (c : tm.Γ k) :
    C.encodeStacks (Function.update S k (c :: S k))
      = C.setStack (C.encodeStacks S) (C.stackEquiv k)
          (C.symbolCode c :: C.encodeStacks S (C.stackEquiv k)) := by
  rw [C.encodeStacks_update, C.encodeStacks_stackEquiv, C.codeStack_push]

/-- **Pop**, coded. -/
theorem encodeStacks_pop (S : ∀ k, List (tm.Γ k)) (k : tm.K) :
    C.encodeStacks (Function.update S k (S k).tail)
      = C.setStack (C.encodeStacks S) (C.stackEquiv k)
          (C.encodeStacks S (C.stackEquiv k)).tail := by
  rw [C.encodeStacks_update, C.encodeStacks_stackEquiv, C.codeStack_tail]

/-- The coded configuration of a source configuration. -/
def encodeCfg (c : tm.Cfg) : C.CodeCfg :=
  (c.l.map C.labelEquiv, C.stateEquiv c.var, C.encodeStacks c.stk)

@[simp] theorem encodeCfg_fst (c : tm.Cfg) : (C.encodeCfg c).1 = c.l.map C.labelEquiv := rfl

@[simp] theorem encodeCfg_state (c : tm.Cfg) : (C.encodeCfg c).2.1 = C.stateEquiv c.var := rfl

@[simp] theorem encodeCfg_stacks (c : tm.Cfg) : (C.encodeCfg c).2.2 = C.encodeStacks c.stk := rfl

/-- A halted source configuration is exactly one whose coded label is `none`: the terminal marker
survives the encoding, and is not conflated with anything else. -/
@[simp] theorem encodeCfg_fst_eq_none_iff (c : tm.Cfg) : (C.encodeCfg c).1 = none ↔ c.l = none := by
  rcases hl : c.l with _ | l <;> simp [encodeCfg, hl]

theorem encodeStacks_injective : Function.Injective C.encodeStacks := by
  intro S S' h
  funext k
  have := congrFun h (C.stackEquiv k)
  rw [C.encodeStacks_stackEquiv, C.encodeStacks_stackEquiv] at this
  exact C.codeStack_injective k this

/-- Encoding loses nothing: label, state and every stack are recoverable. -/
theorem encodeCfg_injective : Function.Injective C.encodeCfg := by
  intro c c' h
  have hl : c.l = c'.l :=
    Option.map_injective C.labelEquiv.injective (congrArg Prod.fst h)
  have hv : c.var = c'.var := C.stateEquiv.injective (congrArg (fun p => p.2.1) h)
  have hS : c.stk = c'.stk := C.encodeStacks_injective (congrArg (fun p => p.2.2) h)
  have : (⟨c.l, c.var, c.stk⟩ : tm.Cfg) = ⟨c'.l, c'.var, c'.stk⟩ := by rw [hl, hv, hS]
  exact this

end MachineCode

end PCP.Machine
