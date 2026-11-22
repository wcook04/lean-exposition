import PCP.Complexity.CallTrace
import PCP.Complexity.Machine

/-!
# A complete, reusable call: entry, the callee, and return

`CallTrace.lean` transports a callee's execution once the callee is already started.  Getting it
started is this module: a caller program that converts an external `Sym` tape onto the callee's
input stack **through the callee's own alphabet equivalence**, while restoring its own copy.

## Layout

Caller stacks are `CallSlot ⊕ G` — retained `input`, `dst`, `scratch`, and an arbitrary unrelated
frame `G` whose alphabets need nothing.  Caller control is `Option Sym × P`: a temporary symbol for
the transfer, and an arbitrary payload carried across the call.  The callee's own state is a
*separate* component and is never borrowed to hold a popped symbol — the callee's state type is
arbitrary, and entry has to establish its `initialState` anyway.

## This is a subroutine theorem, not an `initList` theorem

`parentTM.main` is the callee's main label, so a run starting at a **caller** entry label is not a
whole-machine execution of this parent.  A later checker wrapper will choose its own main label and
its own initial tape; these configurations must not be silently identified.

## Counting

Phase one drains `input` to `scratch`; phase two drains `scratch`, pushing each symbol back onto
`input` **and**, converted, onto the callee's input stack, with the temporary reset only after both
pushes.  The callee's initial state and the jump to its main label ride in phase two's empty-exit
statement, so entry costs exactly `2 * xs.length + 2` — no extra dispatch label, nothing to charge
separately.  That subtotal covers entry alone: the callee's own count, output transfer and cleanup
are charged on top of it, never folded into it.

Return is the mirror image, on the fixed labels `ret` and `return2`: drain the callee's output
stack — **converting each symbol through `eOut` before it reaches the caller's `Option Sym`
temporary**, so nothing assumes the callee's output alphabet is literally `Sym` — then drain
scratch onto the destination.  Its empty exit reaches `resume`, which is the **boundary**: the
caller's continuation has not run.  Return costs `2 * ys.length + 2`, and it leaves every callee
stack empty, so the machine is ready to be called again.

A complete call therefore costs `(2 * xs.length + 2) + h.steps + (2 * ys.length + 2)`, with the
source's own bound `m` kept separate from its recorded `h.steps`.  `callPoly` turns that into one
polynomial in the encoded input length, and `repeatEvals` charges a second call — including the
single counted step of the resume jump between them.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-- The caller's own stacks. -/
inductive CallSlot | input | dst | scratch
  deriving DecidableEq, Inhabited, Repr

instance : Fintype CallSlot where
  elems := {CallSlot.input, CallSlot.dst, CallSlot.scratch}
  complete := by intro x; cases x <;> decide

/-- The caller's labels.  `ret` is where the callee's translated `halt` lands; `resume` is where the
return program will continue, and is left to the supplied continuation here. -/
inductive CallLabel
  -- the four fixed transfer phases, and the boundary
  | entry1 | entry2 | ret | return2 | resume
  -- tuple preparation: three preserving copies with two separator pushes between them.  Like
  -- `resume`, these dispatch through the supplied continuation, so `callProgram` is unchanged and
  -- every theorem about it still applies.
  | prepA1 | prepA2 | sepR | prepR1 | prepR2 | sepX | prepX1 | prepX2
  -- answer-tag dispatch: `resume` pops the encoded answer's head and lands on one of these three.
  -- `lookup` is the only one that may consult the witness.
  | decided | rejected | lookup
  -- the binary counter's zero test: one initialisation step, a forward scan, a restoring scan, and
  -- the two boundaries it selects between.
  | ztInit | ztScan | ztRestore | ztZero | ztPos
  -- the counter's decrement: initialisation, a full-width borrow scan, a restoring scan, and its
  -- own done boundary.
  | dcInit | dcScan | dcRestore | dcDone
  -- the witness search: the main loop label, the exhausted and selected boundaries, the prefix
  -- restoration, the counter drain, and its own done boundary.
  | lkMain | lkExhausted | lkSelected | lkRestore | lkDrain | lkDone
  -- the adaptive turnaround: append the answer at the *end* of the history (two scans through the
  -- call scratch), clear the spent tuple, decrement the depth, and start the next iteration.
  | tuScan | tuPush | tuBack | tuClear | tuDepth
  -- terminal cleanup: both terminal boundaries drain the destination, the spent tuple and the
  -- answer history, normalise finite control, and stop at a reusable seed boundary.
  | clDst | clInp | clHist | clNorm | clDone
  -- seed enumeration: initialise the carry, scan the fixed-width seed tape onto scratch computing
  -- each output cell, scan it back, then test the overflow; and the enumeration's own boundary.
  | inInit | inScan | inBack | inTest | enDone
  -- constructing the canonical-width seed: copy the input's length into a unary tape (preserving
  -- the input), then halve it until empty, emitting a fixed batch of seed cells per pass.
  | cwCopy | cwBack | cwTest | cwHalf | cwMove | cwDone
  -- the wrapper's pair parser: split at the separator onto scratch, restore the input component,
  -- move the witness component onto scratch, restore it onto the witness stack.
  | pdSplit | pdBackX | pdRest | pdBackW
  -- the wrapper's finalisation: drain the input, the seed and the witness, then reset and halt.
  | fnX | fnR | fnW
  deriving DecidableEq, Inhabited, Repr

-- The completeness check decides membership in a sixty-odd-element `insert` chain, which exceeds
-- the default recursion depth; the limit is raised for this one instance only.
set_option maxRecDepth 8000 in
instance : Fintype CallLabel where
  elems := {CallLabel.entry1, CallLabel.entry2, CallLabel.ret, CallLabel.return2,
    CallLabel.resume, CallLabel.prepA1, CallLabel.prepA2, CallLabel.sepR, CallLabel.prepR1,
    CallLabel.prepR2, CallLabel.sepX, CallLabel.prepX1, CallLabel.prepX2, CallLabel.decided,
    CallLabel.rejected, CallLabel.lookup, CallLabel.ztInit, CallLabel.ztScan,
    CallLabel.ztRestore, CallLabel.ztZero, CallLabel.ztPos, CallLabel.dcInit, CallLabel.dcScan,
    CallLabel.dcRestore, CallLabel.dcDone, CallLabel.lkMain, CallLabel.lkExhausted,
    CallLabel.lkSelected, CallLabel.lkRestore, CallLabel.lkDrain, CallLabel.lkDone,
    CallLabel.tuScan, CallLabel.tuPush, CallLabel.tuBack, CallLabel.tuClear,
    CallLabel.tuDepth, CallLabel.clDst, CallLabel.clInp, CallLabel.clHist, CallLabel.clNorm,
    CallLabel.clDone, CallLabel.inInit, CallLabel.inScan, CallLabel.inBack, CallLabel.inTest,
    CallLabel.enDone, CallLabel.cwCopy, CallLabel.cwBack, CallLabel.cwTest, CallLabel.cwHalf,
    CallLabel.cwMove, CallLabel.cwDone, CallLabel.pdSplit, CallLabel.pdBackX, CallLabel.pdRest,
    CallLabel.pdBackW, CallLabel.fnX, CallLabel.fnR, CallLabel.fnW}
  complete := by intro x; cases x <;> decide

section

variable (tm : FinTM2) (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type)
  (P : Type) [Fintype P]

/-- `Sym` on the caller's own stacks, the caller's alphabets on the unrelated frame. -/
abbrev callΓ : CallSlot ⊕ G → Type
  | .inl _ => Sym
  | .inr j => Γg j

/-- The caller's stack family. -/
def callFrame (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    ∀ j : CallSlot ⊕ G, List (callΓ G Γg j)
  | .inl .input => inp
  | .inl .dst => dst
  | .inl .scratch => scratch
  | .inr j => g j

/-- The caller's control: a temporary symbol for the transfer, and a payload carried across. -/
abbrev CallState : Type := Option Sym × P

variable {tm G Γg P}

/-- The caller program.  All four transfer phases — `entry1`, `entry2`, `ret`, `return2` — are
fixed; only `resume` dispatches to the supplied continuation.  So the entry, return and call
theorems below hold for **every** continuation, and the repeated-call construction is free to choose
one that jumps back to `entry1`. -/
def callProgram (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym)
    (cont : CallLabel → Stmt (embedΓ tm (CallSlot ⊕ G) (callΓ G Γg)) (tm.Λ ⊕ CallLabel)
      (tm.σ × CallState P)) :
    CallLabel → Stmt (embedΓ tm (CallSlot ⊕ G) (callΓ G Γg)) (tm.Λ ⊕ CallLabel)
      (tm.σ × CallState P)
  | .entry1 =>
      pop (.inr (.inl .input)) (fun p o => (p.1, (o, p.2.2))) <|
        branch (fun p => p.2.1.isSome)
          (push (.inr (.inl .scratch)) (fun p => p.2.1.getD Sym.sep)
            (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .entry1))))
          (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .entry2)))
  | .entry2 =>
      pop (.inr (.inl .scratch)) (fun p o => (p.1, (o, p.2.2))) <|
        branch (fun p => p.2.1.isSome)
          (push (.inr (.inl .input)) (fun p => p.2.1.getD Sym.sep)
            (push (.inl tm.k₀) (fun p => eIn.symm (p.2.1.getD Sym.sep))
              (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .entry2)))))
          (load (fun p => (tm.initialState, (none, p.2.2))) (goto (fun _ => .inl tm.main)))
  | .ret =>
      pop (.inl tm.k₁) (fun p o => (p.1, (o.map eOut, p.2.2))) <|
        branch (fun p => p.2.1.isSome)
          (push (.inr (.inl .scratch)) (fun p => p.2.1.getD Sym.sep)
            (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .ret))))
          (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .return2)))
  | .return2 =>
      pop (.inr (.inl .scratch)) (fun p o => (p.1, (o, p.2.2))) <|
        branch (fun p => p.2.1.isSome)
          (push (.inr (.inl .dst)) (fun p => p.2.1.getD Sym.sep)
            (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .return2))))
          (load (fun p => (p.1, (none, p.2.2))) (goto (fun _ => .inr .resume)))
  | l => cont l

variable (tm G Γg P)

/-- The parent machine for a call: the callee embedded under the caller program above. -/
def callTM (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : P)
    (cont : CallLabel → Stmt (embedΓ tm (CallSlot ⊕ G) (callΓ G Γg)) (tm.Λ ⊕ CallLabel)
      (tm.σ × CallState P)) : FinTM2 :=
  parentTM tm (CallSlot ⊕ G) (callΓ G Γg) ((none, p₀) : CallState P) CallLabel.ret
    (callProgram eIn eOut cont)

variable {tm G Γg P}

/-- A configuration named by all its parts. -/
def callCfg (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : P) (cont : _)
    (l : Option (tm.Λ ⊕ CallLabel)) (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm G Γg P eIn eOut p₀ cont).Cfg where
  l := l
  var := (v, (temp, pay))
  stk := embedStacks tm (CallSlot ⊕ G) (callΓ G Γg) S (callFrame G Γg inp dst scratch g)

section Steps

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : P)
  (cont : CallLabel → Stmt (embedΓ tm (CallSlot ⊕ G) (callΓ G Γg)) (tm.Λ ⊕ CallLabel)
    (tm.σ × CallState P))

theorem call_step_entry1_cons (v : tm.σ) (temp : Option Sym) (pay : P) (c : Sym)
    (S : ∀ k, List (tm.Γ k)) (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .entry1)) v temp pay S (c :: inp) dst scratch g)
      = some (callCfg eIn eOut p₀ cont (some (.inr .entry1)) v none pay S inp dst
          (c :: scratch) g) := by
  simp only [FinTM2.step, callTM, parentTM, callProgram, callCfg, Turing.TM2.step,
    Turing.TM2.stepAux, embedStacks, callFrame, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  refine congrArg some (congrArg (fun T => (⟨some (.inr .entry1), (v, (none, pay)), T⟩ :
    (callTM tm G Γg P eIn eOut p₀ cont).Cfg)) ?_)
  funext i
  rcases i with k | (s | j)
  · simp [Function.update, embedStacks]
  · cases s <;> simp [Function.update, embedStacks, callFrame]
  · simp [Function.update, embedStacks, callFrame]

theorem call_step_entry1_nil (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .entry1)) v temp pay S [] dst scratch g)
      = some (callCfg eIn eOut p₀ cont (some (.inr .entry2)) v none pay S [] dst scratch g) := by
  simp only [FinTM2.step, callTM, parentTM, callProgram, callCfg, Turing.TM2.step,
    Turing.TM2.stepAux, embedStacks, callFrame, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  refine congrArg some (congrArg (fun T => (⟨some (.inr .entry2), (v, (none, pay)), T⟩ :
    (callTM tm G Γg P eIn eOut p₀ cont).Cfg)) ?_)
  funext i
  rcases i with k | (s | j)
  · simp [Function.update, embedStacks]
  · cases s <;> simp [Function.update, embedStacks, callFrame]
  · simp [Function.update, embedStacks, callFrame]

/-- **The two-push entry step.**  The popped symbol goes back to the caller's `input` *and*,
converted through `eIn.symm`, onto the callee's input stack; the temporary is reset only after
both. -/
theorem call_step_entry2_cons (v : tm.σ) (temp : Option Sym) (pay : P) (c : Sym)
    (S : ∀ k, List (tm.Γ k)) (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .entry2)) v temp pay S inp dst (c :: scratch) g)
      = some (callCfg eIn eOut p₀ cont (some (.inr .entry2)) v none pay
          (Function.update S tm.k₀ (eIn.symm c :: S tm.k₀)) (c :: inp) dst scratch g) := by
  simp only [FinTM2.step, callTM, parentTM, callProgram, callCfg, Turing.TM2.step,
    Turing.TM2.stepAux, embedStacks, callFrame, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  refine congrArg some (congrArg (fun T => (⟨some (.inr .entry2), (v, (none, pay)), T⟩ :
    (callTM tm G Γg P eIn eOut p₀ cont).Cfg)) ?_)
  funext i
  rcases i with k | (s | j)
  · by_cases h : k = tm.k₀
    · subst h; simp [Function.update, embedStacks]
    · simp [Function.update, embedStacks, h]
  · cases s <;> simp [Function.update, embedStacks, callFrame]
  · simp [Function.update, embedStacks, callFrame]

/-- The empty exit installs the callee's own `initialState` and jumps to its main label. -/
theorem call_step_entry2_nil (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (inp dst : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .entry2)) v temp pay S inp dst [] g)
      = some (callCfg eIn eOut p₀ cont (some (.inl tm.main)) tm.initialState none pay S inp dst
          [] g) := by
  simp only [FinTM2.step, callTM, parentTM, callProgram, callCfg, Turing.TM2.step,
    Turing.TM2.stepAux, embedStacks, callFrame, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inl tm.main), (tm.initialState, (none, pay)), T⟩ :
      (callTM tm G Γg P eIn eOut p₀ cont).Cfg)) ?_)
  funext i
  rcases i with k | (s | j)
  · simp [Function.update, embedStacks]
  · cases s <;> simp [Function.update, embedStacks, callFrame]
  · simp [Function.update, embedStacks, callFrame]

/-! ## The phase invariants -/

theorem entry_phase_one : ∀ (xs : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (dst scratch : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[xs.length + 1]
        (some (callCfg eIn eOut p₀ cont (some (.inr .entry1)) v temp pay S xs dst scratch g))
      = some (callCfg eIn eOut p₀ cont (some (.inr .entry2)) v none pay S [] dst
          (xs.reverse ++ scratch) g)
  | [], v, temp, pay, S, dst, scratch, g => by
      change (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .entry1)) v temp pay S [] dst scratch g) = _
      rw [call_step_entry1_nil]
      rfl
  | c :: xs, v, temp, pay, S, dst, scratch, g => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[xs.length + 1]
        ((callTM tm G Γg P eIn eOut p₀ cont).step
          (callCfg eIn eOut p₀ cont (some (.inr .entry1)) v temp pay S (c :: xs) dst scratch g)) = _
      rw [call_step_entry1_cons, entry_phase_one xs v none pay S dst (c :: scratch) g]
      simp

/-- Phase two restores the caller's input **and** builds the callee's, converting each symbol
through `eIn.symm`; its empty exit installs the callee's `initialState` and jumps to its main
label. -/
theorem entry_phase_two : ∀ (ys : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (inp dst : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[ys.length + 1]
        (some (callCfg eIn eOut p₀ cont (some (.inr .entry2)) v temp pay S inp dst ys g))
      = some (callCfg eIn eOut p₀ cont (some (.inl tm.main)) tm.initialState none pay
          (Function.update S tm.k₀ (ys.reverse.map eIn.symm ++ S tm.k₀))
          (ys.reverse ++ inp) dst [] g)
  | [], v, temp, pay, S, inp, dst, g => by
      change (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .entry2)) v temp pay S inp dst [] g) = _
      rw [call_step_entry2_nil]
      simp
  | c :: ys, v, temp, pay, S, inp, dst, g => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[ys.length + 1]
        ((callTM tm G Γg P eIn eOut p₀ cont).step
          (callCfg eIn eOut p₀ cont (some (.inr .entry2)) v temp pay S inp dst (c :: ys) g)) = _
      rw [call_step_entry2_cons,
        entry_phase_two ys v none pay (Function.update S tm.k₀ (eIn.symm c :: S tm.k₀))
          (c :: inp) dst g]
      simp [Function.update_idem]

end Steps

/-! ## The entry theorem -/

/-- The initial stacks, as an update of the empty family. -/
theorem initList_stk_eq_update (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    (initList tm l).stk = Function.update (fun _ => []) tm.k₀ l := by
  funext k
  change (dite (k = tm.k₀) _ _) = _
  by_cases h : k = tm.k₀
  · subst h
    rw [dite_eq_left rfl, Function.update_self]
    rfl
  · rw [dite_eq_right h, Function.update_of_ne h]

section Entry

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : P)
  (cont : CallLabel → Stmt (embedΓ tm (CallSlot ⊕ G) (callΓ G Γg)) (tm.Λ ⊕ CallLabel)
    (tm.σ × CallState P))

/-- **The entry equation.**  From the caller's entry label with external input `xs`, empty scratch
and every callee stack empty, exactly `2 * xs.length + 2` steps reach the **embedded callee
`initList`** — the callee's main label, its own `initialState`, its input tape
`xs.map eIn.symm`, and every other callee stack empty — with the caller's `xs` restored, scratch
empty, destination and unrelated frame untouched, and the temporary normalized.

Holds for every continuation `cont`, so the return program cannot affect it. -/
theorem entry_trace (xs dst : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P)
    (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[2 * xs.length + 2]
        (some (callCfg eIn eOut p₀ cont (some (.inr .entry1)) v temp pay (fun _ => []) xs dst [] g))
      = some (embedCfg (F := CallSlot ⊕ G) (Γf := callΓ G Γg) CallLabel.ret
          ((none, pay) : CallState P) (callFrame G Γg xs dst [] g)
          (initList tm (xs.map eIn.symm))) := by
  have hsplit : 2 * xs.length + 2 = (xs.reverse.length + 1) + (xs.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hsplit, Function.iterate_add_apply,
    entry_phase_one eIn eOut p₀ cont xs v temp pay (fun _ => []) dst [] g, List.append_nil,
    entry_phase_two eIn eOut p₀ cont xs.reverse v none pay (fun _ => []) [] dst g]
  refine congrArg some ?_
  simp only [List.reverse_reverse, List.append_nil]
  change (⟨some (.inl tm.main), (tm.initialState, ((none : Option Sym), pay)),
    embedStacks tm (CallSlot ⊕ G) (callΓ G Γg)
      (Function.update (fun _ => []) tm.k₀ (xs.map eIn.symm))
      (callFrame G Γg xs dst [] g)⟩ : (callTM tm G Γg P eIn eOut p₀ cont).Cfg) = _
  rw [← initList_stk_eq_update]
  rfl

/-- The entry certificate, with its count written out. -/
def entryEvals (xs dst : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P)
    (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (callTM tm G Γg P eIn eOut p₀ cont).step
      (callCfg eIn eOut p₀ cont (some (.inr .entry1)) v temp pay (fun _ => []) xs dst [] g)
      (some (embedCfg (F := CallSlot ⊕ G) (Γf := callΓ G Γg) CallLabel.ret
        ((none, pay) : CallState P) (callFrame G Γg xs dst [] g)
        (initList tm (xs.map eIn.symm)))) (2 * xs.length + 2) where
  steps := 2 * xs.length + 2
  evals_in_steps := entry_trace eIn eOut p₀ cont xs dst v temp pay g
  steps_le_m := le_refl _

@[simp] theorem entryEvals_steps (xs dst : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P)
    (g : ∀ j : G, List (Γg j)) :
    (entryEvals eIn eOut p₀ cont xs dst v temp pay g).steps = 2 * xs.length + 2 := rfl

end Entry

/-! ## Return: move the output out and leave every callee stack empty -/

/-- The halting stacks, as an update of the empty family.  Works whether or not `k₀ = k₁`. -/
theorem haltList_stk_eq_update (tm : FinTM2) (o : List (tm.Γ tm.k₁)) :
    (haltList tm o).stk = Function.update (fun _ => []) tm.k₁ o := by
  funext k
  change (dite (k = tm.k₁) _ _) = _
  by_cases h : k = tm.k₁
  · subst h
    rw [dite_eq_left rfl, Function.update_self]
    rfl
  · rw [dite_eq_right h, Function.update_of_ne h]

section Return

variable (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym) (p₀ : P)
  (cont : CallLabel → Stmt (embedΓ tm (CallSlot ⊕ G) (callΓ G Γg)) (tm.Λ ⊕ CallLabel)
    (tm.σ × CallState P))

/-- **Conversion precedes storage.**  The popped symbol has the callee's own alphabet type; it is
mapped through `eOut` *before* it reaches the caller's `Option Sym` temporary, so nothing here
assumes the callee's output alphabet is literally `Sym`. -/
theorem call_step_ret_cons (v : tm.σ) (temp : Option Sym) (pay : P) (c : tm.Γ tm.k₁)
    (zs : List (tm.Γ tm.k₁)) (S : ∀ k, List (tm.Γ k)) (hS : S tm.k₁ = c :: zs)
    (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .ret)) v temp pay S inp dst scratch g)
      = some (callCfg eIn eOut p₀ cont (some (.inr .ret)) v none pay
          (Function.update S tm.k₁ zs) inp dst (eOut c :: scratch) g) := by
  simp only [FinTM2.step, callTM, parentTM, callProgram, callCfg, Turing.TM2.step,
    Turing.TM2.stepAux, embedStacks, hS, List.head?_cons, List.tail_cons,
    Option.map_some, Option.isSome_some, Bool.cond_true, Option.getD_some]
  refine congrArg some (congrArg (fun T => (⟨some (.inr .ret), (v, (none, pay)), T⟩ :
    (callTM tm G Γg P eIn eOut p₀ cont).Cfg)) ?_)
  funext i
  rcases i with k | (s | j)
  · by_cases h : k = tm.k₁
    · subst h; simp [Function.update, embedStacks]
    · simp [Function.update, embedStacks, h]
  · cases s <;> simp [Function.update, embedStacks, callFrame]
  · simp [Function.update, embedStacks, callFrame]

theorem call_step_ret_nil (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (hS : S tm.k₁ = []) (inp dst scratch : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .ret)) v temp pay S inp dst scratch g)
      = some (callCfg eIn eOut p₀ cont (some (.inr .return2)) v none pay S inp dst scratch g) := by
  simp only [FinTM2.step, callTM, parentTM, callProgram, callCfg, Turing.TM2.step,
    Turing.TM2.stepAux, embedStacks, hS, List.head?_nil, List.tail_nil,
    Option.map_none, Option.isSome_none, Bool.cond_false]
  refine congrArg some (congrArg (fun T => (⟨some (.inr .return2), (v, (none, pay)), T⟩ :
    (callTM tm G Γg P eIn eOut p₀ cont).Cfg)) ?_)
  funext i
  rcases i with k | (s | j)
  · by_cases h : k = tm.k₁
    · subst h; simp [Function.update, embedStacks, hS]
    · simp [Function.update, embedStacks, h]
  · cases s <;> simp [Function.update, embedStacks, callFrame]
  · simp [Function.update, embedStacks, callFrame]

theorem call_step_return2_cons (v : tm.σ) (temp : Option Sym) (pay : P) (c : Sym)
    (S : ∀ k, List (tm.Γ k)) (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .return2)) v temp pay S inp dst (c :: scratch) g)
      = some (callCfg eIn eOut p₀ cont (some (.inr .return2)) v none pay S inp (c :: dst)
          scratch g) := by
  simp only [FinTM2.step, callTM, parentTM, callProgram, callCfg, Turing.TM2.step,
    Turing.TM2.stepAux, embedStacks, callFrame, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  refine congrArg some (congrArg (fun T => (⟨some (.inr .return2), (v, (none, pay)), T⟩ :
    (callTM tm G Γg P eIn eOut p₀ cont).Cfg)) ?_)
  funext i
  rcases i with k | (s | j)
  · simp [Function.update, embedStacks]
  · cases s <;> simp [Function.update, embedStacks, callFrame]
  · simp [Function.update, embedStacks, callFrame]

/-- The second phase's empty exit reaches `resume` — the **boundary**, not a transfer phase.  The
caller's continuation has not run. -/
theorem call_step_return2_nil (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (inp dst : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .return2)) v temp pay S inp dst [] g)
      = some (callCfg eIn eOut p₀ cont (some (.inr .resume)) v none pay S inp dst [] g) := by
  simp only [FinTM2.step, callTM, parentTM, callProgram, callCfg, Turing.TM2.step,
    Turing.TM2.stepAux, embedStacks, callFrame, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  refine congrArg some (congrArg (fun T => (⟨some (.inr .resume), (v, (none, pay)), T⟩ :
    (callTM tm G Γg P eIn eOut p₀ cont).Cfg)) ?_)
  funext i
  rcases i with k | (s | j)
  · simp [Function.update, embedStacks]
  · cases s <;> simp [Function.update, embedStacks, callFrame]
  · simp [Function.update, embedStacks, callFrame]

/-- **Phase one empties the callee's output stack**, converting each symbol on the way out.  The
stack change is an update at `tm.k₁`; nothing relates `k₀` and `k₁`. -/
theorem return_phase_one : ∀ (zs : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[zs.length + 1]
        (some (callCfg eIn eOut p₀ cont (some (.inr .ret)) v temp pay
          (Function.update S tm.k₁ (zs.map eOut.symm)) inp dst scratch g))
      = some (callCfg eIn eOut p₀ cont (some (.inr .return2)) v none pay
          (Function.update S tm.k₁ []) inp dst (zs.reverse ++ scratch) g)
  | [], v, temp, pay, S, inp, dst, scratch, g => by
      change (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .ret)) v temp pay
          (Function.update S tm.k₁ []) inp dst scratch g) = _
      rw [call_step_ret_nil eIn eOut p₀ cont v temp pay _ (by simp) inp dst scratch g]
      simp
  | z :: zs, v, temp, pay, S, inp, dst, scratch, g => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[zs.length + 1]
        ((callTM tm G Γg P eIn eOut p₀ cont).step
          (callCfg eIn eOut p₀ cont (some (.inr .ret)) v temp pay
            (Function.update S tm.k₁ (eOut.symm z :: zs.map eOut.symm)) inp dst scratch g)) = _
      rw [call_step_ret_cons eIn eOut p₀ cont v temp pay (eOut.symm z) (zs.map eOut.symm) _
          (by simp) inp dst scratch g,
        Function.update_idem, Equiv.apply_symm_apply,
        return_phase_one zs v none pay S inp dst (z :: scratch) g]
      simp

theorem return_phase_two : ∀ (rs : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P)
    (S : ∀ k, List (tm.Γ k)) (inp dst : List Sym) (g : ∀ j : G, List (Γg j)),
    (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[rs.length + 1]
        (some (callCfg eIn eOut p₀ cont (some (.inr .return2)) v temp pay S inp dst rs g))
      = some (callCfg eIn eOut p₀ cont (some (.inr .resume)) v none pay S inp
          (rs.reverse ++ dst) [] g)
  | [], v, temp, pay, S, inp, dst, g => by
      change (callTM tm G Γg P eIn eOut p₀ cont).step
        (callCfg eIn eOut p₀ cont (some (.inr .return2)) v temp pay S inp dst [] g) = _
      rw [call_step_return2_nil]
      rfl
  | c :: rs, v, temp, pay, S, inp, dst, g => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[rs.length + 1]
        ((callTM tm G Γg P eIn eOut p₀ cont).step
          (callCfg eIn eOut p₀ cont (some (.inr .return2)) v temp pay S inp dst (c :: rs) g)) = _
      rw [call_step_return2_cons, return_phase_two rs v none pay S inp (c :: dst) g]
      simp

/-- The embedded halting configuration *is* the caller's return configuration. -/
theorem embedCfg_haltList (o : List (tm.Γ tm.k₁)) (pay : P) (inp dst scratch : List Sym)
    (g : ∀ j : G, List (Γg j)) :
    embedCfg (F := CallSlot ⊕ G) (Γf := callΓ G Γg) CallLabel.ret ((none, pay) : CallState P)
        (callFrame G Γg inp dst scratch g) (haltList tm o)
      = callCfg eIn eOut p₀ cont (some (.inr .ret)) tm.initialState none pay (haltList tm o).stk
          inp dst scratch g := rfl

/-- **The return equation.**  From the embedded `haltList`, exactly `2 * ys.length + 2` steps reach
the `resume` boundary with **every callee stack empty** — ready for another call — the caller's
input `xs` untouched, the output prepended to the destination in its original order, scratch empty,
the payload and unrelated frame preserved, and the continuation not yet run. -/
theorem return_trace (xs ys dst : List Sym) (pay : P) (g : ∀ j : G, List (Γg j)) :
    (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[2 * ys.length + 2]
        (some (embedCfg (F := CallSlot ⊕ G) (Γf := callΓ G Γg) CallLabel.ret
          ((none, pay) : CallState P) (callFrame G Γg xs dst [] g)
          (haltList tm (ys.map eOut.symm))))
      = some (callCfg eIn eOut p₀ cont (some (.inr .resume)) tm.initialState none pay
          (fun _ => []) xs (ys ++ dst) [] g) := by
  have hsplit : 2 * ys.length + 2 = (ys.reverse.length + 1) + (ys.length + 1) := by
    rw [List.length_reverse]; omega
  rw [embedCfg_haltList eIn eOut p₀ cont, haltList_stk_eq_update, hsplit,
    Function.iterate_add_apply,
    return_phase_one eIn eOut p₀ cont ys tm.initialState none pay (fun _ => []) xs dst [] g,
    List.append_nil,
    return_phase_two eIn eOut p₀ cont ys.reverse tm.initialState none pay
      (Function.update (fun _ => []) tm.k₁ []) xs dst g]
  simp

/-- The return certificate, with its count written out. -/
def returnEvals (xs ys dst : List Sym) (pay : P) (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (callTM tm G Γg P eIn eOut p₀ cont).step
      (embedCfg (F := CallSlot ⊕ G) (Γf := callΓ G Γg) CallLabel.ret
        ((none, pay) : CallState P) (callFrame G Γg xs dst [] g)
        (haltList tm (ys.map eOut.symm)))
      (some (callCfg eIn eOut p₀ cont (some (.inr .resume)) tm.initialState none pay
        (fun _ => []) xs (ys ++ dst) [] g)) (2 * ys.length + 2) where
  steps := 2 * ys.length + 2
  evals_in_steps := return_trace eIn eOut p₀ cont xs ys dst pay g
  steps_le_m := le_refl _

@[simp] theorem returnEvals_steps (xs ys dst : List Sym) (pay : P) (g : ∀ j : G, List (Γg j)) :
    (returnEvals eIn eOut p₀ cont xs ys dst pay g).steps = 2 * ys.length + 2 := rfl

/-! ## The complete call

Entry, the transported callee execution, and return — all under the **same** completed caller
program, with the source witness's **actual** alphabet equivalences on both sides. -/

/-- **The reusable call certificate.**  Its recorded count is
`(2 * xs.length + 2) + h.steps + (2 * ys.length + 2)`, and its bound is the same with the source's
own bound `m` in place of `h.steps`: the two are kept apart.  The endpoint leaves every callee stack
empty and every caller datum in place, so the machine is ready to be called again. -/
def callEvals {m : ℕ} (xs ys dst : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P)
    (g : ∀ j : G, List (Γg j))
    (h : TM2OutputsInTime tm (xs.map eIn.symm) (some (ys.map eOut.symm)) m) :
    EvalsToInTime (callTM tm G Γg P eIn eOut p₀ cont).step
      (callCfg eIn eOut p₀ cont (some (.inr .entry1)) v temp pay (fun _ => []) xs dst [] g)
      (some (callCfg eIn eOut p₀ cont (some (.inr .resume)) tm.initialState none pay
        (fun _ => []) xs (ys ++ dst) [] g))
      ((2 * xs.length + 2) + m + (2 * ys.length + 2)) where
  steps := (2 * xs.length + 2) + h.steps + (2 * ys.length + 2)
  evals_in_steps := by
    have hsplit : (2 * xs.length + 2) + h.steps + (2 * ys.length + 2)
        = (2 * ys.length + 2) + (h.steps + (2 * xs.length + 2)) := by omega
    rw [hsplit,
      Function.iterate_add_apply (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)
        (2 * ys.length + 2) (h.steps + (2 * xs.length + 2)),
      Function.iterate_add_apply (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)
        h.steps (2 * xs.length + 2),
      entry_trace eIn eOut p₀ cont xs dst v temp pay g]
    -- the middle leg is stated about `parentTM`; `callTM` unfolds to it, so compose by `congrArg`
    -- and `Eq.trans` rather than by syntactic rewriting
    refine Eq.trans (congrArg
      (fun c => (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ cont).step)^[2 * ys.length + 2] c)
      (iterate_embedCfg ((none, p₀) : CallState P) CallLabel.ret (callProgram eIn eOut cont)
        ((none, pay) : CallState P) (callFrame G Γg xs dst [] g) h.steps h.evals_in_steps)) ?_
    exact return_trace eIn eOut p₀ cont xs ys dst pay g
  steps_le_m := by have := h.steps_le_m; omega

@[simp] theorem callEvals_steps {m : ℕ} (xs ys dst : List Sym) (v : tm.σ) (temp : Option Sym)
    (pay : P) (g : ∀ j : G, List (Γg j))
    (h : TM2OutputsInTime tm (xs.map eIn.symm) (some (ys.map eOut.symm)) m) :
    (callEvals eIn eOut p₀ cont xs ys dst v temp pay g h).steps
      = (2 * xs.length + 2) + h.steps + (2 * ys.length + 2) := rfl

/-! ### The call budget

Built from the existing `outputPoly`, not a duplicate of it.  The push bound is the **source's**:
the output-size bound describes the *source* execution, and the parent's own caller statements have
nothing to do with it. -/

/-- The polynomial bounding one complete call, in the **encoded input length**. -/
noncomputable def callPoly (tm : FinTM2) (p : Polynomial ℕ) : Polynomial ℕ :=
  2 * Polynomial.X + p + 2 * outputPoly tm p + 4

@[simp] theorem callPoly_eval (tm : FinTM2) (p : Polynomial ℕ) (n : ℕ) :
    (callPoly tm p).eval n
      = 2 * n + p.eval n + 2 * (n + machinePushBound tm * p.eval n) + 4 := by
  simp [callPoly]

/-- The external output length, bounded by the source's own push bound.  Both equivalence maps
preserve length, so the external and internal tapes agree on it. -/
theorem call_output_length_le {m : ℕ} (xs ys : List Sym)
    (h : TM2OutputsInTime tm (xs.map eIn.symm) (some (ys.map eOut.symm)) m) :
    ys.length ≤ xs.length + machinePushBound tm * m := by
  simpa using output_length_le tm h

/-- **The call's bound, in terms of the input length and the source bound alone.**  Stated about the
bound `callEvals` actually carries. -/
theorem callEvals_bound_le {m : ℕ} (xs ys : List Sym)
    (h : TM2OutputsInTime tm (xs.map eIn.symm) (some (ys.map eOut.symm)) m) :
    (2 * xs.length + 2) + m + (2 * ys.length + 2)
      ≤ 4 * xs.length + (1 + 2 * machinePushBound tm) * m + 4 := by
  have hy := call_output_length_le eIn eOut xs ys h
  have hring : (1 + 2 * machinePushBound tm) * m = m + 2 * (machinePushBound tm * m) := by ring
  rw [hring]
  set c := machinePushBound tm * m with hc
  omega

/-! ### Calling again

Only `resume` dispatches to the continuation, so a continuation that jumps back to `entry1` turns
the call into a loop — and that jump is one counted step, charged explicitly. -/

/-- A continuation whose `resume` jumps straight back to `entry1`. -/
def loopCont : CallLabel → Stmt (embedΓ tm (CallSlot ⊕ G) (callΓ G Γg)) (tm.Λ ⊕ CallLabel)
    (tm.σ × CallState P) := fun _ => .goto (fun _ => .inr .entry1)

/-- The resume jump: **one** counted step, changing nothing but the label. -/
theorem call_step_resume (v : tm.σ) (temp : Option Sym) (pay : P) (S : ∀ k, List (tm.Γ k))
    (inp dst scratch : List Sym) (g : ∀ j : G, List (Γg j)) :
    (callTM tm G Γg P eIn eOut p₀ (loopCont)).step
        (callCfg eIn eOut p₀ (loopCont) (some (.inr .resume)) v temp pay S inp dst
          scratch g)
      = some (callCfg eIn eOut p₀ (loopCont) (some (.inr .entry1)) v temp pay S inp dst
          scratch g) := rfl

/-- **Two calls.**  The second call's precondition — every callee stack empty, scratch empty, the
caller's input still `xs` — is what the first call's cleanup established, not an extra hypothesis.
The destination accumulates. -/
def repeatEvals {m : ℕ} (xs ys dst : List Sym) (v : tm.σ) (temp : Option Sym) (pay : P)
    (g : ∀ j : G, List (Γg j))
    (h : TM2OutputsInTime tm (xs.map eIn.symm) (some (ys.map eOut.symm)) m) :
    EvalsToInTime (callTM tm G Γg P eIn eOut p₀ (loopCont)).step
      (callCfg eIn eOut p₀ (loopCont) (some (.inr .entry1)) v temp pay (fun _ => []) xs
        dst [] g)
      (some (callCfg eIn eOut p₀ (loopCont) (some (.inr .resume)) tm.initialState none
        pay (fun _ => []) xs (ys ++ (ys ++ dst)) [] g))
      (((2 * xs.length + 2) + m + (2 * ys.length + 2)) + 1
        + ((2 * xs.length + 2) + m + (2 * ys.length + 2))) where
  steps := ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2)) + 1
    + ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2))
  evals_in_steps := by
    -- the two legs are stated at the certificates' own counts; restate them at the literal count so
    -- `rw` can match, then charge the resume jump between them
    have hfirst : (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ loopCont).step)^[
          (2 * xs.length + 2) + h.steps + (2 * ys.length + 2)]
          (some (callCfg eIn eOut p₀ loopCont (some (.inr .entry1)) v temp pay (fun _ => []) xs
            dst [] g))
        = some (callCfg eIn eOut p₀ loopCont (some (.inr .resume)) tm.initialState none pay
            (fun _ => []) xs (ys ++ dst) [] g) :=
      (callEvals eIn eOut p₀ loopCont xs ys dst v temp pay g h).evals_in_steps
    have hsecond : (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ loopCont).step)^[
          (2 * xs.length + 2) + h.steps + (2 * ys.length + 2)]
          (some (callCfg eIn eOut p₀ loopCont (some (.inr .entry1)) tm.initialState none pay
            (fun _ => []) xs (ys ++ dst) [] g))
        = some (callCfg eIn eOut p₀ loopCont (some (.inr .resume)) tm.initialState none pay
            (fun _ => []) xs (ys ++ (ys ++ dst)) [] g) :=
      (callEvals eIn eOut p₀ loopCont xs ys (ys ++ dst) tm.initialState none pay g h).evals_in_steps
    have hsplit : ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2)) + 1
        + ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2))
        = ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2))
          + (1 + ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2))) := by omega
    rw [hsplit,
      Function.iterate_add_apply (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ loopCont).step)
        ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2))
        (1 + ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2))),
      Function.iterate_add_apply (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ loopCont).step) 1
        ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2)),
      hfirst, Function.iterate_one]
    change (flip Bind.bind (callTM tm G Γg P eIn eOut p₀ loopCont).step)^[
        (2 * xs.length + 2) + h.steps + (2 * ys.length + 2)]
      ((callTM tm G Γg P eIn eOut p₀ loopCont).step
        (callCfg eIn eOut p₀ loopCont (some (.inr .resume)) tm.initialState none pay
          (fun _ => []) xs (ys ++ dst) [] g)) = _
    rw [call_step_resume]
    exact hsecond
  steps_le_m := by have := h.steps_le_m; omega

@[simp] theorem repeatEvals_steps {m : ℕ} (xs ys dst : List Sym) (v : tm.σ) (temp : Option Sym)
    (pay : P) (g : ∀ j : G, List (Γg j))
    (h : TM2OutputsInTime tm (xs.map eIn.symm) (some (ys.map eOut.symm)) m) :
    (repeatEvals eIn eOut p₀ xs ys dst v temp pay g h).steps
      = ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2)) + 1
        + ((2 * xs.length + 2) + h.steps + (2 * ys.length + 2)) := rfl

end Return

end

/-! ## A polynomially bounded call

The bound is attached to the **actual** returned certificate: only `steps_le_m` is re-proved, so the
execution and the recorded count are untouched and the count projection stays directly usable.

What this is *not*: a `TM2ComputableInPolyTime` witness for the caller.  The parent's main label is
still the callee's, whole-machine cleanup has not been arranged, and caller storage is retained at
the endpoint.  Nor does it bound arbitrary frame data in terms of `ea a` — the subroutine simply
leaves such data alone. -/

section Budget

variable (G : Type) [DecidableEq G] [Fintype G] (Γg : G → Type) (P : Type) [Fintype P]
  {α β : Type} {ea : α → List Sym} {eb : β → List Sym} {f : α → β}

/-- A complete call on a polynomial-time witness, bounded by one polynomial in the encoded input
length. -/
noncomputable def callEvalsPoly (hw : TM2ComputableInPolyTime ea eb f) (p₀ : P)
    (cont : CallLabel → Stmt (embedΓ hw.tm (CallSlot ⊕ G) (callΓ G Γg)) (hw.tm.Λ ⊕ CallLabel)
      (hw.tm.σ × CallState P))
    (a : α) (dst : List Sym) (v : hw.tm.σ) (temp : Option Sym) (pay : P)
    (g : ∀ j : G, List (Γg j)) :
    EvalsToInTime (callTM hw.tm G Γg P hw.inputAlphabet hw.outputAlphabet p₀ cont).step
      (callCfg hw.inputAlphabet hw.outputAlphabet p₀ cont (some (.inr .entry1)) v temp pay
        (fun _ => []) (ea a) dst [] g)
      (some (callCfg hw.inputAlphabet hw.outputAlphabet p₀ cont (some (.inr .resume))
        hw.tm.initialState none pay (fun _ => []) (ea a) (eb (f a) ++ dst) [] g))
      ((callPoly hw.tm hw.time).eval (ea a).length) where
  toEvalsTo := (callEvals hw.inputAlphabet hw.outputAlphabet p₀ cont (ea a) (eb (f a)) dst v temp
    pay g (hw.outputsFun a)).toEvalsTo
  steps_le_m := by
    change (2 * (ea a).length + 2) + (hw.outputsFun a).steps + (2 * (eb (f a)).length + 2) ≤ _
    have h1 : (hw.outputsFun a).steps ≤ hw.time.eval (ea a).length := (hw.outputsFun a).steps_le_m
    have h2 : (eb (f a)).length
        ≤ (ea a).length + machinePushBound hw.tm * hw.time.eval (ea a).length := by
      simpa using encoded_output_length_le hw a
    rw [callPoly_eval]
    omega

@[simp] theorem callEvalsPoly_steps (hw : TM2ComputableInPolyTime ea eb f) (p₀ : P)
    (cont : CallLabel → Stmt (embedΓ hw.tm (CallSlot ⊕ G) (callΓ G Γg)) (hw.tm.Λ ⊕ CallLabel)
      (hw.tm.σ × CallState P))
    (a : α) (dst : List Sym) (v : hw.tm.σ) (temp : Option Sym) (pay : P)
    (g : ∀ j : G, List (Γg j)) :
    (callEvalsPoly G Γg P hw p₀ cont a dst v temp pay g).steps
      = (2 * (ea a).length + 2) + (hw.outputsFun a).steps + (2 * (eb (f a)).length + 2) := rfl

end Budget

end PCP.Machine
