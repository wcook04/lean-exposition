import PCP.Complexity.Machine

/-!
# An order-preserving stack move that preserves its caller's data

The first machine primitive used by the finite-witness checker.

## Two interfaces, in this order

The move must preserve **arbitrary unrelated stack contents**, and `TM2OutputsInTime` cannot say
that: it fixes the endpoints to `initList` and `haltList`, and every non-output stack of a
`haltList` is empty, so a final configuration retaining a nonempty caller stack simply is not one.

So the general theorem comes first, as an `EvalsToInTime` between two explicitly described
configurations — which records the actual optional-step iteration and its count without forcing
either endpoint to be a whole-machine input or output.  The whole-machine certificate is then a
*specialization* of it to an empty frame.  Doing it the other way round would mean either weakening
cleanup or silently restricting every caller to empty storage.

## Layout

Stack indices are `MoveSlot ⊕ F`: three **pairwise distinct** work stacks and an arbitrary frame.
Distinctness is structural rather than a hypothesis, and the frame's alphabet family `Γf` is
arbitrary — untouched stacks need no coding instance, no finiteness, and no inhabitant.

## Counting

One `Turing.TM2.step` executes a whole statement tree up to the next `goto` or `halt`, so a
nonempty pop/push/reset/goto is **one** counted step, and so is each empty-stack test and phase
exit.  Each phase therefore costs `length + 1`, and the whole move `2 * length + 2`.  This counts
TM2 steps, not elementary constructor operations.

## What this is not

A standalone move that finishes with terminal label `none` while retaining its frame is a valid
endpoint for the general trace theorem, not necessarily a `haltList`.  Replacing that local
termination with a caller continuation is the call-and-return embedding, which is separate work.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-- The three work stacks. -/
inductive MoveSlot | src | scratch | dst
  deriving DecidableEq, Inhabited, Repr

instance : Fintype MoveSlot where
  elems := {MoveSlot.src, MoveSlot.scratch, MoveSlot.dst}
  complete := by intro x; cases x <;> decide

/-- The two phases: source → scratch, then scratch → destination. -/
inductive MovePhase | one | two
  deriving DecidableEq, Inhabited, Repr

instance : Fintype MovePhase where
  elems := {MovePhase.one, MovePhase.two}
  complete := by intro x; cases x <;> decide

section

variable (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)

/-- `Sym` on the work stacks, the caller's own alphabets on the frame. -/
def moveΓ : MoveSlot ⊕ F → Type
  | .inl _ => Sym
  | .inr j => Γf j

/-- The mover.  Each phase pops one symbol into the internal state, pushes it on the next stack,
resets the state and loops; on an empty pop it resets and moves on. -/
def moveTM : FinTM2 where
  K := MoveSlot ⊕ F
  k₀ := .inl .src
  k₁ := .inl .dst
  Γ := moveΓ F Γf
  Γk₀Fin := inferInstanceAs (Fintype Sym)
  Λ := MovePhase
  main := .one
  σ := Option Sym
  initialState := none
  m := fun
    | .one =>
        pop (.inl .src) (fun _ o => o) <|
          branch (fun v => v.isSome)
            (push (.inl .scratch) (fun v => v.getD Sym.sep)
              (load (fun _ => none) (goto (fun _ => .one))))
            (load (fun _ => none) (goto (fun _ => .two)))
    | .two =>
        pop (.inl .scratch) (fun _ o => o) <|
          branch (fun v => v.isSome)
            (push (.inl .dst) (fun v => v.getD Sym.sep)
              (load (fun _ => none) (goto (fun _ => .two))))
            (load (fun _ => none) halt)

/-- A configuration named by its four parts: the three work stacks and the caller's frame. -/
def moveCfg (l : Option MovePhase) (v : Option Sym) (src scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) : (moveTM F Γf).Cfg where
  l := l
  var := v
  stk := fun k =>
    match k with
    | .inl .src => src
    | .inl .scratch => scratch
    | .inl .dst => dst
    | .inr j => S j

variable {F Γf}

/-! ## One-step behaviour

The incoming internal state is **arbitrary** in each lemma, which is what exposes that `pop`
overwrites it; and every frame stack is arbitrary, which is what makes preservation visible. -/

theorem move_step_one_cons (v : Option Sym) (c : Sym) (src scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (moveTM F Γf).step (moveCfg F Γf (some .one) v (c :: src) scratch dst S)
      = some (moveCfg F Γf (some .one) none src (c :: scratch) dst S) := by
  simp only [FinTM2.step, moveTM, moveCfg, Turing.TM2.step, Turing.TM2.stepAux]
  refine congrArg some (congrArg (fun S => (⟨some .one, none, S⟩ : (moveTM F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update] <;> rfl

theorem move_step_one_nil (v : Option Sym) (scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (moveTM F Γf).step (moveCfg F Γf (some .one) v [] scratch dst S)
      = some (moveCfg F Γf (some .two) none [] scratch dst S) := by
  simp only [FinTM2.step, moveTM, moveCfg, Turing.TM2.step, Turing.TM2.stepAux]
  refine congrArg some (congrArg (fun S => (⟨some .two, none, S⟩ : (moveTM F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update] <;> rfl

theorem move_step_two_cons (v : Option Sym) (c : Sym) (src scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (moveTM F Γf).step (moveCfg F Γf (some .two) v src (c :: scratch) dst S)
      = some (moveCfg F Γf (some .two) none src scratch (c :: dst) S) := by
  simp only [FinTM2.step, moveTM, moveCfg, Turing.TM2.step, Turing.TM2.stepAux]
  refine congrArg some (congrArg (fun S => (⟨some .two, none, S⟩ : (moveTM F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update] <;> rfl

theorem move_step_two_nil (v : Option Sym) (src dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (moveTM F Γf).step (moveCfg F Γf (some .two) v src [] dst S)
      = some (moveCfg F Γf none none src [] dst S) := by
  simp only [FinTM2.step, moveTM, moveCfg, Turing.TM2.step, Turing.TM2.stepAux]
  refine congrArg some (congrArg (fun S => (⟨none, none, S⟩ : (moveTM F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update] <;> rfl

/-! ## The reverse-transfer invariant

Stated with an **arbitrary accumulator** on the destination, so the induction matches a head-first
pop followed by a push, and so preservation of the third work stack and of every frame stack is part
of the statement rather than recovered afterwards. -/

theorem move_phase_one : ∀ (xs scratch dst : List Sym) (v : Option Sym)
    (S : ∀ j : F, List (Γf j)),
    (flip Bind.bind (moveTM F Γf).step)^[xs.length + 1]
        (some (moveCfg F Γf (some .one) v xs scratch dst S))
      = some (moveCfg F Γf (some .two) none [] (xs.reverse ++ scratch) dst S)
  | [], scratch, dst, v, S => by
      change (moveTM F Γf).step (moveCfg F Γf (some .one) v [] scratch dst S) = _
      rw [move_step_one_nil]
      rfl
  | c :: xs, scratch, dst, v, S => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (moveTM F Γf).step)^[xs.length + 1]
        ((moveTM F Γf).step (moveCfg F Γf (some .one) v (c :: xs) scratch dst S)) = _
      rw [move_step_one_cons, move_phase_one xs (c :: scratch) dst none S]
      simp

theorem move_phase_two : ∀ (ys src dst : List Sym) (v : Option Sym)
    (S : ∀ j : F, List (Γf j)),
    (flip Bind.bind (moveTM F Γf).step)^[ys.length + 1]
        (some (moveCfg F Γf (some .two) v src ys dst S))
      = some (moveCfg F Γf none none src [] (ys.reverse ++ dst) S)
  | [], src, dst, v, S => by
      change (moveTM F Γf).step (moveCfg F Γf (some .two) v src [] dst S) = _
      rw [move_step_two_nil]
      rfl
  | c :: ys, src, dst, v, S => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (moveTM F Γf).step)^[ys.length + 1]
        ((moveTM F Γf).step (moveCfg F Γf (some .two) v src (c :: ys) dst S)) = _
      rw [move_step_two_cons, move_phase_two ys src (c :: dst) none S]
      simp

/-! ## The framed trace, and its certificate -/

/-- **The move, with an arbitrary caller frame.**  Source and scratch end empty, the internal state
is reset, the destination holds `xs` in its **original order**, and every frame stack is untouched.
-/
theorem move_trace (xs : List Sym) (S : ∀ j : F, List (Γf j)) :
    (flip Bind.bind (moveTM F Γf).step)^[2 * xs.length + 2]
        (some (moveCfg F Γf (some .one) none xs [] [] S))
      = some (moveCfg F Γf none none [] [] xs S) := by
  have hsplit : 2 * xs.length + 2 = (xs.reverse.length + 1) + (xs.length + 1) := by
    rw [List.length_reverse]; omega
  rw [hsplit, Function.iterate_add_apply, move_phase_one xs [] [] none S, List.append_nil,
    move_phase_two xs.reverse [] [] none S]
  simp

/-- The same, as an execution certificate with its count written out. -/
def moveEvals (xs : List Sym) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (moveTM F Γf).step (moveCfg F Γf (some .one) none xs [] [] S)
      (some (moveCfg F Γf none none [] [] xs S)) (2 * xs.length + 2) where
  steps := 2 * xs.length + 2
  evals_in_steps := move_trace xs S
  steps_le_m := le_refl _

@[simp] theorem moveEvals_steps (xs : List Sym) (S : ∀ j : F, List (Γf j)) :
    (moveEvals xs S).steps = 2 * xs.length + 2 := rfl

/-! ## The empty-frame specialization

Only now — with the framed theorem already proved — is the frame set to empty so the endpoints
become an `initList` and a `haltList`. -/

theorem moveTM_initList (xs : List Sym) :
    initList (moveTM F Γf) xs = moveCfg F Γf (some .one) none xs [] [] (fun _ => []) := by
  unfold initList moveCfg
  congr 1
  funext k
  rcases k with (_ | _ | _) | j <;> simp [moveTM] <;> rfl

theorem moveTM_haltList (ys : List Sym) :
    haltList (moveTM F Γf) ys = moveCfg F Γf none none [] [] ys (fun _ => []) := by
  unfold haltList moveCfg
  congr 1
  funext k
  rcases k with (_ | _ | _) | j <;> simp [moveTM] <;> rfl

/-- The whole-machine certificate: exact `initList` to exact `haltList`, every auxiliary stack
empty, the internal state restored, in `2 * |xs| + 2` steps. -/
def moveTM_outputs (xs : List Sym) :
    TM2OutputsInTime (moveTM F Γf) xs (some xs) (2 * xs.length + 2) where
  steps := 2 * xs.length + 2
  evals_in_steps := by
    rw [moveTM_initList]
    calc (flip Bind.bind (moveTM F Γf).step)^[2 * xs.length + 2]
          (some (moveCfg F Γf (some .one) none xs [] [] fun _ => []))
        = some (moveCfg F Γf none none [] [] xs fun _ => []) := move_trace xs _
      _ = Option.map (haltList (moveTM F Γf)) (some xs) :=
          congrArg some (moveTM_haltList xs).symm
  steps_le_m := le_refl _

@[simp] theorem moveTM_outputs_steps (xs : List Sym) :
    (moveTM_outputs (F := F) (Γf := Γf) xs).steps = 2 * xs.length + 2 := rfl

/-! ## As a polynomial-time witness -/

variable (F Γf)

/-- Named so `rw` can match it: `k₀` is only definitionally equal to its value. -/
def moveAlphabetIn : (moveTM F Γf).Γ (moveTM F Γf).k₀ ≃ Sym := Equiv.refl Sym

/-- The output side, separate because `k₀` and `k₁` are only definitionally equal to their values.
-/
def moveAlphabetOut : (moveTM F Γf).Γ (moveTM F Γf).k₁ ≃ Sym := Equiv.refl Sym

theorem map_moveAlphabetIn : ∀ l : List Sym, l.map (moveAlphabetIn F Γf).invFun = l
  | [] => rfl
  | c :: l => by rw [List.map_cons, map_moveAlphabetIn l]; rfl

theorem map_moveAlphabetOut : ∀ l : List Sym, l.map (moveAlphabetOut F Γf).invFun = l
  | [] => rfl
  | c :: l => by rw [List.map_cons, map_moveAlphabetOut l]; rfl

/-- The mover as a polynomial-time witness for the identity on raw tapes, with the linear
polynomial the step count actually achieves. -/
noncomputable def moveWitness :
    TM2ComputableInPolyTime (id : List Sym → List Sym) (id : List Sym → List Sym)
      (id : List Sym → List Sym) where
  tm := moveTM F Γf
  inputAlphabet := moveAlphabetIn F Γf
  outputAlphabet := moveAlphabetOut F Γf
  time := 2 * Polynomial.X + 2
  outputsFun s := by
    -- field-by-field with the count written out: rewriting the goal first would bury `steps`
    -- behind an `Eq.mpr` and break the projection below
    refine ⟨⟨2 * s.length + 2, ?_⟩, ?_⟩
    · have e1 : s.map (moveAlphabetIn F Γf).invFun = s := map_moveAlphabetIn F Γf s
      have e2 : s.map (moveAlphabetOut F Γf).invFun = s := map_moveAlphabetOut F Γf s
      calc (flip Bind.bind (moveTM F Γf).step)^[2 * s.length + 2]
            (some (initList (moveTM F Γf) (s.map (moveAlphabetIn F Γf).invFun)))
          = (flip Bind.bind (moveTM F Γf).step)^[2 * s.length + 2]
              (some (initList (moveTM F Γf) s)) := by rw [e1]
        _ = Option.map (haltList (moveTM F Γf)) (some s) := (moveTM_outputs s).evals_in_steps
        _ = Option.map (haltList (moveTM F Γf))
              (some (s.map (moveAlphabetOut F Γf).invFun)) :=
            congrArg (fun l => Option.map (haltList (moveTM F Γf)) (some l)) e2.symm
    · simp

/-- The count survives into the returned witness. -/
@[simp] theorem moveWitness_steps (s : List Sym) :
    ((moveWitness F Γf).outputsFun s).steps = 2 * s.length + 2 := rfl

@[simp] theorem moveWitness_time : (moveWitness F Γf).time = 2 * Polynomial.X + 2 := rfl

end

/-! ## Acceptance

Order, frame preservation, cleanup, and the actual returned witness. -/

section Acceptance

/-- A one-stack frame, so a nonempty unrelated stack can actually be exhibited. -/
abbrev Frame : Type := Unit

/-- **Empty input**: two steps, empty output, and **no default symbol inserted** — the empty branch
never invokes the push. -/
example (S : ∀ _ : Frame, List Sym) :
    (flip Bind.bind (moveTM Frame (fun _ => Sym)).step)^[2]
        (some (moveCfg Frame (fun _ => Sym) (some .one) none [] [] [] S))
      = some (moveCfg Frame (fun _ => Sym) none none [] [] [] S) := move_trace [] S

/-- A singleton. -/
example (S : ∀ _ : Frame, List Sym) :
    (flip Bind.bind (moveTM Frame (fun _ => Sym)).step)^[4]
        (some (moveCfg Frame (fun _ => Sym) (some .one) none [Sym.sep] [] [] S))
      = some (moveCfg Frame (fun _ => Sym) none none [] [] [Sym.sep] S) :=
  move_trace [Sym.sep] S

/-- **A non-palindrome**, which a single reversal would get wrong: it comes out in exactly the
order it went in. -/
example (S : ∀ _ : Frame, List Sym) :
    (flip Bind.bind (moveTM Frame (fun _ => Sym)).step)^[8]
        (some (moveCfg Frame (fun _ => Sym) (some .one) none
          [Sym.bit false, Sym.sep, Sym.bit true] [] [] S))
      = some (moveCfg Frame (fun _ => Sym) none none [] []
          [Sym.bit false, Sym.sep, Sym.bit true] S) :=
  move_trace [Sym.bit false, Sym.sep, Sym.bit true] S

/-- …and that really is a different list from its reverse, so the check has content. -/
example : [Sym.bit false, Sym.sep, Sym.bit true] ≠
    [Sym.bit false, Sym.sep, Sym.bit true].reverse := by decide

/-- **A nonempty unrelated stack survives.**  This is a property of the framed theorem; the
empty-frame specialization below cannot state it. -/
example : (flip Bind.bind (moveTM Frame (fun _ => Sym)).step)^[4]
      (some (moveCfg Frame (fun _ => Sym) (some .one) none [Sym.sep] [] []
        (fun _ => [Sym.bit true, Sym.sep])))
    = some (moveCfg Frame (fun _ => Sym) none none [] [] [Sym.sep]
        (fun _ => [Sym.bit true, Sym.sep])) :=
  move_trace [Sym.sep] _

/-! ### The returned whole-machine witness

Named once, so the checks below are about **that object** and not about a separately correct
construction it happens to be built from. -/

noncomputable def frameWitness :
    TM2ComputableInPolyTime (id : List Sym → List Sym) (id : List Sym → List Sym)
      (id : List Sym → List Sym) :=
  moveWitness Frame fun _ => Sym

/-- Its step count, at a non-palindrome. -/
example : (frameWitness.outputsFun [Sym.bit false, Sym.sep, Sym.bit true]).steps = 8 := rfl

/-- **Its endpoint equation**, stated with the witness's own machine, its own alphabet maps, and its
own recorded count: the exact `haltList`, state restored, every non-output stack empty. -/
example (xs : List Sym) :
    (flip Bind.bind frameWitness.tm.step)^[(frameWitness.outputsFun xs).steps]
        (some (initList frameWitness.tm (xs.map frameWitness.inputAlphabet.invFun)))
      = Option.map (haltList frameWitness.tm)
          (some (xs.map frameWitness.outputAlphabet.invFun)) :=
  (frameWitness.outputsFun xs).evals_in_steps

/-- And its polynomial is the one the count achieves. -/
example : frameWitness.time = 2 * Polynomial.X + 2 := rfl

end Acceptance


end PCP.Machine
