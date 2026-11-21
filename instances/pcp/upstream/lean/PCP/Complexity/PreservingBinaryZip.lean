import PCP.Complexity.BinaryZipMachine

/-!
# Binary scans preserving their left input

Both operands are scanned in parallel. The left operand and emitted result are
materialized on separate scratch stacks and restored together. Thus the left
input is preserved, the right input is replaced by the result, both scratch
stacks are cleared, and caller tapes are untouched. This is the reusable scan
inside binary multiplication and division; it never stores a number in control.
-/

namespace PCP.Machine.PreservingBinaryZip

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

inductive Slot | left | right | save | result
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Slot where
  elems := {.left, .right, .save, .result}
  complete := by intro x; cases x <;> decide

variable (spec : BinaryZip.Spec) (F : Type) [DecidableEq F] [Fintype F]

/-- A finite optional emission, expanded into ordinary push and branch instructions. -/
def pushSome (k : Slot ⊕ F)
    (get : spec.State × Option Sym × Option Sym → Option Sym)
    (next : Stmt (fun _ : Slot ⊕ F => Sym) MovePhase
      (spec.State × Option Sym × Option Sym)) :
    Stmt (fun _ : Slot ⊕ F => Sym) MovePhase (spec.State × Option Sym × Option Sym) :=
  .branch (fun v => (get v).isSome) (.push k (fun v => (get v).getD .sep) next) next

/-- Scan and restore, with finite transducer state and two remembered cells only. -/
def machine : FinTM2 where
  K := Slot ⊕ F
  k₀ := .inl .right
  k₁ := .inl .right
  Γ := fun _ => Sym
  Γk₀Fin := inferInstance
  Λ := MovePhase
  main := .one
  σ := spec.State × Option Sym × Option Sym
  initialState := (spec.init, none, none)
  m := fun
    | .one =>
        .pop (.inl .left) (fun v o => (v.1, o, none)) <|
        .pop (.inl .right) (fun v o => (v.1, v.2.1, o)) <|
        .branch (fun v => v.2.1.isNone && v.2.2.isNone)
          (pushSome spec F (.inl .result) (fun v => spec.finish v.1)
            (.load (fun _ => (spec.init, none, none)) (.goto (fun _ => .two))))
          (pushSome spec F (.inl .save) (fun v => v.2.1)
            (pushSome spec F (.inl .result) (fun v => spec.emit v.1 v.2.1 v.2.2)
              (.load (fun v => (spec.next v.1 v.2.1 v.2.2, none, none))
                (.goto (fun _ => .one)))))
    | .two =>
        .pop (.inl .save) (fun _ o => (spec.init, o, none)) <|
        .pop (.inl .result) (fun v o => (v.1, v.2.1, o)) <|
        .branch (fun v => v.2.1.isNone && v.2.2.isNone)
          (.load (fun _ => (spec.init, none, none)) .halt)
          (pushSome spec F (.inl .left) (fun v => v.2.1)
            (pushSome spec F (.inl .right) (fun v => v.2.2)
              (.load (fun _ => (spec.init, none, none)) (.goto (fun _ => .two)))))

/-- Explicit work tapes and an arbitrary untouched caller frame. -/
def cfg (l : Option MovePhase) (s : spec.State)
    (left right save result : List Sym) (frame : F → List Sym) : (machine spec F).Cfg where
  l := l
  var := (s, none, none)
  stk := fun k => match k with
    | .inl .left => left
    | .inl .right => right
    | .inl .save => save
    | .inl .result => result
    | .inr j => frame j

variable {spec F}

/-- The streaming step physically saves the left cell alongside the emitted cell. -/
theorem step_one (s : spec.State) (xs ys save result : List Sym) (frame : F → List Sym)
    (h : xs ≠ [] ∨ ys ≠ []) :
    (machine spec F).step (cfg spec F (some .one) s xs ys save result frame) =
      some (cfg spec F (some .one) (spec.next s xs.head? ys.head?) xs.tail ys.tail
        (xs.head?.toList ++ save) ((spec.emit s xs.head? ys.head?).toList ++ result) frame) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at h
      | cons d ys =>
          cases he : spec.emit s none (some d) <;>
            dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          all_goals
            simp only [Function.update_of_ne
              (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
            dsimp only [List.head?, List.tail]
            simp only [he]
            dsimp only [Option.isNone, Option.isSome, Option.getD, Option.toList,
              Bool.false_and, Bool.true_and, List.append]
            refine congrArg some (congrArg (fun S =>
              (⟨some .one, (spec.next s none (some d), none, none), S⟩ :
                (machine spec F).Cfg)) ?_)
            funext k
            rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]
  | cons c xs =>
      cases ys with
      | nil =>
          cases he : spec.emit s (some c) none <;>
            dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          all_goals
            simp only [Function.update_of_ne
              (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
            dsimp only [List.head?, List.tail]
            simp only [he]
            dsimp only [Option.isNone, Option.isSome, Option.getD, Option.toList,
              Bool.false_and, Bool.true_and, List.append]
            refine congrArg some (congrArg (fun S =>
              (⟨some .one, (spec.next s (some c) none, none, none), S⟩ :
                (machine spec F).Cfg)) ?_)
            funext k
            rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]
      | cons d ys =>
          cases he : spec.emit s (some c) (some d) <;>
            dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          all_goals
            simp only [Function.update_of_ne
              (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
            dsimp only [List.head?, List.tail]
            simp only [he]
            dsimp only [Option.isNone, Option.isSome, Option.getD, Option.toList,
              Bool.false_and, Bool.true_and, List.append]
            refine congrArg some (congrArg (fun S =>
              (⟨some .one, (spec.next s (some c) (some d), none, none), S⟩ :
                (machine spec F).Cfg)) ?_)
            funext k
            rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

theorem step_one_nil (s : spec.State) (save result : List Sym) (frame : F → List Sym) :
    (machine spec F).step (cfg spec F (some .one) s [] [] save result frame) =
      some (cfg spec F (some .two) spec.init [] [] save
        ((spec.finish s).toList ++ result) frame) := by
  cases he : spec.finish s <;>
    dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
  all_goals
    simp only [Function.update_of_ne
      (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
    dsimp only [List.head?, List.tail]
    simp only [he]
    dsimp only [Option.isNone, Option.isSome, Option.getD, Option.toList,
      Bool.true_and, List.append]
    refine congrArg some (congrArg (fun S =>
      (⟨some .two, (spec.init, none, none), S⟩ : (machine spec F).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

/-- The restoring step returns one available cell to each destination. -/
theorem step_two (xs ys left right : List Sym) (frame : F → List Sym)
    (h : xs ≠ [] ∨ ys ≠ []) :
    (machine spec F).step (cfg spec F (some .two) spec.init left right xs ys frame) =
      some (cfg spec F (some .two) spec.init (xs.head?.toList ++ left)
        (ys.head?.toList ++ right) xs.tail ys.tail frame) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at h
      | cons d ys =>
          dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          refine congrArg some (congrArg (fun S =>
            (⟨some .two, (spec.init, none, none), S⟩ : (machine spec F).Cfg)) ?_)
          funext k
          rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]
  | cons c xs =>
      cases ys with
      | nil =>
          dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          refine congrArg some (congrArg (fun S =>
            (⟨some .two, (spec.init, none, none), S⟩ : (machine spec F).Cfg)) ?_)
          funext k
          rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]
      | cons d ys =>
          dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          refine congrArg some (congrArg (fun S =>
            (⟨some .two, (spec.init, none, none), S⟩ : (machine spec F).Cfg)) ?_)
          funext k
          rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

theorem step_two_nil (left right : List Sym) (frame : F → List Sym) :
    (machine spec F).step (cfg spec F (some .two) spec.init left right [] [] frame) =
      some (cfg spec F none spec.init left right [] [] frame) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
  refine congrArg some (congrArg (fun S =>
    (⟨none, (spec.init, none, none), S⟩ : (machine spec F).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

/-- Streaming saves the complete left word while accumulating the transducer output. -/
theorem phase_one (xs ys save result : List Sym) (s : spec.State) (frame : F → List Sym) :
    (flip Bind.bind (machine spec F).step)^[max xs.length ys.length + 1]
      (some (cfg spec F (some .one) s xs ys save result frame)) =
      some (cfg spec F (some .two) spec.init [] [] (xs.reverse ++ save)
        ((spec.output s xs ys).reverse ++ result) frame) := by
  induction xs generalizing ys s save result with
  | nil =>
      induction ys generalizing s save result with
      | nil =>
          change (machine spec F).step (cfg spec F (some .one) s [] [] save result frame) = _
          cases he : spec.finish s <;>
            simpa [BinaryZip.Spec.output, he] using step_one_nil s save result frame
      | cons d ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F).step)^[ys.length + 1]
            ((machine spec F).step (cfg spec F (some .one) s [] (d :: ys) save result frame)) = _
          rw [step_one s [] (d :: ys) save result frame (by simp)]
          simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
            Option.toList_none, List.nil_append]
          simp only [List.length_nil, Nat.zero_max] at ih
          rw [ih]
          cases he : spec.emit s none (some d) <;>
            simp [BinaryZip.Spec.output, he, List.append_assoc]
  | cons c xs ih =>
      cases ys with
      | nil =>
          simp only [List.length_nil, List.length_cons, Nat.max_zero]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F).step)^[xs.length + 1]
            ((machine spec F).step (cfg spec F (some .one) s (c :: xs) [] save result frame)) = _
          rw [step_one s (c :: xs) [] save result frame (by simp)]
          simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
            Option.toList_some, List.singleton_append]
          have hi := ih [] (c :: save) ((spec.emit s (some c) none).toList ++ result)
            (spec.next s (some c) none)
          simp only [List.length_nil, Nat.max_zero] at hi
          rw [hi]
          cases he : spec.emit s (some c) none <;>
            simp [BinaryZip.Spec.output, he, List.append_assoc]
      | cons d ys =>
          simp only [List.length_cons, max_add_add_right]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F).step)^[max xs.length ys.length + 1]
            ((machine spec F).step
              (cfg spec F (some .one) s (c :: xs) (d :: ys) save result frame)) = _
          rw [step_one s (c :: xs) (d :: ys) save result frame (by simp)]
          simp only [List.head?_cons, List.tail_cons, Option.toList_some, List.singleton_append]
          rw [ih]
          cases he : spec.emit s (some c) (some d) <;>
            simp [BinaryZip.Spec.output, he, List.append_assoc]

/-- Parallel restoration returns both words in their original order. -/
theorem phase_two (xs ys left right : List Sym) (frame : F → List Sym) :
    (flip Bind.bind (machine spec F).step)^[max xs.length ys.length + 1]
      (some (cfg spec F (some .two) spec.init left right xs ys frame)) =
      some (cfg spec F none spec.init (xs.reverse ++ left) (ys.reverse ++ right) [] [] frame) := by
  induction xs generalizing ys left right with
  | nil =>
      induction ys generalizing left right with
      | nil =>
          change (machine spec F).step (cfg spec F (some .two) spec.init left right [] [] frame) = _
          exact step_two_nil left right frame
      | cons d ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F).step)^[ys.length + 1]
            ((machine spec F).step
              (cfg spec F (some .two) spec.init left right [] (d :: ys) frame)) = _
          rw [step_two [] (d :: ys) left right frame (by simp)]
          simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
            Option.toList_none, Option.toList_some, List.nil_append, List.singleton_append]
          simp only [List.length_nil, Nat.zero_max] at ih
          rw [ih]
          simp
  | cons c xs ih =>
      cases ys with
      | nil =>
          simp only [List.length_nil, List.length_cons, Nat.max_zero]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F).step)^[xs.length + 1]
            ((machine spec F).step
              (cfg spec F (some .two) spec.init left right (c :: xs) [] frame)) = _
          rw [step_two (c :: xs) [] left right frame (by simp)]
          simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
            Option.toList_none, Option.toList_some, List.nil_append, List.singleton_append]
          have hi := ih [] (c :: left) right
          simp only [List.length_nil, Nat.max_zero] at hi
          rw [hi]
          simp
      | cons d ys =>
          simp only [List.length_cons, max_add_add_right]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F).step)^[max xs.length ys.length + 1]
            ((machine spec F).step
              (cfg spec F (some .two) spec.init left right (c :: xs) (d :: ys) frame)) = _
          rw [step_two (c :: xs) (d :: ys) left right frame (by simp)]
          simp only [List.head?_cons, List.tail_cons, Option.toList_some, List.singleton_append]
          rw [ih]
          simp

/-- Exact trace, including both materialization and restoration passes. -/
theorem trace (xs ys : List Sym) (frame : F → List Sym) :
    (flip Bind.bind (machine spec F).step)^[max xs.length ys.length +
        max xs.length (spec.output spec.init xs ys).length + 2]
      (some (cfg spec F (some .one) spec.init xs ys [] [] frame)) =
      some (cfg spec F none spec.init xs (spec.output spec.init xs ys) [] [] frame) := by
  have hsplit : max xs.length ys.length + max xs.length (spec.output spec.init xs ys).length + 2 =
      (max xs.reverse.length (spec.output spec.init xs ys).reverse.length + 1) +
        (max xs.length ys.length + 1) := by simp; omega
  rw [hsplit, Function.iterate_add_apply, phase_one, List.append_nil, List.append_nil, phase_two]
  simp

/-- A retained-input binary scan is linear in the longer input length. -/
def evals (xs ys : List Sym) (frame : F → List Sym) :
    EvalsToInTime (machine spec F).step (cfg spec F (some .one) spec.init xs ys [] [] frame)
      (some (cfg spec F none spec.init xs (spec.output spec.init xs ys) [] [] frame))
      (2 * max xs.length ys.length + 3) where
  steps := max xs.length ys.length + max xs.length (spec.output spec.init xs ys).length + 2
  evals_in_steps := trace xs ys frame
  steps_le_m := by have := spec.output_length_le xs ys spec.init; omega

end PCP.Machine.PreservingBinaryZip
