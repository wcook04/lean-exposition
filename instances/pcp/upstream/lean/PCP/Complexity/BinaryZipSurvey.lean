import PCP.Complexity.PreservingBinaryZip
import PCP.Complexity.BinaryComparisonMachine

/-!
# Finite binary surveys preserving both operands

The machine reads both tapes in parallel, records only a finite transducer state,
then restores both words. The final finite state is retained for a caller branch.
Every actual cell movement is counted, with exact time twice the longer length
plus two. Unbounded values remain exclusively on the materialized tapes.
-/

namespace PCP.Machine.BinaryZipSurvey

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

open PreservingBinaryZip (Slot pushSome)

variable (spec : BinaryZip.Spec) (F : Type) [DecidableEq F] [Fintype F]

/-- The finite state after consuming both words, padding exhausted inputs by none. -/
def stateAfter (s : spec.State) : List Sym → List Sym → spec.State
  | [], [] => s
  | [], d :: ys => stateAfter (spec.next s none (some d)) [] ys
  | c :: xs, ys => stateAfter (spec.next s (some c) ys.head?) xs ys.tail
termination_by xs ys => xs.length + ys.length

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
          (.load (fun v => (v.1, none, none)) (.goto (fun _ => .two)))
          (pushSome spec F (.inl .save) (fun v => v.2.1)
            (pushSome spec F (.inl .result) (fun v => v.2.2)
              (.load (fun v => (spec.next v.1 v.2.1 v.2.2, none, none))
                (.goto (fun _ => .one)))))
    | .two =>
        .pop (.inl .save) (fun v o => (v.1, o, none)) <|
        .pop (.inl .result) (fun v o => (v.1, v.2.1, o)) <|
        .branch (fun v => v.2.1.isNone && v.2.2.isNone)
          (.load (fun v => (v.1, none, none)) .halt)
          (pushSome spec F (.inl .left) (fun v => v.2.1)
            (pushSome spec F (.inl .right) (fun v => v.2.2)
              (.load (fun v => (v.1, none, none)) (.goto (fun _ => .two)))))

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

/-- Streaming saves both cells while updating the finite survey state. -/
theorem step_one (s : spec.State) (xs ys save result : List Sym) (frame : F → List Sym)
    (h : xs ≠ [] ∨ ys ≠ []) :
    (machine spec F).step (cfg spec F (some .one) s xs ys save result frame) =
      some (cfg spec F (some .one) (spec.next s xs.head? ys.head?) xs.tail ys.tail
        (xs.head?.toList ++ save) (ys.head?.toList ++ result) frame) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at h
      | cons d ys =>
          dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          simp only [Function.update_of_ne
            (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
          dsimp only [List.head?, List.tail]
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
          dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          simp only [Function.update_of_ne
            (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
          dsimp only [List.head?, List.tail]
          dsimp only [Option.isNone, Option.isSome, Option.getD, Option.toList,
            Bool.false_and, Bool.true_and, List.append]
          refine congrArg some (congrArg (fun S =>
            (⟨some .one, (spec.next s (some c) none, none, none), S⟩ :
              (machine spec F).Cfg)) ?_)
          funext k
          rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]
      | cons d ys =>
          dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          simp only [Function.update_of_ne
            (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
          dsimp only [List.head?, List.tail]
          dsimp only [Option.isNone, Option.isSome, Option.getD, Option.toList,
            Bool.false_and, Bool.true_and, List.append]
          refine congrArg some (congrArg (fun S =>
            (⟨some .one, (spec.next s (some c) (some d), none, none), S⟩ :
              (machine spec F).Cfg)) ?_)
          funext k
          rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

theorem step_one_nil (s : spec.State) (save result : List Sym) (frame : F → List Sym) :
    (machine spec F).step (cfg spec F (some .one) s [] [] save result frame) =
      some (cfg spec F (some .two) s [] [] save result frame) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun S =>
    (⟨some .two, (s, none, none), S⟩ : (machine spec F).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

/-- The restoring step returns one available cell to each destination. -/
theorem step_two (s : spec.State) (xs ys left right : List Sym) (frame : F → List Sym)
    (h : xs ≠ [] ∨ ys ≠ []) :
    (machine spec F).step (cfg spec F (some .two) s left right xs ys frame) =
      some (cfg spec F (some .two) s (xs.head?.toList ++ left)
        (ys.head?.toList ++ right) xs.tail ys.tail frame) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at h
      | cons d ys =>
          dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          refine congrArg some (congrArg (fun S =>
            (⟨some .two, (s, none, none), S⟩ : (machine spec F).Cfg)) ?_)
          funext k
          rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]
  | cons c xs =>
      cases ys with
      | nil =>
          dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          refine congrArg some (congrArg (fun S =>
            (⟨some .two, (s, none, none), S⟩ : (machine spec F).Cfg)) ?_)
          funext k
          rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]
      | cons d ys =>
          dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
          refine congrArg some (congrArg (fun S =>
            (⟨some .two, (s, none, none), S⟩ : (machine spec F).Cfg)) ?_)
          funext k
          rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

theorem step_two_nil (s : spec.State) (left right : List Sym) (frame : F → List Sym) :
    (machine spec F).step (cfg spec F (some .two) s left right [] [] frame) =
      some (cfg spec F none s left right [] [] frame) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, pushSome]
  refine congrArg some (congrArg (fun S =>
    (⟨none, (s, none, none), S⟩ : (machine spec F).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

/-- Streaming saves the complete left word while accumulating the transducer output. -/
theorem phase_one (xs ys save result : List Sym) (s : spec.State) (frame : F → List Sym) :
    (flip Bind.bind (machine spec F).step)^[max xs.length ys.length + 1]
      (some (cfg spec F (some .one) s xs ys save result frame)) =
      some (cfg spec F (some .two) (stateAfter spec s xs ys) [] [] (xs.reverse ++ save)
        (ys.reverse ++ result) frame) := by
  induction xs generalizing ys s save result with
  | nil =>
      induction ys generalizing s save result with
      | nil =>
          change (machine spec F).step (cfg spec F (some .one) s [] [] save result frame) = _
          simpa only [stateAfter, List.reverse_nil, List.nil_append] using
            step_one_nil s save result frame
      | cons d ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F).step)^[ys.length + 1]
            ((machine spec F).step (cfg spec F (some .one) s [] (d :: ys) save result frame)) = _
          rw [step_one s [] (d :: ys) save result frame (by simp)]
          simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
            Option.toList_none, Option.toList_some, List.nil_append, List.singleton_append]
          simp only [List.length_nil, Nat.zero_max] at ih
          rw [ih]
          simp [stateAfter, List.append_assoc]
  | cons c xs ih =>
      cases ys with
      | nil =>
          simp only [List.length_nil, List.length_cons, Nat.max_zero]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F).step)^[xs.length + 1]
            ((machine spec F).step (cfg spec F (some .one) s (c :: xs) [] save result frame)) = _
          rw [step_one s (c :: xs) [] save result frame (by simp)]
          simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
            Option.toList_none, Option.toList_some, List.nil_append, List.singleton_append]
          have hi := ih [] (c :: save) result
            (spec.next s (some c) none)
          simp only [List.length_nil, Nat.max_zero] at hi
          rw [hi]
          simp [stateAfter, List.append_assoc]
      | cons d ys =>
          simp only [List.length_cons, max_add_add_right]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F).step)^[max xs.length ys.length + 1]
            ((machine spec F).step
              (cfg spec F (some .one) s (c :: xs) (d :: ys) save result frame)) = _
          rw [step_one s (c :: xs) (d :: ys) save result frame (by simp)]
          simp only [List.head?_cons, List.tail_cons, Option.toList_some, List.singleton_append]
          rw [ih]
          simp [stateAfter, List.append_assoc]

/-- Parallel restoration returns both words in their original order. -/
theorem phase_two (s : spec.State) (xs ys left right : List Sym) (frame : F → List Sym) :
    (flip Bind.bind (machine spec F).step)^[max xs.length ys.length + 1]
      (some (cfg spec F (some .two) s left right xs ys frame)) =
      some (cfg spec F none s (xs.reverse ++ left) (ys.reverse ++ right) [] [] frame) := by
  induction xs generalizing ys left right with
  | nil =>
      induction ys generalizing left right with
      | nil =>
          change (machine spec F).step (cfg spec F (some .two) s left right [] [] frame) = _
          exact step_two_nil s left right frame
      | cons d ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F).step)^[ys.length + 1]
            ((machine spec F).step
              (cfg spec F (some .two) s left right [] (d :: ys) frame)) = _
          rw [step_two s [] (d :: ys) left right frame (by simp)]
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
              (cfg spec F (some .two) s left right (c :: xs) [] frame)) = _
          rw [step_two s (c :: xs) [] left right frame (by simp)]
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
              (cfg spec F (some .two) s left right (c :: xs) (d :: ys) frame)) = _
          rw [step_two s (c :: xs) (d :: ys) left right frame (by simp)]
          simp only [List.head?_cons, List.tail_cons, Option.toList_some, List.singleton_append]
          rw [ih]
          simp

/-- Exact framed survey trace, retaining the final finite state and both inputs. -/
theorem trace (xs ys : List Sym) (s : spec.State) (frame : F → List Sym) :
    (flip Bind.bind (machine spec F).step)^[2 * max xs.length ys.length + 2]
      (some (cfg spec F (some .one) s xs ys [] [] frame)) =
      some (cfg spec F none (stateAfter spec s xs ys) xs ys [] [] frame) := by
  have hsplit : 2 * max xs.length ys.length + 2 =
      (max xs.reverse.length ys.reverse.length + 1) + (max xs.length ys.length + 1) := by
    simp; omega
  rw [hsplit, Function.iterate_add_apply, phase_one, List.append_nil, List.append_nil, phase_two]
  simp

/-- Surveying and restoring both operands takes linear time. -/
def evals (xs ys : List Sym) (s : spec.State) (frame : F → List Sym) :
    EvalsToInTime (machine spec F).step (cfg spec F (some .one) s xs ys [] [] frame)
      (some (cfg spec F none (stateAfter spec s xs ys) xs ys [] [] frame))
      (2 * max xs.length ys.length + 2) where
  steps := 2 * max xs.length ys.length + 2
  evals_in_steps := trace xs ys s frame
  steps_le_m := le_rfl


open BinaryComparison PCP.Lang

/-- A survey computes the complete comparison while retaining both operand tapes. -/
theorem comparison_state (accept : Ordering → Bool) (xs ys : List Bool) (state : Ordering) :
    stateAfter (BinaryComparison.spec accept) state (ofBits xs) (ofBits ys) =
      compareValue (bitsValue xs) (bitsValue ys) state := by
  induction xs generalizing ys state with
  | nil =>
      induction ys generalizing state with
      | nil => simp [stateAfter, ofBits, bitsValue, compareValue]
      | cons b ys ih =>
          change stateAfter (BinaryComparison.spec accept) state [] (ofBits (b :: ys)) = _
          change ∀ state, stateAfter (BinaryComparison.spec accept) state [] (ofBits ys) = _ at ih
          simp only [ofBits, List.map_cons, stateAfter, BinaryComparison.spec,
            BinaryComparison.readBit]
          change stateAfter (BinaryComparison.spec accept) (compareStep false b state)
            [] (ofBits ys) = _
          rw [ih]
          have he := compareValue_bit 0 (bitsValue ys) false b state
          simp only [Nat.bit_false, Nat.mul_zero] at he
          simp only [bitsValue_nil, bitsValue_cons]
          exact he
  | cons a xs ih =>
      cases ys with
      | nil =>
          change stateAfter (BinaryComparison.spec accept) state (ofBits (a :: xs)) [] = _
          simp only [ofBits, List.map_cons, stateAfter, BinaryComparison.spec,
            BinaryComparison.readBit, List.head?_nil, List.tail_nil]
          have hi := ih [] (compareStep a false state)
          change stateAfter (BinaryComparison.spec accept) (compareStep a false state)
            (ofBits xs) [] = _ at hi
          change stateAfter (BinaryComparison.spec accept) (compareStep a false state)
            (ofBits xs) [] = _
          rw [hi]
          have he := compareValue_bit (bitsValue xs) 0 a false state
          simp only [Nat.bit_false, Nat.mul_zero] at he
          simp only [bitsValue_nil, bitsValue_cons]
          exact he
      | cons b ys =>
          simp only [ofBits, List.map_cons, stateAfter, BinaryComparison.spec,
            BinaryComparison.readBit, List.head?_cons, List.tail_cons]
          change stateAfter (BinaryComparison.spec accept) (compareStep a b state)
            (ofBits xs) (ofBits ys) = _
          rw [ih]
          simp only [bitsValue_cons]
          exact compareValue_bit (bitsValue xs) (bitsValue ys) a b state

/-- Canonical natural operands give their ordinary three-way comparison in finite control. -/
theorem comparison_natTape (accept : Ordering → Bool) (n m : ℕ) :
    stateAfter (BinaryComparison.spec accept) .eq (natTape n) (natTape m) =
      compareValue n m .eq := by
  simpa only [natTape, bitsValue_binDigits] using
    comparison_state accept (binDigits n) (binDigits m) .eq

end PCP.Machine.BinaryZipSurvey
