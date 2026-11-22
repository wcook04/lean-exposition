import PCP.Complexity.BinaryZipMachine
import PCP.Complexity.ReverseTransducer

/-!
# Synchronous binary scans with finite output normalization

The first pass consumes two source tapes and emits reversed raw output onto
scratch. A second finite filter processes it from the high end while restoring
order. Both passes are actual machine traces with arbitrary caller storage.
-/

namespace PCP.Machine.FilteredZip

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition BinaryZip

section Machine

variable (spec : BinaryZip.Spec) (filter : TransducerSpec)
  (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)

/-- Two simultaneous reads followed by order-restoring output transfer. -/
def machine : FinTM2 where
  K := Slot ⊕ F
  k₀ := .inl .left
  k₁ := .inl .dst
  Γ := alphabet F Γf
  Γk₀Fin := inferInstanceAs (Fintype Sym)
  Λ := MovePhase
  main := .one
  σ := (spec.State × filter.State) × Option Sym × Option Sym
  initialState := ((spec.init, filter.init), none, none)
  m := fun
    | .one =>
        pop (.inl .left) (fun v o => (v.1, o, none)) <|
          pop (.inl .right) (fun v o => (v.1, v.2.1, o)) <|
            branch (fun v => v.2.1.isNone && v.2.2.isNone)
              (branch (fun v => (spec.finish v.1.1).isSome)
                (push (.inl .scratch) (fun v => (spec.finish v.1.1).getD .sep)
                  (load (fun _ => ((spec.init, filter.init), none, none)) (goto (fun _ => .two))))
                (load (fun _ => ((spec.init, filter.init), none, none)) (goto (fun _ => .two))))
              (branch (fun v => (spec.emit v.1.1 v.2.1 v.2.2).isSome)
                (push (.inl .scratch) (fun v => (spec.emit v.1.1 v.2.1 v.2.2).getD .sep)
                  (load (fun v => ((spec.next v.1.1 v.2.1 v.2.2, filter.init), none, none))
                    (goto (fun _ => .one))))
                (load (fun v => ((spec.next v.1.1 v.2.1 v.2.2, filter.init), none, none))
                  (goto (fun _ => .one))))
    | .two =>
        pop (.inl .scratch) (fun v o => match o with
          | none => ((spec.init, filter.init), none, some Sym.sep)
          | some c => ((spec.init, filter.next v.1.2 c), filter.emit v.1.2 c, none)) <|
          branch (fun v => v.2.2.isSome)
            (load (fun _ => ((spec.init, filter.init), none, none)) halt)
            (branch (fun v => v.2.1.isSome)
              (push (.inl .dst) (fun v => v.2.1.getD .sep)
                (load (fun v => (v.1, none, none)) (goto (fun _ => .two))))
              (load (fun v => (v.1, none, none)) (goto (fun _ => .two))))

/-- Named configuration exposing both input tapes and the untouched caller frame. -/
def cfg (l : Option MovePhase) (s : spec.State)
    (left right scratch dst : List Sym) (S : ∀ j : F, List (Γf j))
    (t : filter.State := filter.init) :
    (machine spec filter F Γf).Cfg where
  l := l
  var := ((s, t), none, none)
  stk := fun k => match k with
    | .inl .left => left
    | .inl .right => right
    | .inl .scratch => scratch
    | .inl .dst => dst
    | .inr j => S j

variable {spec filter F Γf}

/-- One streaming step consumes exactly the available heads. -/
theorem step_one (s : spec.State) (xs ys scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) (h : xs ≠ [] ∨ ys ≠ []) :
    (machine spec filter F Γf).step (cfg spec filter F Γf (some .one) s xs ys scratch dst S) =
      some (cfg spec filter F Γf (some .one) (spec.next s xs.head? ys.head?)
        xs.tail ys.tail ((spec.emit s xs.head? ys.head?).toList ++ scratch) dst S) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at h
      | cons d ys =>
          cases he : spec.emit s none (some d) <;>
            dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, alphabet]
          all_goals
            simp only [Function.update_of_ne
              (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
            dsimp only [List.head?, List.tail]
            simp only [he]
            dsimp only [Option.isNone, Option.isSome, Option.getD, Option.toList,
              Bool.false_and, Bool.true_and, List.append]
            refine congrArg some (congrArg (fun S =>
              (⟨some .one, ((spec.next s none (some d), filter.init), none, none), S⟩ :
                (machine spec filter F Γf).Cfg)) ?_)
            funext k
            rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]
  | cons c xs =>
      cases ys with
      | nil =>
          cases he : spec.emit s (some c) none <;>
            dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, alphabet]
          all_goals
            simp only [Function.update_of_ne
              (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
            dsimp only [List.head?, List.tail]
            simp only [he]
            dsimp only [Option.isNone, Option.isSome, Option.getD, Option.toList,
              Bool.false_and, Bool.true_and, List.append]
            refine congrArg some (congrArg (fun S =>
              (⟨some .one, ((spec.next s (some c) none, filter.init), none, none), S⟩ :
                (machine spec filter F Γf).Cfg)) ?_)
            funext k
            rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]
      | cons d ys =>
          cases he : spec.emit s (some c) (some d) <;>
            dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, alphabet]
          all_goals
            simp only [Function.update_of_ne
              (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
            dsimp only [List.head?, List.tail]
            simp only [he]
            dsimp only [Option.isNone, Option.isSome, Option.getD, Option.toList,
              Bool.false_and, Bool.true_and, List.append]
            refine congrArg some (congrArg (fun S =>
              (⟨some .one, ((spec.next s (some c) (some d), filter.init), none, none), S⟩ :
                (machine spec filter F Γf).Cfg)) ?_)
            funext k
            rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

/-- The terminal output cell is counted and materialized before restoring output order. -/
theorem step_one_nil (s : spec.State) (scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (machine spec filter F Γf).step (cfg spec filter F Γf (some .one) s [] [] scratch dst S) =
      some (cfg spec filter F Γf (some .two) spec.init [] []
        ((spec.finish s).toList ++ scratch) dst S) := by
  cases he : spec.finish s <;>
    dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, alphabet]
  all_goals
    simp only [Function.update_of_ne
      (show (Sum.inl Slot.right : Slot ⊕ F) ≠ .inl .left from by simp)]
    dsimp only [List.head?, List.tail]
    simp only [he]
    dsimp only [Option.isNone, Option.isSome, Option.getD, Option.toList,
      Bool.true_and, List.append]
    refine congrArg some (congrArg (fun S =>
      (⟨some .two, ((spec.init, filter.init), none, none), S⟩ : (machine spec filter F Γf).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

/-- Streaming takes one step per available pair and one terminal step. -/
theorem phase_one (xs ys scratch dst : List Sym) (s : spec.State)
    (S : ∀ j : F, List (Γf j)) :
    (flip Bind.bind (machine spec filter F Γf).step)^[max xs.length ys.length + 1]
        (some (cfg spec filter F Γf (some .one) s xs ys scratch dst S)) =
      some (cfg spec filter F Γf (some .two) spec.init [] []
        ((spec.output s xs ys).reverse ++ scratch) dst S) := by
  induction xs generalizing ys s scratch with
  | nil =>
      induction ys generalizing s scratch with
      | nil =>
          change (machine spec filter F Γf).step
            (cfg spec filter F Γf (some .one) s [] [] scratch dst S) = _
          cases he : spec.finish s <;>
            simpa [Spec.output, he] using step_one_nil s scratch dst S
      | cons d ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec filter F Γf).step)^[ys.length + 1]
            ((machine spec filter F Γf).step
              (cfg spec filter F Γf (some .one) s [] (d :: ys) scratch dst S)) = _
          rw [step_one s [] (d :: ys) scratch dst S (by simp)]
          simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons]
          simp only [List.length_nil, Nat.zero_max] at ih
          rw [ih]
          cases he : spec.emit s none (some d) <;>
            simp [Spec.output, he, List.append_assoc]
  | cons c xs ih =>
      cases ys with
      | nil =>
          simp only [List.length_nil, List.length_cons, Nat.max_zero]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec filter F Γf).step)^[xs.length + 1]
            ((machine spec filter F Γf).step
              (cfg spec filter F Γf (some .one) s (c :: xs) [] scratch dst S)) = _
          rw [step_one s (c :: xs) [] scratch dst S (by simp)]
          simp only [List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons]
          have hi := ih [] ((spec.emit s (some c) none).toList ++ scratch)
            (spec.next s (some c) none)
          simp only [List.length_nil, Nat.max_zero] at hi
          rw [hi]
          cases he : spec.emit s (some c) none <;>
            simp [Spec.output, he, List.append_assoc]
      | cons d ys =>
          simp only [List.length_cons, max_add_add_right]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec filter F Γf).step)^[max xs.length ys.length + 1]
            ((machine spec filter F Γf).step
              (cfg spec filter F Γf (some .one) s (c :: xs) (d :: ys) scratch dst S)) = _
          rw [step_one s (c :: xs) (d :: ys) scratch dst S (by simp)]
          simp only [List.head?_cons, List.tail_cons]
          rw [ih]
          cases he : spec.emit s (some c) (some d) <;>
            simp [Spec.output, he, List.append_assoc]

/-- Filtering one raw output cell may either push it or discard it. -/
theorem step_two_cons (t : filter.State) (c : Sym) (xs ys scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (machine spec filter F Γf).step
        (cfg spec filter F Γf (some .two) spec.init xs ys (c :: scratch) dst S t) =
      some (cfg spec filter F Γf (some .two) spec.init xs ys scratch
        ((filter.emit t c).toList ++ dst) S (filter.next t c)) := by
  cases he : filter.emit t c <;>
    dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, alphabet]
  all_goals
    dsimp only [List.head?, List.tail]
    simp only [he]
    dsimp only [Option.isSome, Option.getD, Option.toList, List.append]
    refine congrArg some (congrArg (fun S =>
      (⟨some .two, ((spec.init, filter.next t c), none, none), S⟩ :
        (machine spec filter F Γf).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

theorem step_two_nil (t : filter.State) (xs ys dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (machine spec filter F Γf).step
        (cfg spec filter F Γf (some .two) spec.init xs ys [] dst S t) =
      some (cfg spec filter F Γf none spec.init xs ys [] dst S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, alphabet]
  refine congrArg some (congrArg (fun S =>
    (⟨none, ((spec.init, filter.init), none, none), S⟩ : (machine spec filter F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

/-- Every emitted raw cell is charged, including discarded padding or underflow markers. -/
theorem phase_two : ∀ (zs xs ys dst : List Sym) (t : filter.State)
    (S : ∀ j : F, List (Γf j)),
    (flip Bind.bind (machine spec filter F Γf).step)^[zs.length + 1]
        (some (cfg spec filter F Γf (some .two) spec.init xs ys zs dst S t)) =
      some (cfg spec filter F Γf none spec.init xs ys []
        ((filter.output t zs).reverse ++ dst) S)
  | [], xs, ys, dst, t, S => by
      change (machine spec filter F Γf).step
        (cfg spec filter F Γf (some .two) spec.init xs ys [] dst S t) = _
      simpa [TransducerSpec.output] using step_two_nil t xs ys dst S
  | c :: zs, xs, ys, dst, t, S => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine spec filter F Γf).step)^[zs.length + 1]
        ((machine spec filter F Γf).step
          (cfg spec filter F Γf (some .two) spec.init xs ys (c :: zs) dst S t)) = _
      rw [step_two_cons, phase_two]
      cases he : filter.emit t c <;> simp [TransducerSpec.output, he, List.append_assoc]

/-- Complete framed trace, including normalization and cleanup of both source tapes. -/
theorem trace (xs ys : List Sym) (S : ∀ j : F, List (Γf j)) :
    (flip Bind.bind (machine spec filter F Γf).step)^[
        max xs.length ys.length + (spec.output spec.init xs ys).length + 2]
        (some (cfg spec filter F Γf (some .one) spec.init xs ys [] [] S)) =
      some (cfg spec filter F Γf none spec.init [] [] []
        (filter.output filter.init (spec.output spec.init xs ys).reverse).reverse S) := by
  have hsplit : max xs.length ys.length + (spec.output spec.init xs ys).length + 2 =
      (spec.output spec.init xs ys).reverse.length + 1 + (max xs.length ys.length + 1) := by
    simp; omega
  rw [hsplit, Function.iterate_add_apply, phase_one, List.append_nil, phase_two]
  simp

/-- Uniform linear bound for a finite normalized two-input scan. -/
def evals (xs ys : List Sym) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (machine spec filter F Γf).step
      (cfg spec filter F Γf (some .one) spec.init xs ys [] [] S)
      (some (cfg spec filter F Γf none spec.init [] [] []
        (filter.output filter.init (spec.output spec.init xs ys).reverse).reverse S))
      (2 * max xs.length ys.length + 3) where
  steps := max xs.length ys.length + (spec.output spec.init xs ys).length + 2
  evals_in_steps := trace xs ys S
  steps_le_m := by have := spec.output_length_le xs ys spec.init; omega

end Machine

end PCP.Machine.FilteredZip
