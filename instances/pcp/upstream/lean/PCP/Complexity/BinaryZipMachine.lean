import PCP.Complexity.FinalTransducer

/-!
# Framed finite-control machines reading two binary tapes

The two source stacks are consumed synchronously, padding an exhausted source by
`none`. A finite transducer emits at most one cell per pair and one final cell.
All outputs are materialized and restored to low-bit-first order; arbitrary
caller stacks are preserved. This supports carry, borrow, and comparison scans
without storing either unbounded input number in finite control.
-/

namespace PCP.Machine.BinaryZip

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-- Four distinct work stacks; their separation does not depend on runtime data. -/
inductive Slot | left | right | scratch | dst
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Slot where
  elems := {.left, .right, .scratch, .dst}
  complete := by intro x; cases x <;> decide

/-- A finite synchronous transducer with optional terminal output. -/
structure Spec where
  /-- Bounded control only; input words stay on tapes. -/
  State : Type
  [stateFintype : Fintype State]
  init : State
  next : State → Option Sym → Option Sym → State
  emit : State → Option Sym → Option Sym → Option Sym
  finish : State → Option Sym

attribute [instance] Spec.stateFintype

/-- Stream semantics, consuming one cell from each nonempty source. -/
def Spec.output (spec : Spec) (s : spec.State) : List Sym → List Sym → List Sym
  | [], [] => (spec.finish s).toList
  | [], d :: ys => (spec.emit s none (some d)).toList ++
      spec.output (spec.next s none (some d)) [] ys
  | c :: xs, ys => (spec.emit s (some c) ys.head?).toList ++
      spec.output (spec.next s (some c) ys.head?) xs ys.tail
termination_by xs ys => xs.length + ys.length

/-- Emission increases the maximum input length by at most one cell. -/
theorem Spec.output_length_le (spec : Spec) (xs ys : List Sym) (s : spec.State) :
    (spec.output s xs ys).length ≤ max xs.length ys.length + 1 := by
  induction xs generalizing ys s with
  | nil =>
      induction ys generalizing s with
      | nil => cases spec.finish s <;> simp [output]
      | cons d ys ih =>
          have h := ih (spec.next s none (some d))
          cases he : spec.emit s none (some d) <;> simp [output, he] at * <;> omega
  | cons c xs ih =>
      cases ys with
      | nil =>
          have h := ih [] (spec.next s (some c) none)
          cases he : spec.emit s (some c) none <;> simp [output, he] at * <;> omega
      | cons d ys =>
          have h := ih ys (spec.next s (some c) (some d))
          cases he : spec.emit s (some c) (some d) <;>
            simp [output, he] at * <;> omega

section Machine

variable (spec : Spec) (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)

/-- The caller's alphabet family is unrestricted. -/
def alphabet : Slot ⊕ F → Type
  | .inl _ => Sym
  | .inr j => Γf j

/-- Two simultaneous reads followed by order-restoring output transfer. -/
def machine : FinTM2 where
  K := Slot ⊕ F
  k₀ := .inl .left
  k₁ := .inl .dst
  Γ := alphabet F Γf
  Γk₀Fin := inferInstanceAs (Fintype Sym)
  Λ := MovePhase
  main := .one
  σ := spec.State × Option Sym × Option Sym
  initialState := (spec.init, none, none)
  m := fun
    | .one =>
        pop (.inl .left) (fun v o => (v.1, o, none)) <|
          pop (.inl .right) (fun v o => (v.1, v.2.1, o)) <|
            branch (fun v => v.2.1.isNone && v.2.2.isNone)
              (branch (fun v => (spec.finish v.1).isSome)
                (push (.inl .scratch) (fun v => (spec.finish v.1).getD .sep)
                  (load (fun _ => (spec.init, none, none)) (goto (fun _ => .two))))
                (load (fun _ => (spec.init, none, none)) (goto (fun _ => .two))))
              (branch (fun v => (spec.emit v.1 v.2.1 v.2.2).isSome)
                (push (.inl .scratch) (fun v => (spec.emit v.1 v.2.1 v.2.2).getD .sep)
                  (load (fun v => (spec.next v.1 v.2.1 v.2.2, none, none))
                    (goto (fun _ => .one))))
                (load (fun v => (spec.next v.1 v.2.1 v.2.2, none, none))
                  (goto (fun _ => .one))))
    | .two =>
        pop (.inl .scratch) (fun _ o => (spec.init, o, none)) <|
          branch (fun v => v.2.1.isNone)
            (load (fun _ => (spec.init, none, none)) halt)
            (push (.inl .dst) (fun v => v.2.1.getD .sep)
              (load (fun _ => (spec.init, none, none)) (goto (fun _ => .two))))

/-- Named configuration exposing both input tapes and the untouched caller frame. -/
def cfg (l : Option MovePhase) (s : spec.State)
    (left right scratch dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).Cfg where
  l := l
  var := (s, none, none)
  stk := fun k => match k with
    | .inl .left => left
    | .inl .right => right
    | .inl .scratch => scratch
    | .inl .dst => dst
    | .inr j => S j

variable {spec F Γf}

/-- One streaming step consumes exactly the available heads. -/
theorem step_one (s : spec.State) (xs ys scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) (h : xs ≠ [] ∨ ys ≠ []) :
    (machine spec F Γf).step (cfg spec F Γf (some .one) s xs ys scratch dst S) =
      some (cfg spec F Γf (some .one) (spec.next s xs.head? ys.head?)
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
              (⟨some .one, (spec.next s none (some d), none, none), S⟩ :
                (machine spec F Γf).Cfg)) ?_)
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
              (⟨some .one, (spec.next s (some c) none, none, none), S⟩ :
                (machine spec F Γf).Cfg)) ?_)
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
              (⟨some .one, (spec.next s (some c) (some d), none, none), S⟩ :
                (machine spec F Γf).Cfg)) ?_)
            funext k
            rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

/-- The terminal output cell is counted and materialized before restoring output order. -/
theorem step_one_nil (s : spec.State) (scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step (cfg spec F Γf (some .one) s [] [] scratch dst S) =
      some (cfg spec F Γf (some .two) spec.init [] []
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
      (⟨some .two, (spec.init, none, none), S⟩ : (machine spec F Γf).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

theorem step_two_cons (c : Sym) (xs ys scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step
        (cfg spec F Γf (some .two) spec.init xs ys (c :: scratch) dst S) =
      some (cfg spec F Γf (some .two) spec.init xs ys scratch (c :: dst) S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, alphabet]
  refine congrArg some (congrArg (fun S =>
    (⟨some .two, (spec.init, none, none), S⟩ : (machine spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

theorem step_two_nil (xs ys dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step
        (cfg spec F Γf (some .two) spec.init xs ys [] dst S) =
      some (cfg spec F Γf none spec.init xs ys [] dst S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, alphabet]
  refine congrArg some (congrArg (fun S =>
    (⟨none, (spec.init, none, none), S⟩ : (machine spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | j <;> simp [Function.update]

/-- Streaming takes one step per available pair and one terminal step. -/
theorem phase_one (xs ys scratch dst : List Sym) (s : spec.State)
    (S : ∀ j : F, List (Γf j)) :
    (flip Bind.bind (machine spec F Γf).step)^[max xs.length ys.length + 1]
        (some (cfg spec F Γf (some .one) s xs ys scratch dst S)) =
      some (cfg spec F Γf (some .two) spec.init [] []
        ((spec.output s xs ys).reverse ++ scratch) dst S) := by
  induction xs generalizing ys s scratch with
  | nil =>
      induction ys generalizing s scratch with
      | nil =>
          change (machine spec F Γf).step
            (cfg spec F Γf (some .one) s [] [] scratch dst S) = _
          cases he : spec.finish s <;>
            simpa [Spec.output, he] using step_one_nil s scratch dst S
      | cons d ys ih =>
          simp only [List.length_nil, List.length_cons, Nat.zero_max]
          rw [Function.iterate_succ_apply]
          change (flip Bind.bind (machine spec F Γf).step)^[ys.length + 1]
            ((machine spec F Γf).step
              (cfg spec F Γf (some .one) s [] (d :: ys) scratch dst S)) = _
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
          change (flip Bind.bind (machine spec F Γf).step)^[xs.length + 1]
            ((machine spec F Γf).step
              (cfg spec F Γf (some .one) s (c :: xs) [] scratch dst S)) = _
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
          change (flip Bind.bind (machine spec F Γf).step)^[max xs.length ys.length + 1]
            ((machine spec F Γf).step
              (cfg spec F Γf (some .one) s (c :: xs) (d :: ys) scratch dst S)) = _
          rw [step_one s (c :: xs) (d :: ys) scratch dst S (by simp)]
          simp only [List.head?_cons, List.tail_cons]
          rw [ih]
          cases he : spec.emit s (some c) (some d) <;>
            simp [Spec.output, he, List.append_assoc]

/-- Restoring output order empties scratch and leaves caller tapes untouched. -/
theorem phase_two : ∀ (zs xs ys dst : List Sym) (S : ∀ j : F, List (Γf j)),
    (flip Bind.bind (machine spec F Γf).step)^[zs.length + 1]
        (some (cfg spec F Γf (some .two) spec.init xs ys zs dst S)) =
      some (cfg spec F Γf none spec.init xs ys [] (zs.reverse ++ dst) S)
  | [], xs, ys, dst, S => by
      change (machine spec F Γf).step
        (cfg spec F Γf (some .two) spec.init xs ys [] dst S) = _
      simpa using step_two_nil xs ys dst S
  | c :: zs, xs, ys, dst, S => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine spec F Γf).step)^[zs.length + 1]
        ((machine spec F Γf).step
          (cfg spec F Γf (some .two) spec.init xs ys (c :: zs) dst S)) = _
      rw [step_two_cons, phase_two]
      simp

/-- Exact framed trace for every pair of input tapes. -/
theorem trace (xs ys : List Sym) (S : ∀ j : F, List (Γf j)) :
    (flip Bind.bind (machine spec F Γf).step)^[
        max xs.length ys.length + (spec.output spec.init xs ys).length + 2]
        (some (cfg spec F Γf (some .one) spec.init xs ys [] [] S)) =
      some (cfg spec F Γf none spec.init [] [] [] (spec.output spec.init xs ys) S) := by
  have hsplit : max xs.length ys.length + (spec.output spec.init xs ys).length + 2 =
      (spec.output spec.init xs ys).reverse.length + 1 + (max xs.length ys.length + 1) := by
    simp; omega
  rw [hsplit, Function.iterate_add_apply, phase_one, List.append_nil, phase_two]
  simp

/-- The certified scan cost is linear in the longer materialized input. -/
def evals (xs ys : List Sym) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (machine spec F Γf).step
      (cfg spec F Γf (some .one) spec.init xs ys [] [] S)
      (some (cfg spec F Γf none spec.init [] [] [] (spec.output spec.init xs ys) S))
      (2 * max xs.length ys.length + 3) where
  steps := max xs.length ys.length + (spec.output spec.init xs ys).length + 2
  evals_in_steps := trace xs ys S
  steps_le_m := by have := spec.output_length_le xs ys spec.init; omega

end Machine

end PCP.Machine.BinaryZip
