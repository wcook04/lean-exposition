import PCP.Complexity.FiniteTransducer

/-!
# Finite filtering from the high end of a materialized tape

The first pass reverses the input onto scratch. The second runs a finite-state
filter on scratch, pushing retained cells back into the original order. Thus it
can remove high zero padding from little-endian numerals. Both passes charge for
every consumed cell, even when that cell emits nothing. Caller tapes survive.
-/

namespace PCP.Machine.ReverseTransducer

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

section Machine

variable (spec : TransducerSpec) (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)

/-- A full reversal followed by a finite filtering pass. -/
def machine : FinTM2 where
  K := MoveSlot ⊕ F
  k₀ := .inl .src
  k₁ := .inl .dst
  Γ := moveΓ F Γf
  Γk₀Fin := inferInstanceAs (Fintype Sym)
  Λ := MovePhase
  main := .one
  σ := spec.State × Option Sym × Bool
  initialState := (spec.init, none, false)
  m := fun
    | .one =>
        pop (.inl .src) (fun _ o => (spec.init, o, o.isNone)) <|
          branch (fun v => v.2.2)
            (load (fun _ => (spec.init, none, false)) (goto (fun _ => .two)))
            (push (.inl .scratch) (fun v => v.2.1.getD .sep)
              (load (fun _ => (spec.init, none, false)) (goto (fun _ => .one))))
    | .two =>
        pop (.inl .scratch) (fun v o => match o with
          | none => (spec.init, none, true)
          | some c => (spec.next v.1 c, spec.emit v.1 c, false)) <|
          branch (fun v => v.2.2)
            (load (fun _ => (spec.init, none, false)) halt)
            (branch (fun v => v.2.1.isSome)
              (push (.inl .dst) (fun v => v.2.1.getD .sep)
                (load (fun v => (v.1, none, false)) (goto (fun _ => .two))))
              (load (fun v => (v.1, none, false)) (goto (fun _ => .two))))

/-- Configuration exposing the materialized work tapes and arbitrary caller frame. -/
def cfg (l : Option MovePhase) (s : spec.State)
    (src scratch dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).Cfg where
  l := l
  var := (s, none, false)
  stk := fun k => match k with
    | .inl .src => src
    | .inl .scratch => scratch
    | .inl .dst => dst
    | .inr j => S j

variable {spec F Γf}

theorem step_one_cons (c : Sym) (xs scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step (cfg spec F Γf (some .one) spec.init (c :: xs) scratch dst S) =
      some (cfg spec F Γf (some .one) spec.init xs (c :: scratch) dst S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, moveΓ]
  refine congrArg some (congrArg (fun S =>
    (⟨some .one, (spec.init, none, false), S⟩ : (machine spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update]

theorem step_one_nil (scratch dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step (cfg spec F Γf (some .one) spec.init [] scratch dst S) =
      some (cfg spec F Γf (some .two) spec.init [] scratch dst S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, moveΓ]
  refine congrArg some (congrArg (fun S =>
    (⟨some .two, (spec.init, none, false), S⟩ : (machine spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update]

theorem step_two_cons (s : spec.State) (c : Sym) (xs scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step (cfg spec F Γf (some .two) s xs (c :: scratch) dst S) =
      some (cfg spec F Γf (some .two) (spec.next s c)
        xs scratch ((spec.emit s c).toList ++ dst) S) := by
  cases he : spec.emit s c <;>
    dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, moveΓ]
  all_goals
    dsimp only [List.head?, List.tail]
    simp only [he]
    dsimp only [Option.isSome, Option.getD, Option.toList, List.append]
    refine congrArg some (congrArg (fun S =>
      (⟨some .two, (spec.next s c, none, false), S⟩ : (machine spec F Γf).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _) | j <;> simp [Function.update]

theorem step_two_nil (s : spec.State) (xs dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step (cfg spec F Γf (some .two) s xs [] dst S) =
      some (cfg spec F Γf none spec.init xs [] dst S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux, moveΓ]
  refine congrArg some (congrArg (fun S =>
    (⟨none, (spec.init, none, false), S⟩ : (machine spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update]

/-- Every source cell is physically transferred to scratch. -/
theorem phase_one : ∀ (xs scratch dst : List Sym) (S : ∀ j : F, List (Γf j)),
    (flip Bind.bind (machine spec F Γf).step)^[xs.length + 1]
        (some (cfg spec F Γf (some .one) spec.init xs scratch dst S)) =
      some (cfg spec F Γf (some .two) spec.init [] (xs.reverse ++ scratch) dst S)
  | [], scratch, dst, S => by
      change (machine spec F Γf).step (cfg spec F Γf (some .one) spec.init [] scratch dst S) = _
      simpa using step_one_nil scratch dst S
  | c :: xs, scratch, dst, S => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine spec F Γf).step)^[xs.length + 1]
        ((machine spec F Γf).step
          (cfg spec F Γf (some .one) spec.init (c :: xs) scratch dst S)) = _
      rw [step_one_cons, phase_one]
      simp

/-- Filtering consumes all scratch cells and returns reversed filtered output. -/
theorem phase_two : ∀ (ys src dst : List Sym) (s : spec.State) (S : ∀ j : F, List (Γf j)),
    (flip Bind.bind (machine spec F Γf).step)^[ys.length + 1]
        (some (cfg spec F Γf (some .two) s src ys dst S)) =
      some (cfg spec F Γf none spec.init src [] ((spec.output s ys).reverse ++ dst) S)
  | [], src, dst, s, S => by
      change (machine spec F Γf).step (cfg spec F Γf (some .two) s src [] dst S) = _
      simpa [TransducerSpec.output] using step_two_nil s src dst S
  | c :: ys, src, dst, s, S => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine spec F Γf).step)^[ys.length + 1]
        ((machine spec F Γf).step (cfg spec F Γf (some .two) s src (c :: ys) dst S)) = _
      rw [step_two_cons, phase_two]
      cases he : spec.emit s c <;> simp [TransducerSpec.output, he, List.append_assoc]

/-- Exact two-pass computation with arbitrary caller storage. -/
theorem trace (xs : List Sym) (S : ∀ j : F, List (Γf j)) :
    (flip Bind.bind (machine spec F Γf).step)^[2 * xs.length + 2]
        (some (cfg spec F Γf (some .one) spec.init xs [] [] S)) =
      some (cfg spec F Γf none spec.init [] [] (spec.output spec.init xs.reverse).reverse S) := by
  have hsplit : 2 * xs.length + 2 = xs.reverse.length + 1 + (xs.length + 1) := by simp; omega
  rw [hsplit, Function.iterate_add_apply, phase_one, List.append_nil, phase_two]
  simp

/-- Framed runtime certificate for filtering from the high end of a tape. -/
def evals (xs : List Sym) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (machine spec F Γf).step (cfg spec F Γf (some .one) spec.init xs [] [] S)
      (some (cfg spec F Γf none spec.init [] [] (spec.output spec.init xs.reverse).reverse S))
      (2 * xs.length + 2) where
  steps := 2 * xs.length + 2
  evals_in_steps := trace xs S
  steps_le_m := le_refl _

end Machine

end PCP.Machine.ReverseTransducer
