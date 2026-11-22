import PCP.Complexity.ReverseTransducer

/-!
# In-place finite filtering from the high end

One stack contains the input and receives the output. A disjoint scratch stack
holds its reversal during filtering. Both passes are actual traces, scratch is
cleared, and every caller stack is preserved. The time is exactly twice the
original materialized length plus two, including cells removed by the filter.
-/

namespace PCP.Machine.InPlaceReverseTransducer

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

variable (spec : TransducerSpec) (F : Type) [DecidableEq F] [Fintype F]

/-- Two physical work stacks suffice because the input is consumed before output begins. -/
def machine : FinTM2 where
  K := Bool ⊕ F
  k₀ := .inl false
  k₁ := .inl false
  Γ := fun _ => Sym
  Γk₀Fin := inferInstance
  Λ := MovePhase
  main := .one
  σ := spec.State × Option Sym × Bool
  initialState := (spec.init, none, false)
  m := fun
    | .one =>
        .pop (.inl false) (fun _ o => (spec.init, o, o.isNone)) <|
          .branch (fun v => v.2.2)
            (.load (fun _ => (spec.init, none, false)) (.goto (fun _ => .two)))
            (.push (.inl true) (fun v => v.2.1.getD .sep)
              (.load (fun _ => (spec.init, none, false)) (.goto (fun _ => .one))))
    | .two =>
        .pop (.inl true) (fun v o => match o with
          | none => (spec.init, none, true)
          | some c => (spec.next v.1 c, spec.emit v.1 c, false)) <|
          .branch (fun v => v.2.2)
            (.load (fun _ => (spec.init, none, false)) .halt)
            (.branch (fun v => v.2.1.isSome)
              (.push (.inl false) (fun v => v.2.1.getD .sep)
                (.load (fun v => (v.1, none, false)) (.goto (fun _ => .two))))
              (.load (fun v => (v.1, none, false)) (.goto (fun _ => .two))))

/-- Materialized value and scratch, with arbitrary untouched caller storage. -/
def cfg (l : Option MovePhase) (s : spec.State) (value scratch : List Sym)
    (frame : F → List Sym) : (machine spec F).Cfg where
  l := l
  var := (s, none, false)
  stk := fun k => match k with
    | .inl false => value
    | .inl true => scratch
    | .inr j => frame j

variable {spec F}

theorem step_one_cons (c : Sym) (xs scratch : List Sym) (frame : F → List Sym) :
    (machine spec F).step (cfg spec F (some .one) spec.init (c :: xs) scratch frame) =
      some (cfg spec F (some .one) spec.init xs (c :: scratch) frame) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun S =>
    (⟨some .one, (spec.init, none, false), S⟩ : (machine spec F).Cfg)) ?_)
  funext k
  rcases k with (_ | _) | j <;> simp [Function.update]

theorem step_one_nil (scratch : List Sym) (frame : F → List Sym) :
    (machine spec F).step (cfg spec F (some .one) spec.init [] scratch frame) =
      some (cfg spec F (some .two) spec.init [] scratch frame) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun S =>
    (⟨some .two, (spec.init, none, false), S⟩ : (machine spec F).Cfg)) ?_)
  funext k
  rcases k with (_ | _) | j <;> simp [Function.update]

theorem step_two_cons (s : spec.State) (c : Sym) (xs dst : List Sym) (frame : F → List Sym) :
    (machine spec F).step (cfg spec F (some .two) s dst (c :: xs) frame) =
      some (cfg spec F (some .two) (spec.next s c) ((spec.emit s c).toList ++ dst) xs frame) := by
  cases he : spec.emit s c <;>
    dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  all_goals
    dsimp only [List.head?, List.tail]
    simp only [he]
    dsimp only [Option.isSome, Option.getD, Option.toList, List.append]
    refine congrArg some (congrArg (fun S =>
      (⟨some .two, (spec.next s c, none, false), S⟩ : (machine spec F).Cfg)) ?_)
    funext k
    rcases k with (_ | _) | j <;> simp [Function.update]

theorem step_two_nil (s : spec.State) (dst : List Sym) (frame : F → List Sym) :
    (machine spec F).step (cfg spec F (some .two) s dst [] frame) =
      some (cfg spec F none spec.init dst [] frame) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun S =>
    (⟨none, (spec.init, none, false), S⟩ : (machine spec F).Cfg)) ?_)
  funext k
  rcases k with (_ | _) | j <;> simp [Function.update]

/-- Transfer every input cell to scratch before restoring any output. -/
theorem phase_one : ∀ (xs scratch : List Sym) (frame : F → List Sym),
    (flip Bind.bind (machine spec F).step)^[xs.length + 1]
      (some (cfg spec F (some .one) spec.init xs scratch frame)) =
      some (cfg spec F (some .two) spec.init [] (xs.reverse ++ scratch) frame)
  | [], scratch, frame => by
      change (machine spec F).step (cfg spec F (some .one) spec.init [] scratch frame) = _
      simpa using step_one_nil scratch frame
  | c :: xs, scratch, frame => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine spec F).step)^[xs.length + 1]
        ((machine spec F).step (cfg spec F (some .one) spec.init (c :: xs) scratch frame)) = _
      rw [step_one_cons, phase_one]
      simp

/-- Every scratch cell is consumed, including cells filtered out of the result. -/
theorem phase_two : ∀ (xs dst : List Sym) (s : spec.State) (frame : F → List Sym),
    (flip Bind.bind (machine spec F).step)^[xs.length + 1]
      (some (cfg spec F (some .two) s dst xs frame)) =
      some (cfg spec F none spec.init ((spec.output s xs).reverse ++ dst) [] frame)
  | [], dst, s, frame => by
      change (machine spec F).step (cfg spec F (some .two) s dst [] frame) = _
      simpa [TransducerSpec.output] using step_two_nil s dst frame
  | c :: xs, dst, s, frame => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine spec F).step)^[xs.length + 1]
        ((machine spec F).step (cfg spec F (some .two) s dst (c :: xs) frame)) = _
      rw [step_two_cons, phase_two]
      cases he : spec.emit s c <;> simp [TransducerSpec.output, he, List.append_assoc]

/-- Exact in-place filtering, with both tape passes charged. -/
theorem trace (xs : List Sym) (frame : F → List Sym) :
    (flip Bind.bind (machine spec F).step)^[2 * xs.length + 2]
      (some (cfg spec F (some .one) spec.init xs [] frame)) =
      some (cfg spec F none spec.init (spec.output spec.init xs.reverse).reverse [] frame) := by
  have hsplit : 2 * xs.length + 2 = xs.reverse.length + 1 + (xs.length + 1) := by simp; omega
  rw [hsplit, Function.iterate_add_apply, phase_one, List.append_nil, phase_two]
  simp

/-- Framed linear-time certificate, suitable for numeral normalization. -/
def evals (xs : List Sym) (frame : F → List Sym) :
    EvalsToInTime (machine spec F).step (cfg spec F (some .one) spec.init xs [] frame)
      (some (cfg spec F none spec.init (spec.output spec.init xs.reverse).reverse [] frame))
      (2 * xs.length + 2) where
  steps := 2 * xs.length + 2
  evals_in_steps := trace xs frame
  steps_le_m := le_rfl

end PCP.Machine.InPlaceReverseTransducer
