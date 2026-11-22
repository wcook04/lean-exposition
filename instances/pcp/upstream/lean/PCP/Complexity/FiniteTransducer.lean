import PCP.Complexity.StackMove

/-!
# Linear-time finite-state tape transducers

A finite-state transducer reads each input symbol, updates its finite control and
emits either zero or one output symbol. The machine reverses the emitted symbols
onto a scratch stack, then transfers them to the output stack in input order.
The exact trace takes `input.length + output.length + 2` machine steps, preserves
arbitrary caller stacks, and empties both work stacks before terminating.

The final specialization extracts any one of the three verifier input arguments
from its actual separator encoding. Its concrete machine certificates follow
directly from the transducer traces and do not depend on the general composition
or compiler theorems.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

/-- A finite-state filter/map, with at most one emitted symbol per input cell. -/
structure TransducerSpec where
  /-- The finite control type. -/
  State : Type
  /-- Finite control is required by the machine model. -/
  [stateFintype : Fintype State]
  /-- Initial control state. -/
  init : State
  /-- Control transition on a consumed symbol. -/
  next : State → Sym → State
  /-- An optional output cell for a consumed symbol. -/
  emit : State → Sym → Option Sym

attribute [instance] TransducerSpec.stateFintype

/-- The output stream, with the initial control state supplied explicitly. -/
def TransducerSpec.output (spec : TransducerSpec) (s : spec.State) : List Sym → List Sym
  | [] => []
  | c :: xs => (spec.emit s c).toList ++ spec.output (spec.next s c) xs

theorem TransducerSpec.output_length_le (spec : TransducerSpec) :
    ∀ (xs : List Sym) (s : spec.State), (spec.output s xs).length ≤ xs.length
  | [], _ => by simp [output]
  | c :: xs, s => by
      have h := spec.output_length_le xs (spec.next s c)
      cases he : spec.emit s c <;> simp [output, he] at * <;> omega

section Machine

variable (spec : TransducerSpec) (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)

/-- A finite-state streaming phase followed by an order-restoring transfer. -/
def transducerTM : FinTM2 where
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
      pop (.inl .src) (fun v o => match o with
        | none => (v.1, none, true)
        | some c => (spec.next v.1 c, spec.emit v.1 c, false)) <|
        branch (fun v => v.2.2)
          (load (fun _ => (spec.init, none, false)) (goto (fun _ => .two)))
          (branch (fun v => v.2.1.isSome)
            (push (.inl .scratch) (fun v => v.2.1.getD Sym.sep)
              (load (fun v => (v.1, none, false)) (goto (fun _ => .one))))
            (load (fun v => (v.1, none, false)) (goto (fun _ => .one))))
    | .two =>
      pop (.inl .scratch) (fun _ o => (spec.init, o, o.isNone)) <|
        branch (fun v => v.2.2)
          (load (fun _ => (spec.init, none, false)) halt)
          (push (.inl .dst) (fun v => v.2.1.getD Sym.sep)
            (load (fun _ => (spec.init, none, false)) (goto (fun _ => .two))))

/-- Named configuration with arbitrary work-stack and caller contents. -/
def transducerCfg (l : Option MovePhase) (v : spec.State × Option Sym × Bool)
    (src scratch dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (transducerTM spec F Γf).Cfg where
  l := l
  var := v
  stk := fun k => match k with
    | .inl .src => src
    | .inl .scratch => scratch
    | .inl .dst => dst
    | .inr j => S j

variable {spec F Γf}

theorem transducer_step_one_cons (s : spec.State) (c : Sym) (xs scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (transducerTM spec F Γf).step
        (transducerCfg spec F Γf (some .one) (s, none, false) (c :: xs) scratch dst S) =
      some (transducerCfg spec F Γf (some .one) (spec.next s c, none, false)
        xs ((spec.emit s c).toList ++ scratch) dst S) := by
  cases he : spec.emit s c <;>
    simp only [FinTM2.step, transducerTM, transducerCfg, TM2.step, TM2.stepAux]
  all_goals
    dsimp only [List.head?, List.tail]
    simp only [he]
    dsimp only [Option.isSome, Option.getD, Option.toList, List.append]
    refine congrArg some (congrArg (fun S =>
      (⟨some .one, (spec.next s c, none, false), S⟩ : (transducerTM spec F Γf).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _) | j <;> simp [Function.update] <;> rfl

theorem transducer_step_one_nil (s : spec.State) (scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (transducerTM spec F Γf).step
        (transducerCfg spec F Γf (some .one) (s, none, false) [] scratch dst S) =
      some (transducerCfg spec F Γf (some .two) (spec.init, none, false) [] scratch dst S) := by
  simp only [FinTM2.step, transducerTM, transducerCfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun S =>
    (⟨some .two, (spec.init, none, false), S⟩ : (transducerTM spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update] <;> rfl

theorem transducer_step_two_cons (c : Sym) (src scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (transducerTM spec F Γf).step
        (transducerCfg spec F Γf (some .two) (spec.init, none, false)
          src (c :: scratch) dst S) =
      some (transducerCfg spec F Γf (some .two) (spec.init, none, false)
        src scratch (c :: dst) S) := by
  simp only [FinTM2.step, transducerTM, transducerCfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun S =>
    (⟨some .two, (spec.init, none, false), S⟩ : (transducerTM spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update] <;> rfl

theorem transducer_step_two_nil (src dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (transducerTM spec F Γf).step
        (transducerCfg spec F Γf (some .two) (spec.init, none, false) src [] dst S) =
      some (transducerCfg spec F Γf none (spec.init, none, false) src [] dst S) := by
  simp only [FinTM2.step, transducerTM, transducerCfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun S =>
    (⟨none, (spec.init, none, false), S⟩ : (transducerTM spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update] <;> rfl

/-- Streaming preserves the caller and accumulates the reversed output. -/
theorem transducer_phase_one : ∀ (xs scratch dst : List Sym) (s : spec.State)
    (S : ∀ j : F, List (Γf j)),
    (flip Bind.bind (transducerTM spec F Γf).step)^[xs.length + 1]
        (some (transducerCfg spec F Γf (some .one) (s, none, false) xs scratch dst S)) =
      some (transducerCfg spec F Γf (some .two) (spec.init, none, false)
        [] ((spec.output s xs).reverse ++ scratch) dst S)
  | [], scratch, dst, s, S => by
      change (transducerTM spec F Γf).step
        (transducerCfg spec F Γf (some .one) (s, none, false) [] scratch dst S) = _
      simpa [TransducerSpec.output] using transducer_step_one_nil s scratch dst S
  | c :: xs, scratch, dst, s, S => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (transducerTM spec F Γf).step)^[xs.length + 1]
        ((transducerTM spec F Γf).step
          (transducerCfg spec F Γf (some .one) (s, none, false) (c :: xs) scratch dst S)) = _
      rw [transducer_step_one_cons, transducer_phase_one]
      cases he : spec.emit s c <;> simp [TransducerSpec.output, he, List.append_assoc]

/-- The second pass restores output order and empties the scratch stack. -/
theorem transducer_phase_two : ∀ (ys src dst : List Sym) (S : ∀ j : F, List (Γf j)),
    (flip Bind.bind (transducerTM spec F Γf).step)^[ys.length + 1]
        (some (transducerCfg spec F Γf (some .two) (spec.init, none, false) src ys dst S)) =
      some (transducerCfg spec F Γf none (spec.init, none, false) src [] (ys.reverse ++ dst) S)
  | [], src, dst, S => by
      change (transducerTM spec F Γf).step
        (transducerCfg spec F Γf (some .two) (spec.init, none, false) src [] dst S) = _
      simpa using transducer_step_two_nil src dst S
  | c :: ys, src, dst, S => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (transducerTM spec F Γf).step)^[ys.length + 1]
        ((transducerTM spec F Γf).step
          (transducerCfg spec F Γf (some .two) (spec.init, none, false) src (c :: ys) dst S)) = _
      rw [transducer_step_two_cons, transducer_phase_two]
      simp

/-- Exact machine trace, including preservation of arbitrary caller storage. -/
theorem transducer_trace (xs : List Sym) (S : ∀ j : F, List (Γf j)) :
    (flip Bind.bind (transducerTM spec F Γf).step)^[
        xs.length + (spec.output spec.init xs).length + 2]
        (some (transducerCfg spec F Γf (some .one) (spec.init, none, false) xs [] [] S)) =
      some (transducerCfg spec F Γf none (spec.init, none, false)
        [] [] (spec.output spec.init xs) S) := by
  have hsplit : xs.length + (spec.output spec.init xs).length + 2 =
      (spec.output spec.init xs).reverse.length + 1 + (xs.length + 1) := by simp; omega
  rw [hsplit, Function.iterate_add_apply, transducer_phase_one, List.append_nil,
    transducer_phase_two]
  simp

/-- The framed trace packaged with a bound linear in the consumed input. -/
def transducerEvals (xs : List Sym) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (transducerTM spec F Γf).step
      (transducerCfg spec F Γf (some .one) (spec.init, none, false) xs [] [] S)
      (some (transducerCfg spec F Γf none (spec.init, none, false)
        [] [] (spec.output spec.init xs) S)) (2 * xs.length + 2) where
  steps := xs.length + (spec.output spec.init xs).length + 2
  evals_in_steps := transducer_trace xs S
  steps_le_m := by have := spec.output_length_le xs spec.init; omega

theorem transducer_initList (xs : List Sym) :
    initList (transducerTM spec F Γf) xs =
      transducerCfg spec F Γf (some .one) (spec.init, none, false) xs [] [] (fun _ => []) := by
  unfold initList transducerCfg
  congr 1
  funext k
  rcases k with (_ | _ | _) | j <;> simp [transducerTM] <;> rfl

theorem transducer_haltList (ys : List Sym) :
    haltList (transducerTM spec F Γf) ys =
      transducerCfg spec F Γf none (spec.init, none, false) [] [] ys (fun _ => []) := by
  unfold haltList transducerCfg
  congr 1
  funext k
  rcases k with (_ | _ | _) | j <;> simp [transducerTM] <;> rfl

/-- A whole-machine certificate with complete cleanup and no caller frame. -/
def transducer_outputs (xs : List Sym) :
    TM2OutputsInTime (transducerTM spec F Γf) xs
      (some (spec.output spec.init xs)) (2 * xs.length + 2) where
  steps := xs.length + (spec.output spec.init xs).length + 2
  evals_in_steps := by
    rw [transducer_initList]
    exact (transducer_trace xs (fun _ => [])).trans
      (congrArg some (transducer_haltList _).symm)
  steps_le_m := by have := spec.output_length_le xs spec.init; omega

variable (spec F Γf)

/-- Named input-alphabet identification for the dependent machine interface. -/
def transducerAlphabetIn :
    (transducerTM spec F Γf).Γ (transducerTM spec F Γf).k₀ ≃ Sym := Equiv.refl Sym

/-- Named output-alphabet identification for the dependent machine interface. -/
def transducerAlphabetOut :
    (transducerTM spec F Γf).Γ (transducerTM spec F Γf).k₁ ≃ Sym := Equiv.refl Sym

theorem map_transducerAlphabetIn :
    ∀ l : List Sym, l.map (transducerAlphabetIn spec F Γf).invFun = l
  | [] => rfl
  | c :: l => by rw [List.map_cons, map_transducerAlphabetIn l]; rfl

theorem map_transducerAlphabetOut :
    ∀ l : List Sym, l.map (transducerAlphabetOut spec F Γf).invFun = l
  | [] => rfl
  | c :: l => by rw [List.map_cons, map_transducerAlphabetOut l]; rfl

/-- A linear-time machine witness at any encodings matched by the transducer. -/
noncomputable def transducerComputable {α β : Type}
    (ea : α → List Sym) (eb : β → List Sym) (f : α → β)
    (h : ∀ a, eb (f a) = spec.output spec.init (ea a)) :
    TM2ComputableInPolyTime ea eb f where
  tm := transducerTM spec F Γf
  inputAlphabet := transducerAlphabetIn spec F Γf
  outputAlphabet := transducerAlphabetOut spec F Γf
  time := 2 * Polynomial.X + 2
  outputsFun a := by
    rw [map_transducerAlphabetIn, map_transducerAlphabetOut, h a]
    refine ⟨(transducer_outputs (F := F) (Γf := Γf) (ea a)).toEvalsTo, ?_⟩
    have hle := (transducer_outputs (spec := spec) (F := F) (Γf := Γf) (ea a)).steps_le_m
    simpa using hle

end Machine

end PCP.Machine
