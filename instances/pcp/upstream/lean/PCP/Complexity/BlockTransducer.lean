import PCP.Complexity.FiniteTransducer

/-!
# Finite-state transducers emitting bounded blocks

The output block of a transition has a machine-fixed maximum length. Its pushes
are unrolled in the finite statement, so no unbounded data is stored in control.
The framed trace charges every consumed and emitted cell and restores output order.
-/

namespace PCP.Machine.BlockTransducer

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

abbrev Alphabet (F : Type) (Γf : F → Type) : MoveSlot ⊕ F → Type := fun k =>
  match k with
  | .inl _ => Sym
  | .inr j => Γf j

structure Spec where
  State : Type
  [stateFintype : Fintype State]
  init : State
  next : State → Sym → State
  emit : State → Sym → List Sym

attribute [instance] Spec.stateFintype

def Spec.output (spec : Spec) (s : spec.State) : List Sym → List Sym
  | [] => []
  | c :: xs => spec.emit s c ++ spec.output (spec.next s c) xs

def Spec.width (spec : Spec) : ℕ :=
  Finset.univ.sup (fun p : spec.State × Sym => (spec.emit p.1 p.2).length)

theorem Spec.emit_length_le (spec : Spec) (s : spec.State) (c : Sym) :
    (spec.emit s c).length ≤ spec.width := by
  exact Finset.le_sup (f := fun p : spec.State × Sym => (spec.emit p.1 p.2).length)
    (Finset.mem_univ (s, c))

theorem Spec.output_length_le (spec : Spec) :
    ∀ (xs : List Sym) (s : spec.State), (spec.output s xs).length ≤ spec.width * xs.length
  | [], _ => by simp [output]
  | c :: xs, s => by
      have h := spec.output_length_le xs (spec.next s c)
      have he := spec.emit_length_le s c
      simp only [output, List.length_append, List.length_cons]
      nlinarith

section Push

variable {F σ : Type} [DecidableEq F] (Γf : F → Type) {Λ : Type}

/-- A finite list of optional pushes, in output order. -/
def pushBlock (values : List (σ → Option Sym))
    (cont : Stmt (Alphabet F Γf) Λ σ) : Stmt (Alphabet F Γf) Λ σ :=
  match values with
  | [] => cont
  | f :: fs => branch (fun v => (f v).isSome)
      (push (.inl .scratch) (fun v => (f v).getD Sym.sep) (pushBlock fs cont))
      (pushBlock fs cont)

theorem stepAux_pushBlock (values : List (σ → Option Sym))
    (cont : Stmt (Alphabet F Γf) Λ σ) (v : σ) (S : ∀ k, List (Alphabet F Γf k)) :
    stepAux (pushBlock Γf values cont) v S =
      stepAux cont v (Function.update S (.inl .scratch)
        ((values.filterMap (fun f => f v)).reverse ++ S (.inl .scratch))) := by
  induction values generalizing S with
  | nil => simp [pushBlock]
  | cons f fs ih =>
    cases hf : f v with
    | none => simp [pushBlock, stepAux, hf, ih]
    | some c =>
      simp only [pushBlock, stepAux, hf, Option.isSome_some, Option.getD_some, Bool.cond_true, ih,
        List.filterMap_cons, List.reverse_cons, List.singleton_append, Function.update_self,
        Function.update_idem, List.append_assoc]

end Push

variable (spec : Spec) (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)

abbrev Control := spec.State × Option Sym × Bool

def emission (v : Control spec) : List Sym := spec.emit v.1 (v.2.1.getD Sym.sep)

def cells : List (Control spec → Option Sym) :=
  (List.range spec.width).map (fun i v => (emission spec v)[i]?)

private theorem filterMap_indices (l : List Sym) (n : ℕ) :
    (List.range n).filterMap (fun i => l[i]?) = l.take n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, ih]
    by_cases hn : n < l.length
    · rw [List.take_succ_eq_append_getElem hn]
      simp [List.getElem?_eq_getElem hn]
    · simp [List.getElem?_eq_none (by omega : l.length ≤ n),
        List.take_of_length_le (by omega : l.length ≤ n),
        List.take_of_length_le (by omega : l.length ≤ n + 1)]

theorem cells_output (v : Control spec) :
    (cells spec).filterMap (fun f => f v) = emission spec v := by
  rw [cells, List.filterMap_map]
  change ((List.range spec.width).filterMap (fun i => (emission spec v)[i]?)) = _
  rw [filterMap_indices]
  exact List.take_of_length_le (spec.emit_length_le v.1 (v.2.1.getD Sym.sep))

def machine : FinTM2 where
  K := MoveSlot ⊕ F
  k₀ := .inl .src
  k₁ := .inl .dst
  Γ := Alphabet F Γf
  Γk₀Fin := inferInstanceAs (Fintype Sym)
  Λ := MovePhase
  main := .one
  σ := Control spec
  initialState := (spec.init, none, false)
  m := fun
    | .one => pop (.inl .src) (fun v o => (v.1, o, o.isNone)) <|
        branch (fun v => v.2.2)
          (load (fun _ => (spec.init, none, false)) (goto (fun _ => .two)))
          (pushBlock Γf (cells spec)
            (load (fun v => (spec.next v.1 (v.2.1.getD Sym.sep), none, false))
              (goto (fun _ => .one))))
    | .two => pop (.inl .scratch) (fun _ o => (spec.init, o, o.isNone)) <|
        branch (fun v => v.2.2)
          (load (fun _ => (spec.init, none, false)) halt)
          (push (.inl .dst) (fun v => v.2.1.getD Sym.sep)
            (load (fun _ => (spec.init, none, false)) (goto (fun _ => .two))))

def config (l : Option MovePhase) (v : Control spec)
    (src scratch dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).Cfg where
  l := l
  var := v
  stk := fun k => match k with
    | .inl .src => src
    | .inl .scratch => scratch
    | .inl .dst => dst
    | .inr j => S j

variable {spec F Γf}

theorem step_one_cons (s : spec.State) (c : Sym) (xs scratch dst : List Sym)
    (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step
        (config spec F Γf (some .one) (s, none, false) (c :: xs) scratch dst S) =
      some (config spec F Γf (some .one) (spec.next s c, none, false)
        xs ((spec.emit s c).reverse ++ scratch) dst S) := by
  simp only [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  dsimp only [List.head?, List.tail, Option.isNone]
  simp only [Bool.cond_false]
  erw [stepAux_pushBlock]
  rw [cells_output]
  simp only [TM2.stepAux, emission, Option.getD_some]
  refine congrArg some (congrArg (fun S =>
    (⟨some .one, (spec.next s c, none, false), S⟩ : (machine spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update]

theorem step_one_nil (s : spec.State) (scratch dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step
        (config spec F Γf (some .one) (s, none, false) [] scratch dst S) =
      some (config spec F Γf (some .two) (spec.init, none, false) [] scratch dst S) := by
  simp only [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun S =>
    (⟨some .two, (spec.init, none, false), S⟩ : (machine spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update]

theorem step_two_cons (c : Sym) (src scratch dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step
        (config spec F Γf (some .two) (spec.init, none, false) src (c :: scratch) dst S) =
      some (config spec F Γf (some .two) (spec.init, none, false) src scratch (c :: dst) S) := by
  simp only [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun S =>
    (⟨some .two, (spec.init, none, false), S⟩ : (machine spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update]

theorem step_two_nil (src dst : List Sym) (S : ∀ j : F, List (Γf j)) :
    (machine spec F Γf).step
        (config spec F Γf (some .two) (spec.init, none, false) src [] dst S) =
      some (config spec F Γf none (spec.init, none, false) src [] dst S) := by
  simp only [FinTM2.step, machine, config, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun S =>
    (⟨none, (spec.init, none, false), S⟩ : (machine spec F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | j <;> simp [Function.update]

theorem phase_one : ∀ (xs scratch dst : List Sym) (s : spec.State) (S : ∀ j : F, List (Γf j)),
    (flip Bind.bind (machine spec F Γf).step)^[xs.length + 1]
        (some (config spec F Γf (some .one) (s, none, false) xs scratch dst S)) =
      some (config spec F Γf (some .two) (spec.init, none, false)
        [] ((spec.output s xs).reverse ++ scratch) dst S)
  | [], scratch, dst, s, S => by
      change (machine spec F Γf).step
        (config spec F Γf (some .one) (s, none, false) [] scratch dst S) = _
      simpa [Spec.output] using step_one_nil s scratch dst S
  | c :: xs, scratch, dst, s, S => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine spec F Γf).step)^[xs.length + 1]
        ((machine spec F Γf).step
          (config spec F Γf (some .one) (s, none, false) (c :: xs) scratch dst S)) = _
      rw [step_one_cons, phase_one]
      simp [Spec.output, List.reverse_append, List.append_assoc]

theorem phase_two : ∀ (ys src dst : List Sym) (S : ∀ j : F, List (Γf j)),
    (flip Bind.bind (machine spec F Γf).step)^[ys.length + 1]
        (some (config spec F Γf (some .two) (spec.init, none, false) src ys dst S)) =
      some (config spec F Γf none (spec.init, none, false) src [] (ys.reverse ++ dst) S)
  | [], src, dst, S => by
      change (machine spec F Γf).step
        (config spec F Γf (some .two) (spec.init, none, false) src [] dst S) = _
      simpa using step_two_nil src dst S
  | c :: ys, src, dst, S => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine spec F Γf).step)^[ys.length + 1]
        ((machine spec F Γf).step
          (config spec F Γf (some .two) (spec.init, none, false) src (c :: ys) dst S)) = _
      rw [step_two_cons, phase_two]
      simp

theorem trace (xs : List Sym) (S : ∀ j : F, List (Γf j)) :
    (flip Bind.bind (machine spec F Γf).step)^[xs.length + (spec.output spec.init xs).length + 2]
        (some (config spec F Γf (some .one) (spec.init, none, false) xs [] [] S)) =
      some (config spec F Γf none (spec.init, none, false) [] [] (spec.output spec.init xs) S) := by
  have hs : xs.length + (spec.output spec.init xs).length + 2 =
      (spec.output spec.init xs).reverse.length + 1 + (xs.length + 1) := by simp; omega
  rw [hs, Function.iterate_add_apply, phase_one, List.append_nil, phase_two]
  simp

def evals (xs : List Sym) (S : ∀ j : F, List (Γf j)) :
    EvalsToInTime (machine spec F Γf).step
      (config spec F Γf (some .one) (spec.init, none, false) xs [] [] S)
      (some (config spec F Γf none (spec.init, none, false) [] [] (spec.output spec.init xs) S))
      ((spec.width + 1) * xs.length + 2) where
  steps := xs.length + (spec.output spec.init xs).length + 2
  evals_in_steps := trace xs S
  steps_le_m := by have := spec.output_length_le xs spec.init; nlinarith

theorem initial_config (xs : List Sym) : initList (machine spec F Γf) xs =
    config spec F Γf (some .one) (spec.init, none, false) xs [] [] (fun _ => []) := by
  unfold initList config
  congr 1
  funext k
  rcases k with (_ | _ | _) | j <;> simp [machine]
  rfl

theorem terminal_config (ys : List Sym) : haltList (machine spec F Γf) ys =
    config spec F Γf none (spec.init, none, false) [] [] ys (fun _ => []) := by
  unfold haltList config
  congr 1
  funext k
  rcases k with (_ | _ | _) | j <;> simp [machine]
  rfl

def outputs (xs : List Sym) : TM2OutputsInTime (machine spec F Γf) xs
    (some (spec.output spec.init xs)) ((spec.width + 1) * xs.length + 2) where
  steps := xs.length + (spec.output spec.init xs).length + 2
  evals_in_steps := by
    rw [initial_config]
    exact (trace xs (fun _ => [])).trans (congrArg some (terminal_config _).symm)
  steps_le_m := by have := spec.output_length_le xs spec.init; nlinarith

variable (spec F Γf)

def alphabetIn : (machine spec F Γf).Γ (machine spec F Γf).k₀ ≃ Sym := Equiv.refl Sym

def alphabetOut : (machine spec F Γf).Γ (machine spec F Γf).k₁ ≃ Sym := Equiv.refl Sym

theorem map_alphabetIn : ∀ xs : List Sym, xs.map (alphabetIn spec F Γf).invFun = xs
  | [] => rfl
  | c :: xs => by rw [List.map_cons, map_alphabetIn xs]; rfl

theorem map_alphabetOut : ∀ xs : List Sym, xs.map (alphabetOut spec F Γf).invFun = xs
  | [] => rfl
  | c :: xs => by rw [List.map_cons, map_alphabetOut xs]; rfl

/-- A concrete linear-time certificate for each matched pair of public encodings. -/
noncomputable def computable {α β : Type} (ea : α → List Sym) (eb : β → List Sym)
    (f : α → β) (h : ∀ a, eb (f a) = spec.output spec.init (ea a)) :
    TM2ComputableInPolyTime ea eb f where
  tm := machine spec F Γf
  inputAlphabet := alphabetIn spec F Γf
  outputAlphabet := alphabetOut spec F Γf
  time := Polynomial.C (spec.width + 1) * Polynomial.X + 2
  outputsFun a := by
    rw [map_alphabetIn, map_alphabetOut, h a]
    refine ⟨(outputs (F := F) (Γf := Γf) (ea a)).toEvalsTo, ?_⟩
    simpa using (outputs (spec := spec) (F := F) (Γf := Γf) (ea a)).steps_le_m

end PCP.Machine.BlockTransducer
