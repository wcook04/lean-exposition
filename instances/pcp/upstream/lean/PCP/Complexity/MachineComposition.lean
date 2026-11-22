import PCP.Complexity.CallEntry

/-!
# Sequential composition of polynomial-time stack machines

The component machines run on disjoint stacks. Their intermediate tape is moved
through one scratch stack, translating through the given alphabet equivalences
and restoring its original order. This construction uses only finite control.
-/

namespace PCP.Machine

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition

attribute [local instance] FinTM2.kDecidableEq FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace Composition

variable (first second : FinTM2)

/-- Stack alphabets of the second machine together with the transfer scratch. -/
abbrev FrameΓ := embedΓ second Unit (fun _ => Sym)

/-- The composed machine's stack alphabets. -/
abbrev Alphabet := embedΓ first (second.K ⊕ Unit) (FrameΓ second)

/-- Both component controls and one temporary external symbol. -/
abbrev Control := first.σ × second.σ × Option Sym

/-- Component labels and the two transfer phases. -/
abbrev Label := first.Λ ⊕ second.Λ ⊕ Bool

/-- Stack families placed in their disjoint regions. -/
def combinedStacks (S₁ : ∀ k, List (first.Γ k)) (S₂ : ∀ k, List (second.Γ k))
    (scratch : List Sym) : ∀ k, List (Alphabet first second k) :=
  embedStacks first _ _ S₁ (embedStacks second Unit (fun _ => Sym) S₂ (fun _ => scratch))

theorem stacks_update_first (S₁ : ∀ k, List (first.Γ k))
    (S₂ : ∀ k, List (second.Γ k)) (scratch : List Sym) (k : first.K)
    (xs : List (first.Γ k)) :
    combinedStacks first second (Function.update S₁ k xs) S₂ scratch =
      Function.update (combinedStacks first second S₁ S₂ scratch) (.inl k) xs :=
  embedStacks_update S₁ _ k xs

theorem stacks_update_second (S₁ : ∀ k, List (first.Γ k))
    (S₂ : ∀ k, List (second.Γ k)) (scratch : List Sym) (k : second.K)
    (xs : List (second.Γ k)) :
    combinedStacks first second S₁ (Function.update S₂ k xs) scratch =
      Function.update (combinedStacks first second S₁ S₂ scratch) (.inr (.inl k)) xs := by
  unfold combinedStacks
  rw [embedStacks_update, embedStacks_update_frame]

/-- Embed the second machine's configuration, leaving the first region untouched. -/
def secondCfg (v₁ : first.σ) (temp : Option Sym)
    (S₁ : ∀ k, List (first.Γ k)) (scratch : List Sym) (c : second.Cfg) :
    Cfg (Alphabet first second) (Label first second) (Control first second) where
  l := c.l.map (fun l => .inr (.inl l))
  var := (v₁, c.var, temp)
  stk := combinedStacks first second S₁ c.stk scratch

/-- The second component terminates the composed machine when it halts. -/
def liftSecond : Stmt second.Γ second.Λ second.σ →
    Stmt (Alphabet first second) (Label first second) (Control first second)
  | .push k f q => .push (.inr (.inl k)) (fun v => f v.2.1) (liftSecond q)
  | .peek k f q => .peek (.inr (.inl k))
      (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftSecond q)
  | .pop k f q => .pop (.inr (.inl k))
      (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftSecond q)
  | .load f q => .load (fun v => (v.1, f v.2.1, v.2.2)) (liftSecond q)
  | .branch f q r => .branch (fun v => f v.2.1) (liftSecond q) (liftSecond r)
  | .goto f => .goto (fun v => .inr (.inl (f v.2.1)))
  | .halt => .halt

/-- Every second-component statement preserves the first region and the scratch. -/
theorem stepAux_liftSecond (v₁ : first.σ) (temp : Option Sym)
    (S₁ : ∀ k, List (first.Γ k)) (scratch : List Sym) :
    ∀ (q : Stmt second.Γ second.Λ second.σ) (v₂ : second.σ)
      (S₂ : ∀ k, List (second.Γ k)),
    stepAux (liftSecond first second q) (v₁, v₂, temp) (combinedStacks first second S₁ S₂ scratch) =
      secondCfg first second v₁ temp S₁ scratch (stepAux q v₂ S₂)
  | .push k f q, v₂, S₂ => by
      simp only [liftSecond, stepAux, ← stacks_update_second]
      exact stepAux_liftSecond v₁ temp S₁ scratch q v₂ _
  | .peek k f q, v₂, S₂ => by
      simp only [liftSecond, stepAux]
      exact stepAux_liftSecond v₁ temp S₁ scratch q _ S₂
  | .pop k f q, v₂, S₂ => by
      simp only [liftSecond, stepAux, ← stacks_update_second]
      exact stepAux_liftSecond v₁ temp S₁ scratch q _ _
  | .load f q, v₂, S₂ => by
      simp only [liftSecond, stepAux]
      exact stepAux_liftSecond v₁ temp S₁ scratch q _ S₂
  | .branch f q r, v₂, S₂ => by
      simp only [liftSecond, stepAux]
      cases f v₂
      · simpa using stepAux_liftSecond v₁ temp S₁ scratch r v₂ S₂
      · simpa using stepAux_liftSecond v₁ temp S₁ scratch q v₂ S₂
  | .goto f, v₂, S₂ => rfl
  | .halt, v₂, S₂ => rfl

variable (eOut : first.Γ first.k₁ ≃ Sym) (eIn : second.Γ second.k₀ ≃ Sym)

/-- The first output is reversed onto scratch, then restored onto the second input. -/
def caller : second.Λ ⊕ Bool →
    Stmt (Alphabet first second) (Label first second) (Control first second)
  | .inl l => liftSecond first second (second.m l)
  | .inr false =>
      pop (.inl first.k₁) (fun v o => (v.1, v.2.1, o.map eOut)) <|
        branch (fun v => v.2.2.isSome)
          (push (.inr (.inr ())) (fun v => v.2.2.getD Sym.sep)
            (load (fun v => (v.1, v.2.1, none)) (goto (fun _ => .inr (.inr false)))))
          (load (fun v => (v.1, v.2.1, none)) (goto (fun _ => .inr (.inr true))))
  | .inr true =>
      pop (.inr (.inr ())) (fun v o => (v.1, v.2.1, o)) <|
        branch (fun v => v.2.2.isSome)
          (push (.inr (.inl second.k₀)) (fun v => eIn.symm (v.2.2.getD Sym.sep))
            (load (fun v => (v.1, v.2.1, none)) (goto (fun _ => .inr (.inr true)))))
          (load (fun v => (v.1, second.initialState, none))
            (goto (fun _ => .inr (.inl second.main))))

/-- The composite has the first input and the second output as its external ports. -/
def machine : FinTM2 :=
  { parentTM first (second.K ⊕ Unit) (FrameΓ second) (second.initialState, none)
      (.inr false) (caller first second eOut eIn) with
    k₁ := .inr (.inl second.k₁) }

theorem second_step (v₁ : first.σ) (temp : Option Sym)
    (S₁ : ∀ k, List (first.Γ k)) (scratch : List Sym) (c : second.Cfg) :
    (machine first second eOut eIn).step (secondCfg first second v₁ temp S₁ scratch c) =
      (second.step c).map (secondCfg first second v₁ temp S₁ scratch) := by
  rcases c with ⟨l, v₂, S₂⟩
  cases l with
  | none => rfl
  | some l =>
      exact congrArg some (stepAux_liftSecond first second v₁ temp S₁ scratch (second.m l) v₂ S₂)

/-- The second computation runs at exactly its own recorded step count. -/
theorem second_iterate (v₁ : first.σ) (temp : Option Sym)
    (S₁ : ∀ k, List (first.Γ k)) (scratch : List Sym) (n : ℕ) (c : Option second.Cfg) :
    (flip Bind.bind (machine first second eOut eIn).step)^[n]
        (c.map (secondCfg first second v₁ temp S₁ scratch)) =
      ((flip Bind.bind second.step)^[n] c).map
        (secondCfg first second v₁ temp S₁ scratch) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases c with
      | none => exact ih none
      | some c =>
          change (flip Bind.bind (machine first second eOut eIn).step)^[n]
            ((machine first second eOut eIn).step
              (secondCfg first second v₁ temp S₁ scratch c)) = _
          rw [second_step]
          exact ih (second.step c)

/-- A configuration during one of the two intermediate-tape transfer phases. -/
def transferCfg (phase : Bool) (S₁ : ∀ k, List (first.Γ k))
    (S₂ : ∀ k, List (second.Γ k)) (scratch : List Sym) :
    (machine first second eOut eIn).Cfg where
  l := some (.inr (.inr phase))
  var := (first.initialState, second.initialState, none)
  stk := combinedStacks first second S₁ S₂ scratch

theorem transfer_one_cons (c : Sym) (xs scratch : List Sym)
    (S₂ : ∀ k, List (second.Γ k)) :
    (machine first second eOut eIn).step
        (transferCfg first second eOut eIn false
          (Function.update (fun _ => []) first.k₁ ((c :: xs).map eOut.symm)) S₂ scratch) =
      some (transferCfg first second eOut eIn false
        (Function.update (fun _ => []) first.k₁ (xs.map eOut.symm)) S₂ (c :: scratch)) := by
  simp only [FinTM2.step, machine, parentTM, caller, transferCfg, TM2.step, TM2.stepAux,
    combinedStacks, embedStacks, Function.update_self, List.map_cons, List.head?_cons,
    List.tail_cons, Option.map_some, Equiv.apply_symm_apply, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  refine congrArg some (congrArg (fun S =>
    (⟨some (.inr (.inr false)), (first.initialState, second.initialState, none), S⟩ :
      (machine first second eOut eIn).Cfg)) ?_)
  funext k
  rcases k with k | k | u
  · by_cases h : k = first.k₁
    · subst k; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]
  · cases u; simp [Function.update]

theorem transfer_one_nil (scratch : List Sym) (S₂ : ∀ k, List (second.Γ k)) :
    (machine first second eOut eIn).step
        (transferCfg first second eOut eIn false (fun _ => []) S₂ scratch) =
      some (transferCfg first second eOut eIn true (fun _ => []) S₂ scratch) := by
  simp only [FinTM2.step, machine, parentTM, caller, transferCfg, TM2.step, TM2.stepAux,
    combinedStacks, embedStacks]
  refine congrArg some (congrArg (fun S =>
    (⟨some (.inr (.inr true)), (first.initialState, second.initialState, none), S⟩ :
      (machine first second eOut eIn).Cfg)) ?_)
  funext k
  rcases k with k | k | u
  · by_cases h : k = first.k₁
    · subst k; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]
  · cases u; simp [Function.update]

theorem transfer_two_cons (c : Sym) (xs acc : List Sym) :
    (machine first second eOut eIn).step
        (transferCfg first second eOut eIn true (fun _ => [])
          (Function.update (fun _ => []) second.k₀ (acc.map eIn.symm)) (c :: xs)) =
      some (transferCfg first second eOut eIn true (fun _ => [])
        (Function.update (fun _ => []) second.k₀ ((c :: acc).map eIn.symm)) xs) := by
  simp only [FinTM2.step, machine, parentTM, caller, transferCfg, TM2.step, TM2.stepAux,
    combinedStacks, embedStacks]
  refine congrArg some (congrArg (fun S =>
    (⟨some (.inr (.inr true)), (first.initialState, second.initialState, none), S⟩ :
      (machine first second eOut eIn).Cfg)) ?_)
  funext k
  rcases k with k | k | u
  · simp [Function.update]
  · by_cases h : k = second.k₀
    · subst k; simp [Function.update]
    · simp [Function.update, h]
  · cases u; simp [Function.update]

theorem transfer_two_nil (acc : List Sym) :
    (machine first second eOut eIn).step
        (transferCfg first second eOut eIn true (fun _ => [])
          (Function.update (fun _ => []) second.k₀ (acc.map eIn.symm)) []) =
      some (secondCfg first second first.initialState none (fun _ => []) []
        (initList second (acc.map eIn.symm))) := by
  simp only [FinTM2.step, machine, parentTM, caller, transferCfg, TM2.step, TM2.stepAux,
    combinedStacks, embedStacks]
  refine congrArg some (congrArg (fun S =>
    (⟨some (.inr (.inl second.main)), (first.initialState, second.initialState, none), S⟩ :
      (machine first second eOut eIn).Cfg)) ?_)
  change _ = combinedStacks first second (fun _ => []) (initList second (acc.map eIn.symm)).stk []
  rw [initList_stk_eq_update]
  funext k
  rcases k with k | k | u
  · simp [combinedStacks, embedStacks, Function.update]
  · simp [combinedStacks, embedStacks, Function.update]
  · cases u; simp [combinedStacks, embedStacks, Function.update]

/-- The first transfer pass consumes the first output and reverses it onto scratch. -/
theorem transfer_phase_one : ∀ (xs scratch : List Sym) (S₂ : ∀ k, List (second.Γ k)),
    (flip Bind.bind (machine first second eOut eIn).step)^[xs.length + 1]
        (some (transferCfg first second eOut eIn false
          (Function.update (fun _ => []) first.k₁ (xs.map eOut.symm)) S₂ scratch)) =
      some (transferCfg first second eOut eIn true (fun _ => []) S₂ (xs.reverse ++ scratch))
  | [], scratch, S₂ => by
      simp only [List.map_nil, Function.update_eq_self, List.length_nil,
        zero_add, Function.iterate_one]
      change (machine first second eOut eIn).step
        (transferCfg first second eOut eIn false (fun _ => []) S₂ scratch) = _
      exact transfer_one_nil first second eOut eIn scratch S₂
  | c :: xs, scratch, S₂ => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine first second eOut eIn).step)^[xs.length + 1]
        ((machine first second eOut eIn).step
          (transferCfg first second eOut eIn false
            (Function.update (fun _ => []) first.k₁ ((c :: xs).map eOut.symm)) S₂ scratch)) = _
      rw [transfer_one_cons, transfer_phase_one]
      simp

/-- The second transfer pass restores the original order on the second input. -/
theorem transfer_phase_two : ∀ (xs acc : List Sym),
    (flip Bind.bind (machine first second eOut eIn).step)^[xs.length + 1]
        (some (transferCfg first second eOut eIn true (fun _ => [])
          (Function.update (fun _ => []) second.k₀ (acc.map eIn.symm)) xs)) =
      some (secondCfg first second first.initialState none (fun _ => []) []
        (initList second ((xs.reverse ++ acc).map eIn.symm)))
  | [], acc => by
      change (machine first second eOut eIn).step
        (transferCfg first second eOut eIn true (fun _ => [])
          (Function.update (fun _ => []) second.k₀ (acc.map eIn.symm)) []) = _
      exact transfer_two_nil first second eOut eIn acc
  | c :: xs, acc => by
      rw [List.length_cons, Function.iterate_succ_apply]
      change (flip Bind.bind (machine first second eOut eIn).step)^[xs.length + 1]
        ((machine first second eOut eIn).step
          (transferCfg first second eOut eIn true (fun _ => [])
            (Function.update (fun _ => []) second.k₀ (acc.map eIn.symm)) (c :: xs))) = _
      rw [transfer_two_cons, transfer_phase_two]
      simp
      rfl

/-- The intermediate tape crosses between the actual component alphabets in linear time. -/
theorem transfer_trace (xs : List Sym) :
    (flip Bind.bind (machine first second eOut eIn).step)^[2 * xs.length + 2]
        (some (transferCfg first second eOut eIn false
          (haltList first (xs.map eOut.symm)).stk (fun _ => []) [])) =
      some (secondCfg first second first.initialState none (fun _ => []) []
        (initList second (xs.map eIn.symm))) := by
  rw [haltList_stk_eq_update]
  have hsplit : 2 * xs.length + 2 = (xs.reverse.length + 1) + (xs.length + 1) := by simp; omega
  rw [hsplit, Function.iterate_add_apply, transfer_phase_one, List.append_nil]
  have hempty : (fun k => ([] : List (second.Γ k))) =
      Function.update (fun _ => []) second.k₀ ([].map eIn.symm) := by simp
  rw [hempty, transfer_phase_two]
  simp
  rfl

/-- The composed input is exactly the embedded first-machine input. -/
theorem machine_initList (xs : List (first.Γ first.k₀)) :
    initList (machine first second eOut eIn) xs =
      embedCfg (tm := first) (.inr false : second.Λ ⊕ Bool) (second.initialState, none)
        (embedStacks second Unit (fun _ => Sym) (fun _ => []) (fun _ => []))
        (initList first xs) := by
  unfold initList embedCfg
  congr 1
  funext k
  rcases k with k | k | u
  · by_cases h : k = first.k₀
    · subst k; simp [machine, parentTM, embedStacks]; rfl
    · simp [machine, parentTM, embedStacks, h]
  · simp [machine, parentTM, embedStacks]
  · cases u; simp [machine, parentTM, embedStacks]

/-- A cleaned-up second-machine halt is the exact composed-machine halt. -/
theorem machine_haltList (ys : List (second.Γ second.k₁)) :
    secondCfg first second first.initialState none (fun _ => []) [] (haltList second ys) =
      haltList (machine first second eOut eIn) ys := by
  unfold haltList secondCfg
  congr 1
  funext k
  rcases k with k | k | u
  · simp [machine, parentTM, combinedStacks, embedStacks]
  · by_cases h : k = second.k₁
    · subst k; simp [machine, parentTM, combinedStacks, embedStacks]; rfl
    · simp [machine, parentTM, combinedStacks, embedStacks, h]
  · cases u; simp [machine, parentTM, combinedStacks, embedStacks]

/-- The first computation reaches the transfer phase at its original step count. -/
theorem first_trace {m : ℕ} (xs : List (first.Γ first.k₀)) (ys : List Sym)
    (h : TM2OutputsInTime first xs (some (ys.map eOut.symm)) m) :
    (flip Bind.bind (machine first second eOut eIn).step)^[h.steps]
        (some (initList (machine first second eOut eIn) xs)) =
      some (transferCfg first second eOut eIn false
        (haltList first (ys.map eOut.symm)).stk (fun _ => []) []) := by
  rw [machine_initList]
  exact iterate_embedCfg (second.initialState, none) (.inr false)
    (caller first second eOut eIn) (second.initialState, none)
    (embedStacks second Unit (fun _ => Sym) (fun _ => []) (fun _ => []))
    h.steps h.evals_in_steps

/-- Sequential execution, paying for both calls and the entire intermediate-tape handoff. -/
def outputs {m₁ m₂ : ℕ} (xs : List (first.Γ first.k₀)) (ys : List Sym)
    (zs : List (second.Γ second.k₁))
    (h₁ : TM2OutputsInTime first xs (some (ys.map eOut.symm)) m₁)
    (h₂ : TM2OutputsInTime second (ys.map eIn.symm) (some zs) m₂) :
    TM2OutputsInTime (machine first second eOut eIn) xs (some zs)
      (m₁ + 2 * ys.length + 2 + m₂) where
  steps := h₁.steps + 2 * ys.length + 2 + h₂.steps
  evals_in_steps := by
    have hsplit : h₁.steps + 2 * ys.length + 2 + h₂.steps =
        h₂.steps + ((2 * ys.length + 2) + h₁.steps) := by omega
    rw [hsplit, Function.iterate_add_apply,
      Function.iterate_add_apply, first_trace first second eOut eIn xs ys h₁,
      transfer_trace]
    have hsim := second_iterate first second eOut eIn first.initialState none
      (fun _ => []) [] h₂.steps (some (initList second (ys.map eIn.symm)))
    rw [h₂.evals_in_steps] at hsim
    exact hsim.trans (congrArg some (machine_haltList first second eOut eIn zs))
  steps_le_m := by have := h₁.steps_le_m; have := h₂.steps_le_m; omega

@[simp] theorem outputs_steps {m₁ m₂ : ℕ} (xs : List (first.Γ first.k₀)) (ys : List Sym)
    (zs : List (second.Γ second.k₁))
    (h₁ : TM2OutputsInTime first xs (some (ys.map eOut.symm)) m₁)
    (h₂ : TM2OutputsInTime second (ys.map eIn.symm) (some zs) m₂) :
    (outputs first second eOut eIn xs ys zs h₁ h₂).steps =
      h₁.steps + 2 * ys.length + 2 + h₂.steps := rfl

end Composition

/-- The time polynomial for sequential composition, including the actual handoff cost. -/
noncomputable def compositionTime (first : FinTM2) (p q : Polynomial ℕ) : Polynomial ℕ :=
  p + 2 * outputPoly first p + 2 + q.comp (outputPoly first p)

/-- Concrete polynomial-time witnesses compose, at their unchanged `Sym` encodings. -/
noncomputable def composeWitness {α β γ : Type} {ea : α → List Sym} {eb : β → List Sym}
    {ec : γ → List Sym} {f : α → β} {g : β → γ}
    (hf : TM2ComputableInPolyTime ea eb f) (hg : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (g ∘ f) where
  tm := Composition.machine hf.tm hg.tm hf.outputAlphabet hg.inputAlphabet
  inputAlphabet := hf.inputAlphabet
  outputAlphabet := hg.outputAlphabet
  time := compositionTime hf.tm hf.time hg.time
  outputsFun a := by
    have h := Composition.outputs hf.tm hg.tm hf.outputAlphabet hg.inputAlphabet
      ((ea a).map hf.inputAlphabet.symm) (eb (f a))
      ((ec (g (f a))).map hg.outputAlphabet.symm) (hf.outputsFun a) (hg.outputsFun (f a))
    refine ⟨h.toEvalsTo, h.steps_le_m.trans ?_⟩
    have hsize := encoded_output_length_le hf a
    have hsecond := comp_eval_le hf hg.time a
    simp only [compositionTime, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat]
    omega

end PCP.Machine
