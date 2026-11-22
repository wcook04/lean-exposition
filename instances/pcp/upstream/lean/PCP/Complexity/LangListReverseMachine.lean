import PCP.Complexity.LangListMachine

/-!
# Reversing separator-delimited natural lists on actual tapes

The machine transfers one numeral at a time through a scratch stack. This
reverses the order of list entries while preserving each numeral's bit order.
An existing destination is retained as a suffix, implementing reverse-append.
The source and scratch are cleared, all caller stacks are preserved, and the
exact cost is twice the input's encoded length plus one.
-/

namespace PCP.Machine.LangListReverse

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition PCP.Lang

variable (F : Type) [DecidableEq F] [Fintype F] (Γf : F → Type)

abbrev Alphabet : MoveSlot ⊕ F → Type
  | .inl _ => Sym
  | .inr k => Γf k

def machine : FinTM2 where
  K := MoveSlot ⊕ F
  k₀ := .inl .src
  k₁ := .inl .dst
  Γ := Alphabet F Γf
  Γk₀Fin := inferInstanceAs (Fintype Sym)
  Λ := MovePhase
  main := .one
  σ := Option Sym
  initialState := none
  m := fun
    | .one => .pop (.inl .src) (fun _ o => o) <|
        .branch Option.isNone (.load (fun _ => none) .halt)
          (.branch (fun v => v = some .sep)
            (.push (.inl .dst) (fun _ => .sep)
              (.load (fun _ => none) (.goto (fun _ => .two))))
            (.push (.inl .scratch) (fun v => v.getD .sep)
              (.load (fun _ => none) (.goto (fun _ => .one)))))
    | .two => .pop (.inl .scratch) (fun _ o => o) <|
        .branch Option.isNone (.load (fun _ => none) (.goto (fun _ => .one)))
          (.push (.inl .dst) (fun v => v.getD .sep)
            (.load (fun _ => none) (.goto (fun _ => .two))))

def cfg (l : Option MovePhase) (src scratch dst : List Sym)
    (S : ∀ k : F, List (Γf k)) : (machine F Γf).Cfg :=
  ⟨l, none, fun k => match k with
    | .inl .src => src
    | .inl .scratch => scratch
    | .inl .dst => dst
    | .inr k => S k⟩

variable {F Γf}

theorem step_read_bit (b : Bool) (src scratch dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some .one) (.bit b :: src) scratch dst S) =
      some (cfg F Γf (some .one) src (.bit b :: scratch) dst S) := by
  simp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some .one, none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_read_sep (src scratch dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some .one) (.sep :: src) scratch dst S) =
      some (cfg F Γf (some .two) src scratch (.sep :: dst) S) := by
  simp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some .two, none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_read_nil (scratch dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some .one) [] scratch dst S) =
      some (cfg F Γf none [] scratch dst S) := by
  simp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨none, none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_restore_cons (c : Sym) (src scratch dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some .two) src (c :: scratch) dst S) =
      some (cfg F Γf (some .two) src scratch (c :: dst) S) := by
  simp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some .two, none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_restore_nil (src dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some .two) src [] dst S) =
      some (cfg F Γf (some .one) src [] dst S) := by
  simp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some .one, none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

/-- A numeral is copied into scratch in reverse order. -/
theorem read_bits (bs : List Bool) (src scratch dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (flip Bind.bind (machine F Γf).step)^[bs.length]
      (some (cfg F Γf (some .one) (ofBits bs ++ src) scratch dst S)) =
      some (cfg F Γf (some .one) src ((ofBits bs).reverse ++ scratch) dst S) := by
  induction bs generalizing scratch with
  | nil => rfl
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (flip Bind.bind (machine F Γf).step)^[bs.length]
      ((machine F Γf).step (cfg F Γf (some .one) (.bit b :: (ofBits bs ++ src)) scratch dst S)) = _
    rw [step_read_bit, ih]
    simp [ofBits, List.reverse_cons, List.append_assoc]

/-- Restore one materialized numeral onto the destination and return to the scanner. -/
theorem restore (src scratch dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (flip Bind.bind (machine F Γf).step)^[scratch.length + 1]
      (some (cfg F Γf (some .two) src scratch dst S)) =
      some (cfg F Γf (some .one) src [] (scratch.reverse ++ dst) S) := by
  induction scratch generalizing dst with
  | nil =>
    change (machine F Γf).step (cfg F Γf (some .two) src [] dst S) = _
    exact step_restore_nil src dst S
  | cons c scratch ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (flip Bind.bind (machine F Γf).step)^[scratch.length + 1]
      ((machine F Γf).step (cfg F Γf (some .two) src (c :: scratch) dst S)) = _
    rw [step_restore_cons, ih]
    simp [List.reverse_cons, List.append_assoc]

/-- Transfer one whole entry, including the empty numeral representing zero. -/
theorem chunk (bs : List Bool) (src dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (flip Bind.bind (machine F Γf).step)^[2 * bs.length + 2]
      (some (cfg F Γf (some .one) (ofBits bs ++ .sep :: src) [] dst S)) =
      some (cfg F Γf (some .one) src [] (ofBits bs ++ .sep :: dst) S) := by
  have hn : 2 * bs.length + 2 = (bs.length + 1) + 1 + bs.length := by omega
  rw [hn, Function.iterate_add_apply, read_bits]
  simp only [List.append_nil]
  rw [Function.iterate_succ_apply]
  change (flip Bind.bind (machine F Γf).step)^[bs.length + 1]
    ((machine F Γf).step (cfg F Γf (some .one) (.sep :: src) (ofBits bs).reverse dst S)) = _
  rw [step_read_sep]
  have hl : (ofBits bs).reverse.length = bs.length := by simp [ofBits]
  rw [← hl, restore, List.reverse_reverse]

/-- Complete reverse-append with an arbitrary destination and untouched caller frame. -/
theorem trace (xs : List ℕ) (dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (flip Bind.bind (machine F Γf).step)^[2 * (encodeNats xs).length + 1]
      (some (cfg F Γf (some .one) (encodeNats xs) [] dst S)) =
      some (cfg F Γf none [] [] (encodeNats xs.reverse ++ dst) S) := by
  induction xs generalizing dst with
  | nil =>
    change (machine F Γf).step (cfg F Γf (some .one) [] [] dst S) = _
    exact step_read_nil [] dst S
  | cons n xs ih =>
    have he : encodeNats (n :: xs) = ofBits (binDigits n) ++ .sep :: encodeNats xs := by
      simp [encodeNats, ofBits, List.append_assoc]
    have hn : 2 * (encodeNats (n :: xs)).length + 1 =
        (2 * (encodeNats xs).length + 1) + (2 * (binDigits n).length + 2) := by
      rw [he]
      simp only [List.length_append, List.length_cons, length_ofBits]
      omega
    rw [hn, he, Function.iterate_add_apply, chunk, ih]
    congr 1
    simp [encodeNats, List.flatMap_append, List.reverse_cons, ofBits, List.append_assoc]

/-- Concrete framed execution in the language's exact list encoding. -/
def evals (xs ys : List ℕ) (S : ∀ k : F, List (Γf k)) :
    EvalsToInTime (machine F Γf).step
      (cfg F Γf (some .one) (encodeNats xs) [] (encodeNats ys) S)
      (some (cfg F Γf none [] [] (encodeNats (xs.reverse ++ ys)) S))
      (2 * listSize xs + 1) where
  steps := 2 * (encodeNats xs).length + 1
  evals_in_steps := by simpa [encodeNats, List.flatMap_append] using trace xs (encodeNats ys) S
  steps_le_m := by rw [listTape_length]

end PCP.Machine.LangListReverse
