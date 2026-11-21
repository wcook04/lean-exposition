import PCP.Complexity.BinaryNaturalMachine

/-!
# Counting list delimiters with a concrete binary counter

Every separator increments an on-tape canonical binary counter. Carry bits use
scratch storage and are restored before scanning resumes. No unbounded counter
is part of finite control. The machine consumes the source list, empties scratch,
preserves caller stacks and returns the exact binary natural list length.
-/

namespace PCP.Machine.LangListLength

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
  Λ := Fin 3
  main := 0
  σ := Option Sym
  initialState := none
  m := fun phase =>
    if phase = 0 then
      .pop (.inl .src) (fun _ o => o) <|
        .branch Option.isNone (.load (fun _ => none) .halt)
          (.load (fun v => v) <|
            .goto (fun v => if v = some .sep then 1 else 0))
    else if phase = 1 then
      .pop (.inl .dst) (fun _ o => o) <|
        .branch (fun v => v = some (.bit true))
          (.push (.inl .scratch) (fun _ => .bit false)
            (.load (fun _ => none) (.goto (fun _ => 1))))
          (.push (.inl .dst) (fun _ => .bit true)
            (.load (fun _ => none) (.goto (fun _ => 2))))
    else
      .pop (.inl .scratch) (fun _ o => o) <|
        .branch Option.isNone (.load (fun _ => none) (.goto (fun _ => 0)))
          (.push (.inl .dst) (fun v => v.getD .sep)
            (.load (fun _ => none) (.goto (fun _ => 2))))

/-- The scan's just-read symbol is irrelevant; reset it explicitly at entry points. -/
def cfg (l : Option (Fin 3)) (v : Option Sym) (src scratch dst : List Sym)
    (S : ∀ k : F, List (Γf k)) : (machine F Γf).Cfg :=
  ⟨l, v, fun k => match k with
    | .inl .src => src
    | .inl .scratch => scratch
    | .inl .dst => dst
    | .inr k => S k⟩

variable {F Γf}

theorem step_scan_bit (b : Bool) (v : Option Sym) (src scratch dst : List Sym)
    (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some 0) v (.bit b :: src) scratch dst S) =
      some (cfg F Γf (some 0) (some (.bit b)) src scratch dst S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some (0 : Fin 3), some (.bit b), T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_scan_sep (v : Option Sym) (src scratch dst : List Sym)
    (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some 0) v (.sep :: src) scratch dst S) =
      some (cfg F Γf (some 1) (some .sep) src scratch dst S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some (1 : Fin 3), some .sep, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_scan_nil (v : Option Sym) (scratch dst : List Sym)
    (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some 0) v [] scratch dst S) =
      some (cfg F Γf none none [] scratch dst S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨none, none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_carry_true (v : Option Sym) (src scratch dst : List Sym)
    (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some 1) v src scratch (.bit true :: dst) S) =
      some (cfg F Γf (some 1) none src (.bit false :: scratch) dst S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some (1 : Fin 3), none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_carry_false (v : Option Sym) (src scratch dst : List Sym)
    (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some 1) v src scratch (.bit false :: dst) S) =
      some (cfg F Γf (some 2) none src scratch (.bit true :: dst) S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some (2 : Fin 3), none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_carry_nil (v : Option Sym) (src scratch : List Sym)
    (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some 1) v src scratch [] S) =
      some (cfg F Γf (some 2) none src scratch [.bit true] S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some (2 : Fin 3), none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_restore_cons (c : Sym) (src scratch dst : List Sym)
    (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some 2) none src (c :: scratch) dst S) =
      some (cfg F Γf (some 2) none src scratch (c :: dst) S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some (2 : Fin 3), none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem step_restore_nil (src dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (machine F Γf).step (cfg F Γf (some 2) none src [] dst S) =
      some (cfg F Γf (some 0) none src [] dst S) := by
  dsimp only [FinTM2.step, machine, cfg, TM2.step, TM2.stepAux]
  refine congrArg some (congrArg (fun T =>
    (⟨some (0 : Fin 3), none, T⟩ : (machine F Γf).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _) | k <;> simp [Function.update]

theorem restore (src scratch dst : List Sym) (S : ∀ k : F, List (Γf k)) :
    (flip Bind.bind (machine F Γf).step)^[scratch.length + 1]
      (some (cfg F Γf (some 2) none src scratch dst S)) =
      some (cfg F Γf (some 0) none src [] (scratch.reverse ++ dst) S) := by
  induction scratch generalizing dst with
  | nil => exact step_restore_nil src dst S
  | cons c scratch ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (flip Bind.bind (machine F Γf).step)^[scratch.length + 1]
      ((machine F Γf).step (cfg F Γf (some 2) none src (c :: scratch) dst S)) = _
    rw [step_restore_cons, ih]
    simp [List.reverse_cons, List.append_assoc]

/-- Exact carry cost, with arbitrary earlier carry cells already materialized in scratch. -/
theorem increment (bs : List Bool) (v : Option Sym) (src scratch : List Sym)
    (S : ∀ k : F, List (Γf k)) :
    (flip Bind.bind (machine F Γf).step)^[2 * (bs.takeWhile id).length + scratch.length + 2]
      (some (cfg F Γf (some 1) v src scratch (ofBits bs) S)) =
      some (cfg F Γf (some 0) none src []
        (scratch.reverse ++ ofBits (BinaryNatural.increment bs)) S) := by
  induction bs generalizing v scratch with
  | nil =>
    simp only [List.takeWhile_nil, List.length_nil, Nat.mul_zero, Nat.zero_add]
    rw [show scratch.length + 2 = (scratch.length + 1) + 1 by omega,
      Function.iterate_succ_apply]
    change (flip Bind.bind (machine F Γf).step)^[scratch.length + 1]
      ((machine F Γf).step (cfg F Γf (some 1) v src scratch [] S)) = _
    rw [step_carry_nil, restore]
    rfl
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [List.takeWhile_cons, id_eq, Bool.false_eq_true, ↓reduceIte, List.length_nil,
        Nat.mul_zero, Nat.zero_add]
      rw [show scratch.length + 2 = (scratch.length + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change (flip Bind.bind (machine F Γf).step)^[scratch.length + 1]
        ((machine F Γf).step
          (cfg F Γf (some 1) v src scratch (.bit false :: ofBits bs) S)) = _
      rw [step_carry_false, restore]
      rfl
    | true =>
      simp only [List.takeWhile_cons, id_eq, ↓reduceIte, ↓reduceIte, List.length_cons]
      have hn : 2 * ((List.takeWhile id bs).length + 1) + scratch.length + 2 =
          (2 * (List.takeWhile id bs).length + (.bit false :: scratch).length + 2) + 1 := by
        simp only [List.length_cons]; omega
      rw [hn, Function.iterate_succ_apply]
      change (flip Bind.bind (machine F Γf).step)^[
        2 * (List.takeWhile id bs).length + (.bit false :: scratch).length + 2]
        ((machine F Γf).step
          (cfg F Γf (some 1) v src scratch (.bit true :: ofBits bs) S)) = _
      rw [step_carry_true, ih]
      simp [BinaryNatural.increment, ofBits, List.reverse_cons, List.append_assoc]

/-- Consume a numeral and its separator before entering the increment phase. -/
theorem scan_chunk (bs : List Bool) (v : Option Sym) (src scratch dst : List Sym)
    (S : ∀ k : F, List (Γf k)) :
    (flip Bind.bind (machine F Γf).step)^[bs.length + 1]
      (some (cfg F Γf (some 0) v (ofBits bs ++ .sep :: src) scratch dst S)) =
      some (cfg F Γf (some 1) (some .sep) src scratch dst S) := by
  induction bs generalizing v with
  | nil => exact step_scan_sep v src scratch dst S
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (flip Bind.bind (machine F Γf).step)^[bs.length + 1]
      ((machine F Γf).step
        (cfg F Γf (some 0) v (.bit b :: (ofBits bs ++ .sep :: src)) scratch dst S)) = _
    rw [step_scan_bit, ih]

def runtime : List ℕ → ℕ → ℕ
  | [], _ => 1
  | a :: xs, n => runtime xs (n + 1) +
      (2 * (n.bits.takeWhile id).length + 2 + ((binDigits a).length + 1))

/-- The counter remains canonical at every entry boundary. -/
theorem trace (xs : List ℕ) (n : ℕ) (v : Option Sym) (S : ∀ k : F, List (Γf k)) :
    (flip Bind.bind (machine F Γf).step)^[runtime xs n]
      (some (cfg F Γf (some 0) v (encodeNats xs) [] (natTape n) S)) =
      some (cfg F Γf none none [] [] (natTape (n + xs.length)) S) := by
  induction xs generalizing n v with
  | nil =>
    change (machine F Γf).step (cfg F Γf (some 0) v [] [] (natTape n) S) = _
    exact step_scan_nil v [] (natTape n) S
  | cons a xs ih =>
    have he : encodeNats (a :: xs) = ofBits (binDigits a) ++ .sep :: encodeNats xs := by
      simp [encodeNats, ofBits, List.append_assoc]
    rw [runtime, Function.iterate_add_apply]
    rw [Function.iterate_add_apply, he, scan_chunk]
    have hi := increment n.bits (some Sym.sep) (encodeNats xs) [] S
    simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append,
      BinaryNatural.increment_bits] at hi
    simp only [natTape, binDigits_eq_bits] at ih ⊢
    rw [hi, ih]
    simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- The total step bound depends only on physically supplied input data and counter value. -/
theorem runtime_le (xs : List ℕ) (n : ℕ) :
    runtime xs n ≤ (encodeNats xs).length + xs.length * (2 * (n + xs.length) + 3) + 1 := by
  induction xs generalizing n with
  | nil => simp [runtime, encodeNats]
  | cons a xs ih =>
    have h := ih (n + 1)
    have ht : (n.bits.takeWhile id).length ≤ n := by
      have hb : n.bits.length = Nat.size n := by
        simpa only [natTape, binDigits_eq_bits, length_ofBits] using natTape_length n
      exact (List.takeWhile_prefix id).length_le.trans (hb.trans_le (size_le_self n))
    have hl : (encodeNats (a :: xs)).length =
        (binDigits a).length + 1 + (encodeNats xs).length := by
      simp [encodeNats, ofBits]
      omega
    rw [runtime, hl, List.length_cons]
    nlinarith

/-- A polynomial-time materialized list-length primitive, preserving arbitrary caller storage. -/
def evals (xs : List ℕ) (S : ∀ k : F, List (Γf k)) :
    EvalsToInTime (machine F Γf).step
      (cfg F Γf (some 0) none (encodeNats xs) [] [] S)
      (some (cfg F Γf none none [] [] (natTape xs.length) S))
      ((2 * listSize xs + 4) * listSize xs + 1) where
  steps := runtime xs 0
  evals_in_steps := by
    simpa only [Nat.zero_add, show natTape 0 = [] from rfl] using trace xs 0 none S
  steps_le_m := by
    have h := runtime_le xs 0
    have hl := length_le_listSize xs
    rw [listTape_length] at h
    simp only [Nat.zero_add] at h
    nlinarith

end PCP.Machine.LangListLength
