import PCP.Complexity.BinaryMultiplicationCore
import PCP.Complexity.PreservingBinaryZip
import PCP.Complexity.FiniteBlockMachine

/-!
# A concrete binary multiplication machine

The multiplier is reversed once and scanned from high bits to low bits. Each
pass doubles the on-tape accumulator; a set bit invokes the actual binary adder,
retaining the multiplicand. The finite controller stores only a bit and an
emptiness flag. All multiplier and scratch tapes are cleared at termination.
-/

namespace PCP.Machine.BinaryMultiplication

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition PCP.Lang FiniteBlocks

variable (F : Type) [DecidableEq F] [Fintype F]

abbrev Tapes := PreservingBinaryZip.Slot ⊕ (Bool ⊕ F)

abbrev adder : Block (Tapes F) (fun _ => Sym) where
  Label := MovePhase
  Control := Bool × Option Sym × Option Sym
  entry := .one
  initial := (false, none, none)
  code := (PreservingBinaryZip.machine BinaryAddition.spec (Bool ⊕ F)).m

abbrev blocks (_ : Unit) : Block (Tapes F) (fun _ => Sym) := adder F

abbrev Label := Labels (blocks F) (L := Bool)
abbrev Control := Controls (blocks F) × (Option Sym × Bool)

def returns (_ : Unit) : Bool := true

def resume : Stmt (fun _ : Tapes F => Sym) (Label F) (Control F) :=
  .branch (fun v => v.2.1 = some (.bit true))
    (.load (fun v => (v.1, none, false)) (enter (blocks F) ()))
    (.load (fun v => (v.1, none, false)) (.goto (fun _ => .inr true)))

/-- False reverses the multiplier; true runs the Horner scan. -/
def caller : Bool → Stmt (fun _ : Tapes F => Sym) (Label F) (Control F)
  | false => .pop (.inr (.inl false)) (fun v o => (v.1, o, false)) <|
      .branch (fun v => v.2.1.isNone)
        (.load (fun v => (v.1, none, false)) (.goto (fun _ => .inr true)))
        (.push (.inr (.inl true)) (fun v => v.2.1.getD .sep)
          (.load (fun v => (v.1, none, false)) (.goto (fun _ => .inr false))))
  | true => .pop (.inr (.inl true)) (fun v o => (v.1, o, false)) <|
      .branch (fun v => v.2.1.isNone)
        (.load (fun v => (v.1, none, false)) .halt)
        (.peek (.inl .right) (fun v o => (v.1, v.2.1, o.isSome))
          (.branch (fun v => v.2.2)
            (.push (.inl .right) (fun _ => .bit false) (resume F)) (resume F)))

abbrev machine : FinTM2 :=
  FiniteBlocks.machine (blocks F) (.inr (.inl false)) (.inl .right)
    false (none, false) returns (caller F)

def frame (source bits : List Sym) (S : F → List Sym) : Bool ⊕ F → List Sym
  | .inl false => source
  | .inl true => bits
  | .inr k => S k

def cfg (l : Option (Label F)) (left right source bits : List Sym) (S : F → List Sym) :
    (machine F).Cfg :=
  ⟨l, ((fun _ => (false, none, none)), none, false), fun k => match k with
    | .inl .left => left
    | .inl .right => right
    | .inl .save => []
    | .inl .result => []
    | .inr k => frame F source bits S k⟩

variable {F}

def doubleTape : List Sym → List Sym
  | [] => []
  | c :: cs => .bit false :: c :: cs

theorem doubleTape_natTape (a : ℕ) : doubleTape (natTape a) = natTape (2 * a) := by
  by_cases ha : a = 0
  · subst a; rfl
  · have ht : natTape a ≠ [] := fun h => ha (natTape_injective h)
    have he : doubleTape (natTape a) = .bit false :: natTape a := by
      cases h : natTape a with
      | nil => exact False.elim (ht h)
      | cons c cs => rfl
    rw [he]
    simp only [natTape, binDigits_eq_bits, Nat.bit0_bits a ha, ofBits, List.map_cons]

theorem step_reverse_cons (c : Sym) (left right source bits : List Sym) (S : F → List Sym) :
    (machine F).step (cfg F (some (.inr false)) left right (c :: source) bits S) =
      some (cfg F (some (.inr false)) left right source (c :: bits) S) := by
  dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg, TM2.stepAux, frame]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr false), ((fun _ => (false, none, none)), none, false), T⟩ : (machine F).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | (b | k)
  all_goals first | cases b <;> simp [Function.update] | simp [Function.update]

theorem step_reverse_nil (left right bits : List Sym) (S : F → List Sym) :
    (machine F).step (cfg F (some (.inr false)) left right [] bits S) =
      some (cfg F (some (.inr true)) left right [] bits S) := by
  dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg, TM2.stepAux, frame]
  refine congrArg some (congrArg (fun T =>
    (⟨some (.inr true), ((fun _ => (false, none, none)), none, false), T⟩ : (machine F).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | (b | k)
  all_goals first | cases b <;> simp [Function.update] | simp [Function.update]

theorem step_scan_nil (left right source : List Sym) (S : F → List Sym) :
    (machine F).step (cfg F (some (.inr true)) left right source [] S) =
      some (cfg F none left right source [] S) := by
  dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg, TM2.stepAux, frame]
  refine congrArg some (congrArg (fun T =>
    (⟨none, ((fun _ => (false, none, none)), none, false), T⟩ : (machine F).Cfg)) ?_)
  funext k
  rcases k with (_ | _ | _ | _) | (b | k)
  all_goals first | cases b <;> simp [Function.update] | simp [Function.update]

theorem step_scan_false (left right source bits : List Sym) (S : F → List Sym) :
    (machine F).step
      (cfg F (some (.inr true)) left right source (.bit false :: bits) S) =
      some (cfg F (some (.inr true)) left (doubleTape right) source bits S) := by
  cases right with
  | nil =>
    dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
      TM2.stepAux, frame, resume, doubleTape]
    refine congrArg some (congrArg (fun T =>
      (⟨some (.inr true), ((fun _ => (false, none, none)), none, false), T⟩ : (machine F).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _ | _) | (b | k)
    all_goals first | cases b <;> simp [Function.update] | simp [Function.update]
  | cons c cs =>
    dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
      TM2.stepAux, frame, resume, doubleTape]
    refine congrArg some (congrArg (fun T =>
      (⟨some (.inr true), ((fun _ => (false, none, none)), none, false), T⟩ : (machine F).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _ | _) | (b | k)
    all_goals first | cases b <;> simp [Function.update] | simp [Function.update]

theorem step_scan_true (left right source bits : List Sym) (S : F → List Sym) :
    (machine F).step
      (cfg F (some (.inr true)) left right source (.bit true :: bits) S) =
      some (cfg F (some (.inl ⟨(), .one⟩)) left (doubleTape right) source bits S) := by
  cases right with
  | nil =>
    dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
      TM2.stepAux, frame, resume, doubleTape, enter]
    simp only [Function.update_eq_self]
    refine congrArg some (congrArg (fun T =>
      (⟨some (.inl ⟨(), .one⟩), ((fun _ => (false, none, none)), none, false), T⟩ :
        (machine F).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _ | _) | (b | k)
    all_goals first | cases b <;> simp [Function.update] | simp [Function.update]
  | cons c cs =>
    dsimp only [machine, FiniteBlocks.machine, FinTM2.step, TM2.step, caller, cfg,
      TM2.stepAux, frame, resume, doubleTape, enter]
    simp only [Function.update_eq_self]
    refine congrArg some (congrArg (fun T =>
      (⟨some (.inl ⟨(), .one⟩), ((fun _ => (false, none, none)), none, false), T⟩ :
        (machine F).Cfg)) ?_)
    funext k
    rcases k with (_ | _ | _ | _) | (b | k)
    all_goals first | cases b <;> simp [Function.update] | simp [Function.update]

/-- The existing concrete adder runs inside the fixed multiplication control graph. -/
theorem addition_trace (n a : ℕ) (source bits : List Sym) (S : F → List Sym) :
    (flip Bind.bind (machine F).step)^[additionTime n a]
      (some (cfg F (some (.inl ⟨(), .one⟩)) (natTape n) (natTape a) source bits S)) =
      some (cfg F (some (.inr true)) (natTape n) (natTape (n + a)) source bits S) := by
  have h := PreservingBinaryZip.trace (spec := BinaryAddition.spec)
    (natTape n) (natTape a) (frame F source bits S)
  simp only [BinaryAddition.output_natTape, natTape_length] at h
  have hi := FiniteBlocks.iterate_embedCfg (blocks F) (.inr (.inl false)) (.inl .right)
    false (none, false) returns (caller F) () (fun _ => (false, none, none))
      (none, false) (additionTime n a) h
  have hc (l : Option MovePhase) (x y : List Sym) :
      FiniteBlocks.embedCfg (blocks F) returns () (fun _ => (false, none, none))
        (none, false) (PreservingBinaryZip.cfg BinaryAddition.spec (Bool ⊕ F)
          l false x y [] [] (frame F source bits S)) =
      cfg F (some (l.elim (.inr true) (fun k => .inl ⟨(), k⟩))) x y source bits S := by
    cases l <;>
      dsimp only [FiniteBlocks.embedCfg, PreservingBinaryZip.cfg, cfg, returns, Option.elim]
    all_goals
      simp only [Function.update_eq_self]
      congr 1
      funext k
      rcases k with (_ | _ | _ | _) | k <;> rfl
  simp only [hc, Option.elim] at hi
  dsimp only [FinTM2.Cfg, machine, FiniteBlocks.machine] at hi ⊢
  exact hi

/-- Reversal is a single physical pass followed by one emptiness test. -/
theorem reverse_trace (left right source bits : List Sym) (S : F → List Sym) :
    (flip Bind.bind (machine F).step)^[source.length + 1]
      (some (cfg F (some (.inr false)) left right source bits S)) =
      some (cfg F (some (.inr true)) left right [] (source.reverse ++ bits) S) := by
  induction source generalizing bits with
  | nil => exact step_reverse_nil left right bits S
  | cons c source ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (flip Bind.bind (machine F).step)^[source.length + 1]
      ((machine F).step (cfg F (some (.inr false)) left right (c :: source) bits S)) = _
    rw [step_reverse_cons, ih]
    simp [List.reverse_cons, List.append_assoc]

/-- Each high-to-low bit performs the stated Horner step on materialized natural tapes. -/
theorem loop_trace (n a : ℕ) (bs : List Bool) (source : List Sym) (S : F → List Sym) :
    (flip Bind.bind (machine F).step)^[runtime n a bs]
      (some (cfg F (some (.inr true)) (natTape n) (natTape a) source (ofBits bs) S)) =
      some (cfg F none (natTape n) (natTape (value n a bs)) source [] S) := by
  induction bs generalizing a with
  | nil => exact step_scan_nil (natTape n) (natTape a) source S
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [runtime, Bool.false_eq_true, ite_false, Nat.add_zero]
      rw [Function.iterate_succ_apply]
      change (flip Bind.bind (machine F).step)^[runtime n (stepValue n a false) bs]
        ((machine F).step (cfg F (some (.inr true)) (natTape n) (natTape a)
          source (.bit false :: ofBits bs) S)) = _
      rw [step_scan_false, doubleTape_natTape]
      exact ih (2 * a)
    | true =>
      simp only [runtime, ite_true]
      rw [Function.iterate_succ_apply]
      change (flip Bind.bind (machine F).step)^[runtime n (stepValue n a true) bs +
        additionTime n (2 * a)]
        ((machine F).step (cfg F (some (.inr true)) (natTape n) (natTape a)
          source (.bit true :: ofBits bs) S)) = _
      rw [step_scan_true, doubleTape_natTape, Function.iterate_add_apply, addition_trace]
      have he : n + 2 * a = stepValue n a true := by simp [stepValue, Nat.add_comm]
      rw [he]
      exact ih _

/-- Complete framed multiplication with canonical output and cleared work tapes. -/
def evals (n m : ℕ) (S : F → List Sym) :
    EvalsToInTime (machine F).step
      (cfg F (some (.inr false)) (natTape n) [] (natTape m) [] S)
      (some (cfg F none (natTape n) (natTape (n * m)) [] [] S))
      (10 * (Nat.size n + Nat.size m + 1) ^ 2) where
  steps := Nat.size m + 1 + runtime n 0 m.bits.reverse
  evals_in_steps := by
    rw [Nat.add_comm, Function.iterate_add_apply]
    rw [← natTape_length m, reverse_trace, List.append_nil]
    have he : (natTape m).reverse = ofBits m.bits.reverse := by
      simp only [natTape, binDigits_eq_bits, ofBits, List.map_reverse]
    rw [he]
    have h := loop_trace n 0 m.bits.reverse [] S
    simpa only [show natTape 0 = [] from rfl, value_bits] using h
  steps_le_m := full_runtime_le n m

end PCP.Machine.BinaryMultiplication
