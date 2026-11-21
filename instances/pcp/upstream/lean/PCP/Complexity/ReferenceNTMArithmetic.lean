import PCP.Complexity.ReferenceNTMSimulation
import PCP.Complexity.ReferenceNTMFiniteTable

/-!
# A reference NTM transition as simultaneous arithmetic expressions

The first registers hold the encoded configuration; the final register is the
supplied nondeterministic choice bit. Every transition lookup is a fixed finite
expression tree determined by the source machine and its finite state numbering.
-/

namespace PCP.ReferenceNTM.Arithmetic

open Complexity PCP.Lang.ArithmeticExpression

variable {k q : ℕ} (tm : NTM k) (eQ : tm.Q ≃ Fin q)

abbrev inputs (k : ℕ) : ℕ := Cfg.width k + 1

def values (c : Cfg tm) (b : Bool) : Fin (inputs k) → ℕ :=
  Fin.snoc (Cfg.encode eQ c) b.toNat

def state : Term (inputs k) := .input ((0 : Fin (Cfg.width k)).castSucc)

def choice : Term (inputs k) := .input (Fin.last (Cfg.width k))

def tape (j : Fin (k + 2)) : TapeTerms (inputs k) :=
  ⟨.input (Cfg.codeIndex j).castSucc, .input (Cfg.headIndex j).castSucc,
    .input (Cfg.powerIndex j).castSucc⟩

@[simp] theorem eval_state (c : Cfg tm) (b : Bool) :
    (state (k := k)).eval (values tm eQ c b) = (eQ c.state).val := by
  simp [state, Term.eval, values]

@[simp] theorem eval_choice (c : Cfg tm) (b : Bool) :
    (choice (k := k)).eval (values tm eQ c b) = b.toNat := by
  simp [choice, Term.eval, values]

@[simp] theorem eval_tape (c : Cfg tm) (b : Bool) (j : Fin (k + 2)) :
    (tape j).eval (values tm eQ c b) = c.tapes j := by
  ext <;> simp [tape, TapeTerms.eval, Term.eval, values]

abbrev Instruction := tm.Q × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3

def instruction (b : Bool) (c : Cfg tm) : Instruction tm :=
  tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read

/-- Project any numeric component of the source machine's finite transition. -/
def lookup (f : Instruction tm → ℕ) : Term (inputs k) :=
  symbolTable (k + 2) (fun syms =>
    let atState (b : Bool) := Term.table (List.ofFn fun i : Fin q =>
      f (tm.δ b (eQ.symm i) (syms 0) (fun j => syms ⟨j.val + 2, by omega⟩)
        (syms 1))) state
    .cond choice (atState true) (atState false)) (fun j => (tape j).read)

theorem eval_lookup (f : Instruction tm → ℕ) (c : Cfg tm) (b : Bool) :
    (lookup tm eQ f).eval (values tm eQ c b) = f (instruction tm b c) := by
  rw [lookup, eval_symbolTable _ _ _ _ (fun j => (c.tapes j).read) (by
    intro j
    rw [TapeTerms.eval_read, eval_tape])]
  cases b <;>
    simp only [Term.eval, eval_choice, Bool.toNat_false, Bool.toNat_true,
      ne_eq, not_true_eq_false, ite_false]
  all_goals
    rw [Term.eval_finiteTable _ _ _ (eQ c.state) (eval_state tm eQ c _)]
    simp [instruction, Cfg.input, Cfg.output, Cfg.work]

/-- Direction of any of the input, output, or work tapes. -/
def tapeDirection (i : Instruction tm) (j : Fin (k + 2)) : Dir3 :=
  if h0 : j.val = 0 then i.2.2.2.1
  else if h1 : j.val = 1 then i.2.2.2.2.2
  else i.2.2.2.2.1 ⟨j.val - 2, by omega⟩

/-- The input tape is never written; its unused write value is blank. -/
def tapeWrite (i : Instruction tm) (j : Fin (k + 2)) : Γ :=
  if h0 : j.val = 0 then .blank
  else if h1 : j.val = 1 then i.2.2.1.toΓ
  else (i.2.1 ⟨j.val - 2, by omega⟩).toΓ

def nextTape (j : Fin (k + 2)) : TapeTerms (inputs k) :=
  let d := lookup tm eQ fun i => directionCode (tapeDirection tm i j)
  if j.val = 0 then (tape j).move d
  else (tape j).writeAndMove (lookup tm eQ fun i => symbolCode (tapeWrite tm i j)) d

theorem eval_nextTape (c : Cfg tm) (b : Bool) (j : Fin (k + 2)) :
    (nextTape tm eQ j).eval (values tm eQ c b) =
      if j.val = 0 then (c.tapes j).move (tapeDirection tm (instruction tm b c) j)
      else (c.tapes j).writeAndMove (tapeWrite tm (instruction tm b c) j)
        (tapeDirection tm (instruction tm b c) j) := by
  unfold nextTape
  split
  · rw [TapeTerms.eval_move _ _ _ _ (eval_lookup tm eQ _ c b), eval_tape]
  · rw [TapeTerms.eval_writeAndMove _ _ _ _ _ _ (eval_lookup tm eQ _ c b)
      (eval_lookup tm eQ _ c b), eval_tape]

theorem step_state (c : Cfg tm) (b : Bool) (h : c.state ≠ tm.qhalt) :
    (Cfg.step b c).state = (instruction tm b c).1 := by
  simp [Cfg.step, instruction, h]

theorem step_tape (c : Cfg tm) (b : Bool) (j : Fin (k + 2))
    (h : c.state ≠ tm.qhalt) :
    (Cfg.step b c).tapes j =
      if j.val = 0 then (c.tapes j).move (tapeDirection tm (instruction tm b c) j)
      else (c.tapes j).writeAndMove (tapeWrite tm (instruction tm b c) j)
        (tapeDirection tm (instruction tm b c) j) := by
  by_cases h0 : j.val = 0
  · have hj : j = 0 := Fin.ext h0
    subst j
    simp [Cfg.step, instruction, h, tapeDirection, Cfg.input]
  · by_cases h1 : j.val = 1
    · have hj : j = 1 := Fin.ext h1
      subst j
      simp [Cfg.step, instruction, h, tapeDirection, tapeWrite, Cfg.output]
    · have hj : (⟨j.val - 2 + 2, by omega⟩ : Fin (k + 2)) = j := by
        apply Fin.ext
        dsimp
        omega
      have hj0 : j ≠ 0 := by
        intro he
        exact h0 (congrArg Fin.val he)
      simp [Cfg.step, instruction, h, h0, h1, hj0, tapeDirection, tapeWrite, Cfg.work, hj]

/-- Simultaneously update every configuration coordinate from the old registers. -/
def transition (r : Fin (Cfg.width k)) : Term (inputs k) :=
  let fresh := if h : r.val = 0 then lookup tm eQ fun i => (eQ i.1).val
    else
      let j : Fin (k + 2) := ⟨(r.val - 1) / 3, by
        have hr := r.isLt
        dsimp [Cfg.width] at hr
        omega⟩
      let t := nextTape tm eQ j
      if (r.val - 1) % 3 = 0 then t.code
      else if (r.val - 1) % 3 = 1 then t.head else t.power
  .iteEq state (.const (eQ tm.qhalt).val) (.input r.castSucc) fresh

/-- The expression tuple realizes the exact supplied-choice reference transition. -/
theorem eval_transition (c : Cfg tm) (b : Bool) (r : Fin (Cfg.width k)) :
    (transition tm eQ r).eval (values tm eQ c b) = Cfg.encode eQ (Cfg.step b c) r := by
  have he : (eQ c.state).val = (eQ tm.qhalt).val ↔ c.state = tm.qhalt := by
    constructor
    · intro h
      exact eQ.injective (Fin.ext h)
    · intro h
      rw [h]
  rw [transition, Term.eval_iteEq, eval_state]
  simp only [Term.eval, he]
  by_cases hh : c.state = tm.qhalt
  · simp [hh, Cfg.step, values]
  · simp only [hh, ite_false]
    by_cases hr : r.val = 0
    · simp only [hr, dite_true]
      rw [eval_lookup]
      rw [Cfg.encode]
      simp only [hr, dite_true, step_state tm c b hh]
    · let j : Fin (k + 2) := ⟨(r.val - 1) / 3, by
        have h := r.isLt
        dsimp [Cfg.width] at h
        omega⟩
      have ht : (nextTape tm eQ j).eval (values tm eQ c b) = (Cfg.step b c).tapes j := by
        rw [eval_nextTape, step_tape tm c b j hh]
      have hc := congrArg Tape.code ht
      have hd := congrArg Tape.head ht
      have hp := congrArg Tape.power ht
      simp only [TapeTerms.eval] at hc hd hp
      simp only [hr, dite_false, Cfg.encode]
      split_ifs <;> assumption

end PCP.ReferenceNTM.Arithmetic
