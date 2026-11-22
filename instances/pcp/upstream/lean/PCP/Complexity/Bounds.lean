import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Basic

/-!
# Structural execution bounds: how fast can a machine's tape grow?

## The target

```text
output.length ≤ input.length + C_push · timeBound
```

with `C_push` fixed by the machine and independent of the input. This is what charges the
intermediate-output size in a composition: to evaluate a second machine's time polynomial at the
first machine's output, one needs a bound on that output, and "polynomial time" alone does not give
one.

## The counting convention

One `Turing.TM2.step` executes a whole statement tree, so a step is not one operation. `opBound`
and `pushBound` are **upper bounds** on the constructors and the pushes of one counted step — the
longest path through the statement tree, taking the larger side of each branch. The actual counting
is done by `runCount`, which follows the branch selected; `runCount_snd_le_opBound` relates the two.
Neither bound recurses through labels: `goto` *ends* the counted step, and following its destination
is the next iteration's business.

`opBound` is a syntactic bound on statement constructors. It is **not** a cost model for an
elementary machine.

## This module is generic

Nothing here mentions the PCP encoders, and the imports say so: only mathlib. Keeping the
dependency one-way avoids a cycle when machine constructions need these bounds.

The `FinTM2` instances below are declared `local`, so they are **not** exported; a consumer that
needs them declares its own.

## Why the instance plumbing appears at the top

`stepAux` uses the machine's own `kDecidableEq` field, and `mass` needs its `kFin`. Earlier modules
worked around this per-lemma; this file makes both available as local instances once, which is what
lets `mass_update` be stated with the same dependent stack family `stepAux` actually uses.
-/

namespace PCP.Machine

open Turing Turing.TM2

attribute [local instance] Turing.FinTM2.kDecidableEq Turing.FinTM2.kFin
  Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-! ## Step A: constructor bounds -/

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- An **upper bound** on the statement constructors one counted step executes: the longest path
through the statement tree, taking the larger side of each branch.

It is an upper bound, not an exact count — an execution takes one side of each branch. `runCount`
below is the instrumented evaluator that follows the side actually taken, and
`runCount_snd_le_opBound` relates the two. -/
def opBound : Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + opBound q
  | .peek _ _ q => 1 + opBound q
  | .pop _ _ q => 1 + opBound q
  | .load _ q => 1 + opBound q
  | .branch _ q₁ q₂ => 1 + max (opBound q₁) (opBound q₂)
  | .goto _ => 1
  | .halt => 1

/-- An **upper bound** on the pushes one counted step performs: again the larger side of each
branch. Unlike `opBound` this bound is what the stack-growth argument needs directly, since
`mass_stepAux_le` proves the real execution never exceeds it. -/
def pushBound : Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + pushBound q
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q₁ q₂ => max (pushBound q₁) (pushBound q₂)
  | .goto _ => 0
  | .halt => 0

/-! ### The execution interpretation of `opBound`

A numeric definition is not an execution theorem. `runCount` is an instrumented evaluator: it
follows the branch actually selected, counting each constructor it executes, and produces the same
configuration `stepAux` does. `goto` and `halt` each contribute one and end the evaluation. -/

/-- Execute a statement, returning the resulting configuration together with the number of
constructors actually executed. -/
def runCount [DecidableEq K] : Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → Cfg Γ Λ σ × ℕ
  | .push k f q, v, S => ((runCount q v (Function.update S k (f v :: S k))).1,
      (runCount q v (Function.update S k (f v :: S k))).2 + 1)
  | .peek k f q, v, S => ((runCount q (f v (S k).head?) S).1,
      (runCount q (f v (S k).head?) S).2 + 1)
  | .pop k f q, v, S =>
      ((runCount q (f v (S k).head?) (Function.update S k (S k).tail)).1,
       (runCount q (f v (S k).head?) (Function.update S k (S k).tail)).2 + 1)
  | .load a q, v, S => ((runCount q (a v) S).1, (runCount q (a v) S).2 + 1)
  | .branch f q₁ q₂, v, S =>
      cond (f v) ((runCount q₁ v S).1, (runCount q₁ v S).2 + 1)
        ((runCount q₂ v S).1, (runCount q₂ v S).2 + 1)
  | .goto f, v, S => (⟨some (f v), v, S⟩, 1)
  | .halt, v, S => (⟨none, v, S⟩, 1)

/-- The instrumented evaluator computes exactly what `stepAux` computes. -/
theorem runCount_fst [DecidableEq K] : ∀ (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)),
    (runCount q v S).1 = stepAux q v S
  | .push k f q, v, S => runCount_fst q v _
  | .peek k f q, v, S => runCount_fst q _ S
  | .pop k f q, v, S => runCount_fst q _ _
  | .load a q, v, S => runCount_fst q _ S
  | .branch f q₁ q₂, v, S => by
      cases h : f v with
      | false => simpa [runCount, stepAux, h] using runCount_fst q₂ v S
      | true => simpa [runCount, stepAux, h] using runCount_fst q₁ v S
  | .goto f, v, S => rfl
  | .halt, v, S => rfl

/-- The executed count never exceeds the syntactic bound. -/
theorem runCount_snd_le_opBound [DecidableEq K] :
    ∀ (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)), (runCount q v S).2 ≤ opBound q
  | .push k f q, v, S => by
      have := runCount_snd_le_opBound q v (Function.update S k (f v :: S k))
      simp only [runCount, opBound]; omega
  | .peek k f q, v, S => by
      have := runCount_snd_le_opBound q (f v (S k).head?) S
      simp only [runCount, opBound]; omega
  | .pop k f q, v, S => by
      have := runCount_snd_le_opBound q (f v (S k).head?) (Function.update S k (S k).tail)
      simp only [runCount, opBound]; omega
  | .load a q, v, S => by
      have := runCount_snd_le_opBound q (a v) S
      simp only [runCount, opBound]; omega
  | .branch f q₁ q₂, v, S => by
      cases h : f v with
      | false =>
          have h1 := runCount_snd_le_opBound q₂ v S
          have h2 : opBound q₂ ≤ max (opBound q₁) (opBound q₂) := le_max_right _ _
          simp only [runCount, opBound, h, Bool.cond_false]; omega
      | true =>
          have h1 := runCount_snd_le_opBound q₁ v S
          have h2 : opBound q₁ ≤ max (opBound q₁) (opBound q₂) := le_max_left _ _
          simp only [runCount, opBound, h, Bool.cond_true]; omega
  | .goto f, v, S => by simp [runCount, opBound]
  | .halt, v, S => by simp [runCount, opBound]

/-! ## Step B: the dependent stack-update identity

Stated additively, so that no truncated subtraction appears: a push grows the total by exactly one,
a pop does not increase it, and a pop on an empty stack is covered without a side condition. -/

/-- Total length across all stacks. -/
def mass [Fintype K] (S : ∀ k, List (Γ k)) : ℕ := ∑ k, (S k).length

/-- Replacing one stack changes the total by exactly the difference in that stack's length. -/
theorem mass_update [DecidableEq K] [Fintype K] (S : ∀ k, List (Γ k)) (k : K) (new : List (Γ k)) :
    mass (Function.update S k new) + (S k).length = mass S + new.length := by
  classical
  have h1 : ∑ j, ((Function.update S k new) j).length
      = new.length + ∑ j ∈ Finset.univ.erase k, (S j).length := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    congr 1
    · simp
    · exact Finset.sum_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have h2 : ∑ j, (S j).length = (S k).length + ∑ j ∈ Finset.univ.erase k, (S j).length :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
  simp only [mass, h1, h2]
  omega

/-- A push grows the total by exactly one. -/
theorem mass_update_cons [DecidableEq K] [Fintype K] (S : ∀ k, List (Γ k)) (k : K) (c : Γ k) :
    mass (Function.update S k (c :: S k)) = mass S + 1 := by
  have := mass_update S k (c :: S k)
  simp only [List.length_cons] at this
  omega

/-- A pop never grows the total.  No hypothesis on the stack is needed: the empty case is covered
because `[].tail = []`. -/
theorem mass_update_tail_le [DecidableEq K] [Fintype K] (S : ∀ k, List (Γ k)) (k : K) :
    mass (Function.update S k (S k).tail) ≤ mass S := by
  have h := mass_update S k (S k).tail
  have : (S k).tail.length ≤ (S k).length := by
    cases hs : S k <;> simp [hs]
  omega

/-! ## Step C: from statements to whole machines -/

/-- Executing a statement grows the total stack length by at most its push bound. -/
theorem mass_stepAux_le [DecidableEq K] [Fintype K] : ∀ (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ
k)),
    mass (stepAux q v S).stk ≤ mass S + pushBound q
  | .push k f q, v, S => by
      have ih := mass_stepAux_le q v (Function.update S k (f v :: S k))
      rw [mass_update_cons] at ih
      simpa [stepAux, pushBound] using ih.trans (by omega)
  | .peek k f q, v, S => by
      simpa [stepAux, pushBound] using mass_stepAux_le q (f v (S k).head?) S
  | .pop k f q, v, S => by
      have ih := mass_stepAux_le q (f v (S k).head?) (Function.update S k (S k).tail)
      have hle := mass_update_tail_le S k
      simpa [stepAux, pushBound] using ih.trans (by omega)
  | .load a q, v, S => by
      simpa [stepAux, pushBound] using mass_stepAux_le q (a v) S
  | .branch f q₁ q₂, v, S => by
      cases h : f v with
      | false =>
          have ih := mass_stepAux_le q₂ v S
          simp only [stepAux, pushBound, h, Bool.cond_false]
          exact ih.trans (by omega)
      | true =>
          have ih := mass_stepAux_le q₁ v S
          simp only [stepAux, pushBound, h, Bool.cond_true]
          exact ih.trans (by omega)
  | .goto f, v, S => by simp [stepAux, pushBound, mass]
  | .halt, v, S => by simp [stepAux, pushBound, mass]

/-- The machine's push constant: the largest push bound over its finitely many labels.

Fixed by the machine. It does not depend on the input, which is the whole point. -/
noncomputable def machinePushBound (tm : FinTM2) : ℕ :=
  Finset.univ.sup fun l : tm.Λ => pushBound (tm.m l)

theorem pushBound_le_machinePushBound (tm : FinTM2) (l : tm.Λ) :
    pushBound (tm.m l) ≤ machinePushBound tm := by
  unfold machinePushBound
  exact Finset.le_sup (f := fun l : tm.Λ => pushBound (tm.m l)) (Finset.mem_univ l)

/-- One successful step grows the total stack length by at most `machinePushBound`. -/
theorem mass_step_le (tm : FinTM2) {c c' : tm.Cfg} (h : tm.step c = some c') :
    mass c'.stk ≤ mass c.stk + machinePushBound tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have h' : stepAux (tm.m l) v S = c' :=
        Option.some_inj.mp (show (some (stepAux (tm.m l) v S) : Option tm.Cfg) = some c' from h)
      subst h'
      exact (mass_stepAux_le (tm.m l) v S).trans
        (Nat.add_le_add_left (pushBound_le_machinePushBound tm l) _)

/-- A halted transition sequence stays halted. -/
theorem iterate_none (tm : FinTM2) : ∀ n : ℕ,
    (flip Bind.bind tm.step)^[n] none = none
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply]
      exact iterate_none tm n

/-- Growth over a whole transition sequence is linear in the number of steps. -/
theorem mass_iterate_le (tm : FinTM2) : ∀ (n : ℕ) (c c' : tm.Cfg),
    (flip Bind.bind tm.step)^[n] (some c) = some c' →
    mass c'.stk ≤ mass c.stk + machinePushBound tm * n
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst h
      simp
  | n + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h
      cases hstep : tm.step c with
      | none =>
          rw [show (flip Bind.bind tm.step) (some c) = none from hstep, iterate_none] at h
          exact absurd h (by simp)
      | some c₁ =>
          rw [show (flip Bind.bind tm.step) (some c) = some c₁ from hstep] at h
          have ih := mass_iterate_le tm n c₁ c' h
          have h1 := mass_step_le tm hstep
          calc mass c'.stk ≤ mass c₁.stk + machinePushBound tm * n := ih
            _ ≤ (mass c.stk + machinePushBound tm) + machinePushBound tm * n := by omega
            _ = mass c.stk + machinePushBound tm * (n + 1) := by ring

/-! ### The initial and final configurations have the expected mass -/

theorem mass_initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    mass (initList tm s).stk = s.length := by
  classical
  simp only [mass, initList]
  rw [Finset.sum_eq_single tm.k₀]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mass_haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    mass (haltList tm s).stk = s.length := by
  classical
  simp only [mass, haltList]
  rw [Finset.sum_eq_single tm.k₁]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The output-length bound -/

/-- **The target theorem.**  A machine's output is no longer than its input plus a machine-fixed
constant times the time bound.

This is what lets a composition charge the intermediate result: the second machine's time
polynomial can be evaluated at `N + C · p N` rather than at an unknown quantity. -/
theorem output_length_le (tm : FinTM2) {input : List (tm.Γ tm.k₀)} {output : List (tm.Γ tm.k₁)}
    {m : ℕ} (h : TM2OutputsInTime tm input (some output) m) :
    output.length ≤ input.length + machinePushBound tm * m := by
  have hevals : (flip Bind.bind tm.step)^[h.steps] (some (initList tm input))
      = some (haltList tm output) := h.evals_in_steps
  have hmass := mass_iterate_le tm h.steps (initList tm input) (haltList tm output) hevals
  rw [mass_initList, mass_haltList] at hmass
  have hsteps : machinePushBound tm * h.steps ≤ machinePushBound tm * m :=
    Nat.mul_le_mul_left _ h.steps_le_m
  omega

/-! ## The encoded-output polynomial

Packaging `output_length_le` for a `TM2ComputableInPolyTime` witness. This is the size algebra a
composition needs: to evaluate a second machine's time polynomial one must know how big the first
machine's output can be, and "polynomial time" alone does not say. -/

/-- `Q = X + C_push · p`: the bound on encoded output length in terms of encoded input length. -/
noncomputable def outputPoly (tm : FinTM2) (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (machinePushBound tm) * p

@[simp] theorem outputPoly_eval (tm : FinTM2) (p : Polynomial ℕ) (n : ℕ) :
    (outputPoly tm p).eval n = n + machinePushBound tm * p.eval n := by
  simp [outputPoly]

/-- **The encoded-output bound.**  Holds for any encodings: the alphabet conversions are list maps,
which preserve length, so no assumption about the PCP encoders enters. -/
theorem encoded_output_length_le {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f : α → β} (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (outputPoly h.tm h.time).eval (ea a).length := by
  have hout := output_length_le h.tm (h.outputsFun a)
  simpa using hout

/-- Evaluation of a polynomial over `ℕ` is monotone — all coefficients are nonnegative. -/
theorem eval_mono (p : Polynomial ℕ) {m n : ℕ} (hmn : m ≤ n) : p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using Nat.add_le_add hp hq
  | monomial k a =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmn k)

/-- **The composition size-and-time algebra.**  A second machine's time polynomial, evaluated at the
first machine's output length, is bounded by the composite polynomial evaluated at the original
input length.

This is algebra only. It does not construct a composed machine, and it does not pay for the handoff
between them — moving a stack, converting alphabets, clearing temporaries. -/
theorem comp_eval_le {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (p₂ : Polynomial ℕ) (a : α) :
    p₂.eval ((eb (f a)).length) ≤ (p₂.comp (outputPoly h.tm h.time)).eval (ea a).length := by
  rw [Polynomial.eval_comp]
  exact eval_mono p₂ (encoded_output_length_le h a)

/-! ## Generic acceptance cases -/

section Acceptance

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Two nested pushes in one statement push twice.  This is why a machine whose statements push at
most once is a fact about that machine, not about TM2 machines in general. -/
theorem pushBound_nested (k : K) (f g : σ → Γ k) :
    pushBound (Stmt.push k f (Stmt.push k g Stmt.halt) : Stmt Γ Λ σ) = 2 := rfl

/-- A branch takes the larger of its two sides. -/
theorem pushBound_branch (c : σ → Bool) (q₁ q₂ : Stmt Γ Λ σ) :
    pushBound (Stmt.branch c q₁ q₂) = max (pushBound q₁) (pushBound q₂) := rfl

/-- `goto` ends the counted step, so it contributes nothing — a self-loop still has a finite
one-statement bound. -/
theorem pushBound_goto (f : σ → Λ) : pushBound (Stmt.goto f : Stmt Γ Λ σ) = 0 := rfl

@[simp] theorem opBound_goto (f : σ → Λ) : opBound (Stmt.goto f : Stmt Γ Λ σ) = 1 := rfl

/-- Popping a stack that *is* empty leaves the total unchanged.  This assumes emptiness; the
unrestricted statement is `mass_update_tail_le`, which needs no such hypothesis. -/
theorem mass_pop_empty [DecidableEq K] [Fintype K] (S : ∀ k, List (Γ k)) (k : K) (hk : S k = []) :
    mass (Function.update S k (S k).tail) = mass S := by
  have h := mass_update S k (S k).tail
  rw [hk] at h ⊢
  simpa using h

end Acceptance

end PCP.Machine
