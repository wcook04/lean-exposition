/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Registers.EmitSeq
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# Chaining a sequence of stages through pinned tape states

A machine assembled from many subroutines is a `TM.bigSeqTM` of stages, each carrying the tape
state from one pinned configuration to the next. `TM.bigSeqTM_hoareTime` already chains stages,
but only through the `EmitPred` state shape, whose output component is a written list. A stage
that leaves a counter tape half-scanned, or two tallies at different values, does not fit that
shape.

The rule below chains through *arbitrary* pinned states — a fixed input tape, a family of work
banks, and a family of output tapes — asking only that every pinned tape be `Parked`, which is
what makes the phase transitions between stages no-ops.

## Main results

- `TM.bigSeqTM_hoareTime_pinned_gen` — the chain rule for arbitrary pinned tape states, input
  tape included
- `TM.bigSeqTM_hoareTime_pinned` — the same with a fixed input tape
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **Chaining stages through pinned tape states.** Stage `k` carries the pinned state `k` to the
pinned state `k + 1`; the fold carries state `0` to state `ms.length`. Every pinned tape is
required `Parked`, which makes the phase transition between consecutive stages a no-op.

The input tape is indexed too. A stage may move the input head — a rewind does — and then the
next stage's precondition names a different input tape, so a single fixed one will not do. -/
theorem bigSeqTM_hoareTime_pinned_gen :
    ∀ (ms : List (TM n)) (I : ℕ → Tape) (W : ℕ → Fin n → Tape) (O : ℕ → Tape) (b : ℕ),
      (∀ k, Parked (I k)) → (∀ k i, Parked (W k i)) → (∀ k, Parked (O k)) →
      (∀ k, (hk : k < ms.length) →
        ms[k].HoareTime (fun inp work out => inp = I k ∧ work = W k ∧ out = O k)
          (fun inp work out => inp = I (k + 1) ∧ work = W (k + 1) ∧ out = O (k + 1)) b) →
      (bigSeqTM ms).HoareTime
        (fun inp work out => inp = I 0 ∧ work = W 0 ∧ out = O 0)
        (fun inp work out => inp = I ms.length ∧ work = W ms.length ∧ out = O ms.length)
        (ms.length * (b + 1) + 1) := by
  intro ms
  induction ms with
  | nil =>
      intro I W O b hI hW hO _
      exact (skipTM_hoareTime_frame (I 0) (W 0) (O 0) (hI 0) (hW 0) (hO 0)).mono_bound (by simp)
  | cons m ms ih =>
      intro I W O b hI hW hO hms
      have hhead := hms 0 (by simp)
      have hrest := ih (fun k => I (k + 1)) (fun k => W (k + 1)) (fun k => O (k + 1)) b
        (fun k => hI (k + 1)) (fun k i => hW (k + 1) i) (fun k => hO (k + 1))
        (fun k hk => by
          have h := hms (k + 1) (by simpa using Nat.succ_lt_succ hk)
          simpa using h)
      have htrans : ∀ inp work out,
          (inp = I 1 ∧ work = W 1 ∧ out = O 1) →
          (transitionInput inp = I 1 ∧ (fun i => transitionTape (work i)) = W 1 ∧
            transitionTape out = O 1) := by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        refine ⟨transitionInput_eq_self ((hI 1).read_ne_start), funext fun i => ?_,
          transitionTape_eq_self ((hO 1).read_ne_start)⟩
        exact transitionTape_eq_self ((hW 1 i).read_ne_start)
      have hseq := seqTM_hoareTime m (bigSeqTM ms) hhead htrans hrest
      refine hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => ?_) ?_
      · show (_ = I (m :: ms).length ∧ _ = W (m :: ms).length ∧ _ = O (m :: ms).length)
        rw [List.length_cons]
        exact h
      · rw [List.length_cons]
        have hmul : (ms.length + 1) * (b + 1) = ms.length * (b + 1) + (b + 1) := Nat.succ_mul ..
        omega

/-- **The chain rule with a fixed input tape**, the common case: no stage moves the input head. -/
theorem bigSeqTM_hoareTime_pinned (ms : List (TM n)) (I : Tape) (W : ℕ → Fin n → Tape)
    (O : ℕ → Tape) (b : ℕ)
    (hI : Parked I) (hW : ∀ k i, Parked (W k i)) (hO : ∀ k, Parked (O k))
    (hms : ∀ k, (hk : k < ms.length) →
      ms[k].HoareTime (fun inp work out => inp = I ∧ work = W k ∧ out = O k)
        (fun inp work out => inp = I ∧ work = W (k + 1) ∧ out = O (k + 1)) b) :
    (bigSeqTM ms).HoareTime
      (fun inp work out => inp = I ∧ work = W 0 ∧ out = O 0)
      (fun inp work out => inp = I ∧ work = W ms.length ∧ out = O ms.length)
      (ms.length * (b + 1) + 1) :=
  bigSeqTM_hoareTime_pinned_gen ms (fun _ => I) W O b (fun _ => hI) hW hO hms

end TM

end Complexity
