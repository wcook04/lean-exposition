/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Hoare

/-!
# Running a loop a fixed number of times

`TM.loopTM_hoareTime` proves a loop terminates from an invariant and a decreasing variant. A
counting loop has a more specific shape: its tape state is indexed by how many iterations have
run, the index advances by one each time, and the loop stops at a known count. The rule below
packages that shape, so a client supplies only two facts — one iteration advances the index, and
the loop halts at the final index — with the fuel bookkeeping discharged here.

The index has to be readable from the tapes, since `TM.loopTM_hoareTime`'s variant is a function
of them; in practice it is the counter the loop is iterating.

## Main results

- `TM.loopTM_hoareTime_indexed` — a loop that runs to a known iteration count
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **A loop that runs to a known iteration count.** `E j` describes the tapes after `j`
iterations and `idx` reads the index back off them. Given that one iteration carries `E j` to
`E (j + 1)` for every `j` below `N`, and that the loop halts from `E N` with `post`, the loop
carries `E 0` to `post`. -/
theorem loopTM_hoareTime_indexed (tmBody tmTest : TM n)
    {E : ℕ → TapePred n} {post : TapePred n} {N b : ℕ}
    {idx : Tape → (Fin n → Tape) → Tape → ℕ}
    (hidx : ∀ j inp work out, E j inp work out → idx inp work out = j)
    (hstep : ∀ j, j < N → ∀ inp work out, E j inp work out →
      ∃ inp' work' out' t, t ≤ b ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩
          ⟨(loopTM tmBody tmTest).qstart, inp', work', out'⟩ ∧
        E (j + 1) inp' work' out')
    (hstop : ∀ inp work out, E N inp work out →
      ∃ c' t, t ≤ b ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (loopTM tmBody tmTest).halted c' ∧ post c'.input c'.work c'.output) :
    (loopTM tmBody tmTest).HoareTime
      (E 0) post ((N + 1) * b) := by
  refine (loopTM_hoareTime tmBody tmTest
    (inv := fun inp work out => ∃ j ≤ N, E j inp work out)
    (variant := fun inp work out => N - idx inp work out)
    (b_iter := b) (k := N) (fun inp work out _ => Nat.sub_le N _) ?_).consequence
    (fun inp work out h => ⟨0, Nat.zero_le N, h⟩) (fun _ _ _ h => h) (le_refl _)
  rintro inp work out ⟨j, hjN, hEj⟩
  rcases Nat.lt_or_ge j N with hlt | hge
  · obtain ⟨inp', work', out', t, ht, hreach, hE'⟩ := hstep j hlt inp work out hEj
    refine Or.inr ⟨inp', work', out', t, ht, hreach, ⟨j + 1, by omega, hE'⟩, ?_⟩
    show N - idx inp' work' out' < N - idx inp work out
    rw [hidx j inp work out hEj, hidx (j + 1) inp' work' out' hE']
    omega
  · have hjeq : j = N := by omega
    subst hjeq
    exact Or.inl (hstop inp work out hEj)

end TM

end Complexity
