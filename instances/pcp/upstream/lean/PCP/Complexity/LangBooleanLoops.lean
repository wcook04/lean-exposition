/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.LangCost
import Mathlib.Data.Finset.Range

/-!
# Finite universal scans in the counted-loop language

The flag is a stored zero-or-one natural number. Each loop stage multiplies it by
the next decidable truth value. The operational invariant also retains a caller
context, allowing nested finite searches without an unbounded search primitive.
-/

namespace PCP.Lang.BooleanLoops

def truth (P : Prop) [Decidable P] : ℕ := if P then 1 else 0

def AllBelow (P : ℕ → Prop) (n : ℕ) : Prop := ∀ i ∈ Finset.range n, P i

instance (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : Decidable (AllBelow P n) :=
  inferInstanceAs (Decidable (∀ i ∈ Finset.range n, P i))

theorem allBelow_succ (P : ℕ → Prop) (n : ℕ) :
    AllBelow P (n + 1) ↔ AllBelow P n ∧ P n := by
  simp [AllBelow, Finset.range_add_one, and_comm]

theorem truth_allBelow_succ (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    truth (AllBelow P (n + 1)) = truth (AllBelow P n) * truth (P n) := by
  simp only [truth, allBelow_succ]
  split_ifs <;> simp_all

theorem truth_lt_two (P : Prop) [Decidable P] : truth P < 2 := by
  unfold truth
  split_ifs <;> decide

/-- A universal finite scan with an arbitrary incoming accumulated flag. -/
theorem iterate_all {R Q : ℕ} (f : State R Q → State R Q × ℕ) (c N : ℕ)
    (index flag : Fin R) (C : State R Q → Prop) (P : ℕ → Prop) [DecidablePred P]
    (hstep : ∀ n st, n < N → C st → st.regs index = n →
      C (f st).1 ∧ (f st).1.regs index = n + 1 ∧
        (f st).1.regs flag = st.regs flag * truth (P n))
    (st : State R Q) (hC : C st) (hi : st.regs index = 0) :
    C (iterate f c N st).1 ∧ (iterate f c N st).1.regs index = N ∧
      (iterate f c N st).1.regs flag = st.regs flag * truth (AllBelow P N) := by
  have h := iterate_inv f c N
    (fun n s => C s ∧ s.regs index = n ∧
      s.regs flag = st.regs flag * truth (AllBelow P n))
    (by
      intro n s hn hs
      obtain ⟨hc, hi, hf⟩ := hstep n s hn hs.1 hs.2.1
      refine ⟨hc, hi, ?_⟩
      rw [hf, hs.2.2, truth_allBelow_succ, Nat.mul_assoc]) st
    ⟨hC, hi, by simp [truth, AllBelow]⟩
  exact h

/-- The same scan's charged bound, with a separately proved stage cost. -/
theorem iterate_all_cost {R Q : ℕ} (f : State R Q → State R Q × ℕ) (c N B : ℕ)
    (index flag : Fin R) (C : State R Q → Prop) (P : ℕ → Prop) [DecidablePred P]
    (hstep : ∀ n st, n < N → C st → st.regs index = n →
      C (f st).1 ∧ (f st).1.regs index = n + 1 ∧
        (f st).1.regs flag = st.regs flag * truth (P n))
    (hcost : ∀ n st, n < N → C st → st.regs index = n → st.regs flag < 2 → (f st).2 ≤ B)
    (st : State R Q) (hC : C st) (hi : st.regs index = 0) (hf : st.regs flag < 2) :
    (iterate f c N st).2 ≤ N * (c + B) := by
  apply iterate_cost_idx f c B N
    (fun n s => C s ∧ s.regs index = n ∧ s.regs flag < 2)
  · intro n s hn hs
    obtain ⟨hc, hi, hf'⟩ := hstep n s hn hs.1 hs.2.1
    refine ⟨⟨hc, hi, ?_⟩, hcost n s hn hs.1 hs.2.1 hs.2.2⟩
    rw [hf']
    have hp := truth_lt_two (P n)
    have hflag := hs.2.2
    have hprod := Nat.mul_le_mul (show s.regs flag ≤ 1 by omega)
      (show truth (P n) ≤ 1 by omega)
    omega
  · exact ⟨hC, hi, hf⟩

end PCP.Lang.BooleanLoops
