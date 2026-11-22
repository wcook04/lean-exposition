/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialDegreeCost

/-!
# Counted-loop selection of the production irreducible polynomial

All masks below `2^t` are tested with the concrete coefficient-convolution
program. A stored minimum retains the least successful mask. Existence is used
only to prove the result equals the production selector, not to run the search.
-/

namespace PCP.Lang.BinaryPolynomialSelector

open PCP.Algebraic BinaryPolynomialDegreeScan BooleanLoops

def testEmbedding : Fin 32 → Fin 36 := Fin.castLE (by decide)
def test36 : Stmt 36 2 := testCandidate.rename testEmbedding id

set_option maxHeartbeats 800000 in
-- Register transport traverses the fixed nested factor enumeration program.
theorem test36_run (st : State 36 2) (t code : ℕ)
    (h20 : st.regs 20 = t) (h21 : st.regs 21 = code) (h28 : st.regs 28 = 2 ^ t) :
    (test36.run st).1.regs 27 = truth (NumericPasses t code) := by
  have h := congrArg (fun z : State 32 2 × ℕ => z.1.regs 27)
    (testCandidate.run_rename testEmbedding id (Fin.castLE_injective _)
      Function.injective_id st)
  exact h.trans (testCandidate_run t code _ h20 h21 h28)

def candidateCheck : Stmt 36 2 := .seq (.assign 21 (.var 32)) test36

def candidateTail : Stmt 36 2 :=
  .seq (.assign 0 (.lt 32 33)) (.seq (.assign 0 (.mul 0 27))
    (.seq (.ite 0 (.assign 33 (.var 32)) .skip) (.assign 32 (.add 32 35))))

def candidateBody : Stmt 36 2 := .seq candidateCheck candidateTail

theorem candidateCheck_run (st : State 36 2) (t : ℕ)
    (h20 : st.regs 20 = t) (h28 : st.regs 28 = 2 ^ t) :
    (candidateCheck.run st).1.regs 27 = truth (NumericPasses t (st.regs 32)) := by
  simp only [candidateCheck, run_seq_fst, run_assign_fst, Expr.eval]
  apply test36_run
  · simpa only [setReg_regs, Function.update_of_ne (by decide : (20 : Fin 36) ≠ 21)] using h20
  · simp
  · simpa only [setReg_regs, Function.update_of_ne (by decide : (28 : Fin 36) ≠ 21)] using h28

theorem candidateTail_step (st : State 36 2) (h35 : st.regs 35 = 1)
    (P : Prop) [Decidable P] (h27 : st.regs 27 = truth P) :
    (candidateTail.run st).1.regs 33 =
      (if P then min (st.regs 33) (st.regs 32) else st.regs 33) ∧
    (candidateTail.run st).1.regs 32 = st.regs 32 + 1 := by
  simp only [candidateTail, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false, h27]
  unfold truth
  by_cases hp : P <;> by_cases hlt : st.regs 32 < st.regs 33
  · simp [hp, hlt, Stmt.run, Expr.eval, Function.update, h35, min_eq_right hlt.le]
  · simp [hp, hlt, Stmt.run, Function.update, h35, min_eq_left (Nat.le_of_not_gt hlt)]
  · simp [hp, hlt, Stmt.run, Function.update, h35]
  · simp [hp, hlt, Stmt.run, Function.update, h35]

theorem candidateBody_step (st : State 36 2) (t : ℕ)
    (h20 : st.regs 20 = t) (h28 : st.regs 28 = 2 ^ t) (h35 : st.regs 35 = 1) :
    (candidateBody.run st).1.regs 33 =
      (if NumericPasses t (st.regs 32) then min (st.regs 33) (st.regs 32) else st.regs 33) ∧
    (candidateBody.run st).1.regs 32 = st.regs 32 + 1 := by
  have hs27 := candidateCheck_run st t h20 h28
  have hs32 := run_regs_frame candidateCheck 32 (by decide) st
  have hs33 := run_regs_frame candidateCheck 33 (by decide) st
  have hs35 := run_regs_frame candidateCheck 35 (by decide) st
  simp only [candidateBody, run_seq_fst]
  generalize hs : (candidateCheck.run st).1 = s at *
  have h := candidateTail_step s (hs35.trans h35) _ hs27
  simpa only [hs32, hs33] using h

/-- Invariant of a bounded minimum scan, with the bound as the initial sentinel. -/
def LeastInv (P : ℕ → Prop) (q n r : ℕ) : Prop :=
  r ≤ q ∧ (r < q → P r) ∧ ∀ i < n, P i → r ≤ i

theorem leastInv_zero (P : ℕ → Prop) (q : ℕ) : LeastInv P q 0 q := by
  simp [LeastInv]

theorem leastInv_step (P : ℕ → Prop) [DecidablePred P] (q n r : ℕ)
    (_hn : n < q) (h : LeastInv P q n r) :
    LeastInv P q (n + 1) (if P n then min r n else r) := by
  obtain ⟨hr, hgood, hmin⟩ := h
  by_cases hp : P n
  · simp only [hp, ite_eq_left]
    refine ⟨(min_le_left _ _).trans hr, ?_, ?_⟩
    · intro hm
      rcases le_total r n with hle | hle
      · rw [min_eq_left hle] at hm ⊢
        exact hgood hm
      · simpa only [min_eq_right hle] using hp
    · intro i hi hpi
      by_cases hi' : i < n
      · exact (min_le_left _ _).trans (hmin i hi' hpi)
      · have heq : i = n := by omega
        subst i
        exact min_le_right _ _
  · simp only [hp]
    refine ⟨hr, hgood, fun i hi hpi => ?_⟩
    apply hmin i
    · by_contra hi'
      have heq : i = n := by omega
      exact hp (heq ▸ hpi)
    · exact hpi

def SearchContext (t : ℕ) (st : State 36 2) : Prop :=
  st.regs 20 = t ∧ st.regs 28 = 2 ^ t ∧ st.regs 35 = 1

theorem candidateBody_frame (st : State 36 2) (r : Fin 36)
    (hr : r ∈ ([20, 28, 35] : List (Fin 36))) :
    (candidateBody.run st).1.regs r = st.regs r := by
  apply run_regs_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

theorem candidateBody_inv (t n : ℕ) (st : State 36 2) (hn : n < 2 ^ t)
    (hc : SearchContext t st) (hi : st.regs 32 = n)
    (hm : LeastInv (NumericPasses t) (2 ^ t) n (st.regs 33)) :
    SearchContext t (candidateBody.run st).1 ∧ (candidateBody.run st).1.regs 32 = n + 1 ∧
      LeastInv (NumericPasses t) (2 ^ t) (n + 1) ((candidateBody.run st).1.regs 33) := by
  have hs := candidateBody_step st t hc.1 hc.2.1 hc.2.2
  refine ⟨?_, hs.2.trans (by rw [hi]), ?_⟩
  · unfold SearchContext at hc ⊢
    rw [candidateBody_frame st 20 (by decide), candidateBody_frame st 28 (by decide),
      candidateBody_frame st 35 (by decide)]
    exact hc
  · rw [hs.1, hi]
    exact leastInv_step _ _ n _ hn hm

/-- Scan all candidate masks; `28` must contain `2^t`. The selected mask is in `33`. -/
def selectMask : Stmt 36 2 :=
  .seq (.assign 32 (.const 0)) (.seq (.assign 33 (.var 28))
    (.seq (.assign 35 (.const 1)) (.loop 28 candidateBody)))

theorem selectMask_invariant (t : ℕ) (st : State 36 2)
    (h20 : st.regs 20 = t) (h28 : st.regs 28 = 2 ^ t) :
    LeastInv (NumericPasses t) (2 ^ t) (2 ^ t) ((selectMask.run st).1.regs 33) := by
  let q := 2 ^ t
  let s := setReg (setReg (setReg st 32 0) 33 q) 35 1
  have h := iterate_inv candidateBody.run (Nat.size q + 1) q
    (fun n u => SearchContext t u ∧ u.regs 32 = n ∧
      LeastInv (NumericPasses t) q n (u.regs 33))
    (fun n u hn hu => candidateBody_inv t n u hn hu.1 hu.2.1 hu.2.2) s
    (by simp [s, SearchContext, Function.update, h20, h28, q, leastInv_zero])
  simp only [selectMask, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    setReg_regs, Function.update, Fin.reduceEq, dite_false, h28]
  exact h.2.2

/-- The program returns the identical least successful mask used by production fields. -/
theorem selectMask_run (t : ℕ) (ht : 0 < t) (st : State 36 2)
    (h20 : st.regs 20 = t) (h28 : st.regs 28 = 2 ^ t) :
    (selectMask.run st).1.regs 33 = (BinaryIrreduciblePolynomial.selectedCode t ht).val := by
  have h := selectMask_invariant t st h20 h28
  let i := BinaryIrreduciblePolynomial.selectedCode t ht
  have hi : NumericPasses t i.val := (numericPasses_iff t i).mpr
    (BinaryIrreduciblePolynomial.selectedCode_passes t ht)
  have hle := h.2.2 i.val i.isLt hi
  have hlt : (selectMask.run st).1.regs 33 < 2 ^ t := lt_of_le_of_lt hle i.isLt
  have hpasses := (numericPasses_iff t ⟨_, hlt⟩).mp (h.2.1 hlt)
  have hge := BinaryIrreduciblePolynomial.selectedCode_le ht ⟨_, hlt⟩ hpasses
  exact Nat.le_antisymm hle hge

end PCP.Lang.BinaryPolynomialSelector
