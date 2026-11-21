/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryPolynomialMaskScan

/-!
# Exhaustive irreducibility testing by counted loops

The degree loop maintains `2^d` by one doubling per iteration and calls the
joint-mask factor scan only at proper positive factor degrees. Its stored flag
is exactly the semantic irreducibility test used by the production field.
-/

namespace PCP.Lang.BinaryPolynomialDegreeScan

open PCP.Algebraic BinaryPolynomialCoefficient BinaryPolynomialFactor BooleanLoops
open BinaryPolynomialMaskScan

def degreePrepare : Stmt 32 2 :=
  .seq (.assign 8 (.var 24)) (.assign 9 (.sub 20 24))

def degreeCheck : Stmt 32 2 := .seq degreePrepare maskScan

theorem degreeCheck_run (st : State 32 2) (h30 : st.regs 30 = 1) :
    (degreeCheck.run st).1.regs 27 = st.regs 27 * truth
      (AllBelow (NoFactor (st.regs 20) (st.regs 21) (st.regs 24)
        (st.regs 20 - st.regs 24) (st.regs 29)) (st.regs 28)) := by
  let s := setReg (setReg st 8 (st.regs 24)) 9 (st.regs 20 - st.regs 24)
  have h := maskScan_run (st.regs 20) (st.regs 21) (st.regs 24)
    (st.regs 20 - st.regs 24) (st.regs 28) (st.regs 29) s
    (by simp [Context, s, Function.update, h30])
  simp only [degreeCheck, degreePrepare, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update_of_ne (by decide : (20 : Fin 32) ≠ 8),
    Function.update_of_ne (by decide : (24 : Fin 32) ≠ 8)]
  simpa only [s, setReg_regs, Function.update_of_ne (by decide : (27 : Fin 32) ≠ 9),
    Function.update_of_ne (by decide : (27 : Fin 32) ≠ 8)] using h

def degreeGuard : Stmt 32 2 :=
  .seq (.assign 0 (.const 0)) (.seq (.assign 1 (.lt 0 24))
    (.seq (.assign 2 (.lt 24 20)) (.assign 3 (.mul 1 2))))

def degreeConditional : Stmt 32 2 := .seq degreeGuard (.ite 3 degreeCheck .skip)

def degreeAdvance : Stmt 32 2 :=
  .seq (.assign 24 (.add 24 30))
    (.seq (.assign 0 (.const 2)) (.assign 29 (.mul 29 0)))

def degreeBody : Stmt 32 2 := .seq degreeConditional degreeAdvance

def DegreeGood (t code d : ℕ) : Prop :=
  0 < d ∧ d < t → AllBelow (NoFactor t code d (t - d) (2 ^ d)) (2 ^ t)

instance (t code d : ℕ) : Decidable (DegreeGood t code d) :=
  inferInstanceAs (Decidable
    (0 < d ∧ d < t → AllBelow (NoFactor t code d (t - d) (2 ^ d)) (2 ^ t)))

theorem degreeConditional_run (st : State 32 2) (h30 : st.regs 30 = 1) :
    (degreeConditional.run st).1.regs 27 = st.regs 27 * truth
      (0 < st.regs 24 ∧ st.regs 24 < st.regs 20 →
        AllBelow (NoFactor (st.regs 20) (st.regs 21) (st.regs 24)
          (st.regs 20 - st.regs 24) (st.regs 29)) (st.regs 28)) := by
  let s := (degreeGuard.run st).1
  have hs3 : s.regs 3 =
      (if 0 < st.regs 24 then 1 else 0) * (if st.regs 24 < st.regs 20 then 1 else 0) := by
    simp [s, degreeGuard, run_seq_fst, run_assign_fst, Expr.eval, Function.update]
  have h30' := (run_regs_frame degreeGuard 30 (by decide) st).trans h30
  have hc := degreeCheck_run s h30'
  have hs20 := run_regs_frame degreeGuard 20 (by decide) st
  have hs21 := run_regs_frame degreeGuard 21 (by decide) st
  have hs24 := run_regs_frame degreeGuard 24 (by decide) st
  have hs27 := run_regs_frame degreeGuard 27 (by decide) st
  have hs28 := run_regs_frame degreeGuard 28 (by decide) st
  have hs29 := run_regs_frame degreeGuard 29 (by decide) st
  change (degreeCheck.run s).1.regs 27 = _ at hc
  dsimp only [s] at hc
  simp only [hs20, hs21, hs24, hs27, hs28, hs29] at hc
  simp only [degreeConditional, run_seq_fst]
  change ((Stmt.ite 3 degreeCheck .skip).run s).1.regs 27 = _
  simp only [Stmt.run, hs3]
  by_cases hpos : 0 < st.regs 24 <;> by_cases hlt : st.regs 24 < st.regs 20
  · simpa only [hpos, hlt, ite_eq_left, Nat.mul_one, ne_eq, one_ne_zero, not_false_eq_true,
      truth, and_self, true_implies] using hc
  · simp [hpos, hlt, truth, s, hs27]
  · simp [hpos, hlt, truth, s, hs27]
  · simp [hpos, hlt, truth, s, hs27]

def DegreeContext (t code : ℕ) (st : State 32 2) : Prop :=
  st.regs 20 = t ∧ st.regs 21 = code ∧ st.regs 28 = 2 ^ t ∧ st.regs 30 = 1

set_option maxHeartbeats 800000 in
-- Frame proofs inspect the complete fixed factor-check syntax.
theorem degreeBody_step (t code d : ℕ) (st : State 32 2)
    (hc : DegreeContext t code st) (hd : st.regs 24 = d) (hw : st.regs 29 = 2 ^ d) :
    DegreeContext t code (degreeBody.run st).1 ∧
      (degreeBody.run st).1.regs 24 = d + 1 ∧
      (degreeBody.run st).1.regs 29 = 2 ^ (d + 1) ∧
      (degreeBody.run st).1.regs 27 = st.regs 27 * truth (DegreeGood t code d) := by
  have hf := degreeConditional_run st hc.2.2.2
  have hs24 := run_regs_frame degreeConditional 24 (by decide) st
  have hs29 := run_regs_frame degreeConditional 29 (by decide) st
  have hs30 := run_regs_frame degreeConditional 30 (by decide) st
  rw [hd] at hs24
  rw [hw] at hs29
  rw [hc.2.2.2] at hs30
  simp only [hd, hw, hc.1, hc.2.1, hc.2.2.1] at hf
  have hctx : DegreeContext t code (degreeBody.run st).1 :=
    ⟨(run_regs_frame degreeBody 20 (by decide) st).trans hc.1,
      (run_regs_frame degreeBody 21 (by decide) st).trans hc.2.1,
      (run_regs_frame degreeBody 28 (by decide) st).trans hc.2.2.1,
      (run_regs_frame degreeBody 30 (by decide) st).trans hc.2.2.2⟩
  refine ⟨hctx, ?_⟩
  simp only [degreeBody, run_seq_fst]
  generalize hs : (degreeConditional.run st).1 = s at *
  simp only [degreeAdvance, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false,
    hs24, hs29, hs30, hf, pow_succ, DegreeGood, true_and]
  rfl

/-- The field degree and candidate occupy `20,21`; `28` supplies `2^t`.
The result is a Boolean stored in register `27`. -/
def testCandidate : Stmt 32 2 :=
  .seq (.assign 24 (.const 0)) (.seq (.assign 29 (.const 1))
    (.seq (.assign 30 (.const 1)) (.seq (.assign 27 (.lt 24 20))
      (.seq (.assign 31 (.add 20 30)) (.loop 31 degreeBody)))))

def NumericPasses (t code : ℕ) : Prop := 0 < t ∧ AllBelow (DegreeGood t code) (t + 1)

instance (t code : ℕ) : Decidable (NumericPasses t code) :=
  inferInstanceAs (Decidable (0 < t ∧ AllBelow (DegreeGood t code) (t + 1)))

set_option maxHeartbeats 800000 in
-- The nested degree-loop invariant includes the accumulated finite truth value.
theorem testCandidate_run (t code : ℕ) (st : State 32 2)
    (h20 : st.regs 20 = t) (h21 : st.regs 21 = code) (h28 : st.regs 28 = 2 ^ t) :
    (testCandidate.run st).1.regs 27 = truth (NumericPasses t code) := by
  let s := setReg (setReg (setReg (setReg (setReg st 24 0) 29 1) 30 1)
    27 (truth (0 < t))) 31 (t + 1)
  have hit := iterate_inv degreeBody.run (Nat.size (t + 1) + 1) (t + 1)
    (fun n u => DegreeContext t code u ∧ u.regs 24 = n ∧ u.regs 29 = 2 ^ n ∧
      u.regs 27 = truth (0 < t) * truth (AllBelow (DegreeGood t code) n))
    (by
      intro n u _ hu
      obtain ⟨hc, hd, hw, hf⟩ := degreeBody_step t code n u hu.1 hu.2.1 hu.2.2.1
      refine ⟨hc, hd, hw, ?_⟩
      rw [hf, hu.2.2.2, truth_allBelow_succ, Nat.mul_assoc]) s
    (by simp [s, DegreeContext, Function.update, h20, h21, h28, truth, AllBelow])
  have hf := hit.2.2.2
  simp only [testCandidate, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false, h20]
  change (iterate degreeBody.run (Nat.size (t + 1) + 1) (t + 1) s).1.regs 27 = _
  rw [hf]
  unfold NumericPasses truth
  split_ifs <;> simp_all

theorem numericPasses_iff (t : ℕ) (code : Fin (2 ^ t)) :
    NumericPasses t code.val ↔ BinaryIrreduciblePolynomial.Passes t code := by
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, fun d hd hdt => ?_⟩
    exact (allBelow_noFactor_iff t code d.val (by omega)).mp
      (h d.val (Finset.mem_range.mpr d.isLt) ⟨hd, hdt⟩)
  · rintro ⟨ht, h⟩
    refine ⟨ht, fun d hd hp => ?_⟩
    exact (allBelow_noFactor_iff t code d (by omega)).mpr
      (h ⟨d, Finset.mem_range.mp hd⟩ hp.1 hp.2)

end PCP.Lang.BinaryPolynomialDegreeScan
