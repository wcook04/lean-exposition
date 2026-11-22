/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowVerdict

/-!
# Exact Hadamard acceptance from stored received answers

The complete numeric checker is tied to the executable verifier on every received
row, without an honesty or consistency assumption on the answers.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard

variable {t r : ℕ}

def checkSetup : Stmt 100 32 :=
  .seq (.copy 29 25) (.seq readPrefix prefixCheck)

theorem checkSetup_run (b a z u lp l : ℕ) (ps : List (ℕ × ℕ)) (st : State 100 32)
    (h : st.lists 29 = b :: a :: z :: u :: lp :: l :: pairAnswers ps) :
    (checkSetup.run st).1.regs 63 = prefixVerdict b a z u lp l ∧
      (checkSetup.run st).1.regs 74 = b ∧
      (checkSetup.run st).1.regs 69 = (lp + b) % 2 ∧
      (checkSetup.run st).1.regs 61 = 1 ∧ (checkSetup.run st).1.regs 62 = 2 ∧
      (checkSetup.run st).1.regs 56 = st.regs 56 ∧
      (checkSetup.run st).1.lists 25 = pairAnswers ps := by
  let v := setList st 25 (st.lists 29)
  have hh := readPrefix_run b a z u lp l (pairAnswers ps) v (by simpa [v] using h)
  have h56 := run_regs_frame readPrefix 56 (by decide) v
  dsimp only [v] at hh h56
  simp only [checkSetup, run_seq_fst, run_copy_fst]
  generalize hv : (readPrefix.run (setList st 25 (st.lists 29))).1 = v at *
  have hc := prefixCheck_run v
  have h74 := run_regs_frame prefixCheck 74 (by decide) v
  have h56' := run_regs_frame prefixCheck 56 (by decide) v
  have h25 := run_lists_frame prefixCheck 25 (by decide) v
  generalize hw : (prefixCheck.run v).1 = w at *
  refine ⟨?_, h74.trans hh.1, ?_, hc.2.2.1, hc.2.2.2, h56'.trans h56,
    h25.trans hh.2.2.2.2.2.2⟩
  · simpa only [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1,
      hh.2.2.2.2.2.1] using hc.1
  · simpa only [hh.1, hh.2.2.2.2.1] using hc.2.1

def checkAnswers : Stmt 100 32 :=
  .seq checkSetup (.seq (.assign 58 (.sub 56 61)) (.loop 58 factorCheck))

theorem checkAnswers_run (b a z u lp l : ℕ) (ps : List (ℕ × ℕ)) (st : State 100 32)
    (h : st.lists 29 = b :: a :: z :: u :: lp :: l :: pairAnswers ps)
    (hlen : st.regs 56 - 1 = ps.length) :
    (checkAnswers.run st).1.regs 63 =
      prefixVerdict b a z u lp l * factorVerdicts b ((lp + b) % 2) ps := by
  have hs := checkSetup_run b a z u lp l ps st h
  simp only [checkAnswers, run_seq_fst]
  generalize hv : (checkSetup.run st).1 = v at *
  let w := setReg v 58 (v.regs 56 - v.regs 61)
  have hn : w.regs 58 = ps.length := by simp [w, hs.2.2.2.1, hs.2.2.2.2.2.1, hlen]
  have hh := factorCheck_iterate ps (Nat.size ps.length + 1) w hs.2.2.2.2.2.2
    (by simpa [w, Function.update] using hs.2.2.2.2.1)
  simp only [run_assign_fst, Expr.eval, run_loop_fst]
  change (iterate factorCheck.run (Nat.size (w.regs 58) + 1) (w.regs 58) w).1.regs 63 = _
  rw [hn, hh]
  simp [w, Function.update, hs.1, hs.2.1, hs.2.2.1]

theorem decide_mul (P Q : Prop) [Decidable P] [Decidable Q] :
    (decide P).toNat * (decide Q).toNat = (decide (P ∧ Q)).toNat := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem factorVerdicts_eq (b lp : ZMod 2) (ps : List (ZMod 2 × ZMod 2)) :
    factorVerdicts b.val (lp - b).val (ps.map fun x => (x.1.val, x.2.val)) =
      (decide (∀ x ∈ ps, x.1 - b = (lp - b) * (x.2 - b))).toNat := by
  induction ps with
  | nil => simp [factorVerdicts]
  | cons pf ps ih =>
      simp only [List.map_cons, factorVerdicts, List.prod_cons, factorVerdict_eq]
      change (decide (pf.1 - b = (lp - b) * (pf.2 - b))).toNat *
        factorVerdicts b.val (lp - b).val (ps.map fun x => (x.1.val, x.2.val)) = _
      rw [ih, decide_mul]
      simp

def receivedPairs (H : Coefficients t r → ZMod 2) (s : TestRandomness t r) :
    List (ZMod 2 × ZMod 2) :=
  (List.finRange (r - 1)).map fun k =>
    (H (ComputableHadamardTest.productQuery s k + s.base),
      H (ComputableHadamardTest.factorQuery s k + s.base))

theorem received_trace (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (s : TestRandomness t r) :
    (ComputableHadamardTest.queries hr s).map (fun p => (H p).val) =
      (H s.base).val :: (H s.auxiliary).val :: (H (s.base + s.auxiliary)).val ::
        (H (BooleanCoefficientArithmetic.constant 1 + s.base)).val ::
          (H (ComputableHadamardTest.linearQuery hr s + s.base)).val ::
            (H (ComputableHadamardTest.linearQuery hr s)).val ::
              pairAnswers ((receivedPairs H s).map fun x => (x.1.val, x.2.val)) := by
  simp only [ComputableHadamardTest.queries, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.map_flatMap, pairAnswers, receivedPairs,
    List.map_map, List.flatMap_map, Function.comp_def]

/-- Complete acceptance is the exact named executable Hadamard test. -/
theorem checkAnswers_test (hr : 1 ≤ r) (H : Coefficients t r → ZMod 2)
    (s : TestRandomness t r) (st : State 100 32) (hrg : st.regs 56 = r)
    (h : st.lists 29 = (ComputableHadamardTest.queries hr s).map (fun p => (H p).val)) :
    (checkAnswers.run st).1.regs 63 = (ComputableHadamardTest.test hr H s).toNat := by
  rw [received_trace hr H s] at h
  have hh := checkAnswers_run _ _ _ _ _ _ _ st h
    (by simp [hrg, receivedPairs])
  rw [hh, prefixVerdict_eq]
  have hdelta (x y : ZMod 2) : (x.val + y.val) % 2 = (x - y).val := by
    fin_cases x <;> fin_cases y <;> decide
  rw [hdelta, factorVerdicts_eq, decide_mul]
  apply congrArg Bool.toNat
  apply Bool.eq_iff_iff.mpr
  simp [ComputableHadamardTest.test, ComputableHadamardTest.Accepts, receivedPairs, and_assoc]

end PCP.Lang.HadamardRow
