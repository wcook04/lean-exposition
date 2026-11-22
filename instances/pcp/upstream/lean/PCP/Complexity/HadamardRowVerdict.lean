/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowHistory

/-!
# Arithmetic checks for a Hadamard row's received answers

The prefix tests and every factor equation are evaluated on the stored answers,
with binary addition implemented by reduction modulo two.
-/

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard

/-- Numeric form of the first three checks. -/
def prefixVerdict (b a z u lp l : ℕ) : ℕ :=
  if z = (b + a) % 2 ∧ (u + b) % 2 = 1 ∧ (lp + b) % 2 = l then 1 else 0

def readPrefix : Stmt 100 32 :=
  .seq (.pop 25 74 65) (.seq (.pop 25 75 65) (.seq (.pop 25 76 65)
    (.seq (.pop 25 77 65) (.seq (.pop 25 78 65) (.pop 25 79 65)))))

theorem readPrefix_run (b a z u lp l : ℕ) (rest : List ℕ) (st : State 100 32)
    (h : st.lists 25 = b :: a :: z :: u :: lp :: l :: rest) :
    (readPrefix.run st).1.regs 74 = b ∧ (readPrefix.run st).1.regs 75 = a ∧
      (readPrefix.run st).1.regs 76 = z ∧ (readPrefix.run st).1.regs 77 = u ∧
      (readPrefix.run st).1.regs 78 = lp ∧ (readPrefix.run st).1.regs 79 = l ∧
      (readPrefix.run st).1.lists 25 = rest := by
  simp [readPrefix, Stmt.run, Function.update, h]

def prefixCheck : Stmt 100 32 :=
  .seq (.assign 61 (.const 1)) (
  .seq (.assign 62 (.const 2)) (
  .seq (.assign 66 (.add 74 75)) (
  .seq (.assign 66 (.mod 66 62)) (
  .seq (.assign 67 (.eq 76 66)) (
  .seq (.assign 68 (.add 77 74)) (
  .seq (.assign 68 (.mod 68 62)) (
  .seq (.assign 68 (.eq 68 61)) (
  .seq (.assign 69 (.add 78 74)) (
  .seq (.assign 69 (.mod 69 62)) (
  .seq (.assign 70 (.eq 69 79)) (
  .seq (.assign 63 (.mul 67 68)) (
  .assign 63 (.mul 63 70)))))))))))))

theorem prefixCheck_run (st : State 100 32) :
    (prefixCheck.run st).1.regs 63 = prefixVerdict (st.regs 74) (st.regs 75)
      (st.regs 76) (st.regs 77) (st.regs 78) (st.regs 79) ∧
      (prefixCheck.run st).1.regs 69 = (st.regs 78 + st.regs 74) % 2 ∧
      (prefixCheck.run st).1.regs 61 = 1 ∧ (prefixCheck.run st).1.regs 62 = 2 := by
  by_cases h1 : st.regs 76 = (st.regs 74 + st.regs 75) % 2 <;>
    by_cases h2 : (st.regs 77 + st.regs 74) % 2 = 1 <;>
    by_cases h3 : (st.regs 78 + st.regs 74) % 2 = st.regs 79 <;>
    simp [prefixCheck, Stmt.run, Expr.eval, Function.update, prefixVerdict, h1, h2, h3]

/-- The numeric checks coincide with the finite-field equations. -/
theorem prefixVerdict_eq (b a z u lp l : ZMod 2) :
    prefixVerdict b.val a.val z.val u.val lp.val l.val =
      (decide (z = b + a ∧ u - b = 1 ∧ lp - b = l)).toNat := by
  fin_cases b <;> fin_cases a <;> fin_cases z <;> fin_cases u <;>
    fin_cases lp <;> fin_cases l <;> decide

/-- One multiplicative factor consistency equation. -/
def factorVerdict (b d p f : ℕ) : ℕ :=
  if (p + b) % 2 = d * ((f + b) % 2) then 1 else 0

def factorCheck : Stmt 100 32 :=
  .seq (.pop 25 66 65) (
  .seq (.pop 25 67 65) (
  .seq (.assign 68 (.add 66 74)) (
  .seq (.assign 68 (.mod 68 62)) (
  .seq (.assign 70 (.add 67 74)) (
  .seq (.assign 70 (.mod 70 62)) (
  .seq (.assign 70 (.mul 69 70)) (
  .seq (.assign 71 (.eq 68 70)) (
  .assign 63 (.mul 63 71)))))))))

theorem factorCheck_run (p f : ℕ) (rest : List ℕ) (st : State 100 32)
    (h : st.lists 25 = p :: f :: rest) (htwo : st.regs 62 = 2) :
    (factorCheck.run st).1.regs 63 =
      st.regs 63 * factorVerdict (st.regs 74) (st.regs 69) p f ∧
      (factorCheck.run st).1.lists 25 = rest := by
  simp [factorCheck, Stmt.run, Expr.eval, Function.update, h, htwo, factorVerdict]

theorem factorVerdict_eq (b lp p f : ZMod 2) :
    factorVerdict b.val (lp - b).val p.val f.val =
      (decide (p - b = (lp - b) * (f - b))).toNat := by
  fin_cases b <;> fin_cases lp <;> fin_cases p <;> fin_cases f <;> decide

def pairAnswers (ps : List (ℕ × ℕ)) : List ℕ := ps.flatMap fun x => [x.1, x.2]

def factorVerdicts (b d : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  (ps.map fun x => factorVerdict b d x.1 x.2).prod

theorem factorCheck_iterate (ps : List (ℕ × ℕ)) (c : ℕ) (st : State 100 32)
    (h : st.lists 25 = pairAnswers ps) (htwo : st.regs 62 = 2) :
    (iterate factorCheck.run c ps.length st).1.regs 63 =
      st.regs 63 * factorVerdicts (st.regs 74) (st.regs 69) ps := by
  induction ps generalizing st with
  | nil => simp [factorVerdicts, iterate]
  | cons pf ps ih =>
      have hin : st.lists 25 = pf.1 :: pf.2 :: pairAnswers ps := h
      have hs := factorCheck_run pf.1 pf.2 (pairAnswers ps) st hin htwo
      have h62 := run_regs_frame factorCheck 62 (by decide) st
      have h74 := run_regs_frame factorCheck 74 (by decide) st
      have h69 := run_regs_frame factorCheck 69 (by decide) st
      simp only [List.length_cons, iterate_succ_fst]
      generalize hu : (factorCheck.run st).1 = u at *
      rw [ih u hs.2 (h62.trans htwo), hs.1, h74, h69]
      simp only [factorVerdicts, List.map_cons, List.prod_cons, Nat.mul_assoc]

end PCP.Lang.HadamardRow
