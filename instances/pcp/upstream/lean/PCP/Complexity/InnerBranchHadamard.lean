/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.InnerBranchState

/-! # The relocated physical Hadamard arm of the inner selector -/

namespace PCP.Lang.InnerBranch

open PCP.Algebraic BinaryPolynomialSpace InterpolationBranch

variable {t n m : ℕ} [NeZero t]

omit [NeZero t] in
theorem prepareHad_sources (s : Hadamard.TestRandomness t 1) (st : State 120 40)
    (hc : HadamardRow.Sources s (st.restrict hadRegs hadLists)) :
    HadamardRow.Sources s ((prepareHad.run st).1.restrict hadRegs hadLists) := by
  change st.regs 20 = t ∧ st.regs 56 = 1 ∧ st.lists 7 = [] ∧
    st.lists 20 = BooleanCoefficientList.encode s.base ∧
    st.lists 21 = BooleanCoefficientList.encode s.auxiliary ∧
    st.lists 22 = BooleanCoefficientList.encode s.linear ∧
    st.lists 23 = HadamardRow.factorCodes s at hc
  change (prepareHad.run st).1.regs 20 = t ∧ (prepareHad.run st).1.regs 56 = 1 ∧
    (prepareHad.run st).1.lists 7 = [] ∧
    (prepareHad.run st).1.lists 20 = BooleanCoefficientList.encode s.base ∧
    (prepareHad.run st).1.lists 21 = BooleanCoefficientList.encode s.auxiliary ∧
    (prepareHad.run st).1.lists 22 = BooleanCoefficientList.encode s.linear ∧
    (prepareHad.run st).1.lists 23 = HadamardRow.factorCodes s
  simpa only [prepareHad, run_seq_fst, run_copy_fst, setList_regs, setList_lists,
    Function.update, Fin.reduceEq, dite_false] using hc

theorem prepareHad_payload (p : Fin 10 → ℕ) (st : State 120 40)
    (hp : HadamardRow.Payload p (st.restrict hadRegs hadLists)) :
    HadamardRow.Payload p ((prepareHad.run st).1.restrict hadRegs hadLists) := by
  intro i
  simpa only [State.restrict_regs, prepareHad, run_seq_fst, run_copy_fst, setList_regs]
    using hp i

theorem prepareHad_histories (st : State 120 40) :
    (prepareHad.run st).1.lists 30 = st.lists 36 ∧
      (prepareHad.run st).1.lists 31 = st.lists 37 ∧
      (prepareHad.run st).1.lists 27 = st.lists 7 := by
  simp [prepareHad, Stmt.run, Function.update]

omit [NeZero t] in
theorem hadCall_run (site : StandardCorrection.Site (Field t) n) (x : Point t m)
    (s : Hadamard.TestRandomness t 1) (qs : List ℕ) (bs : List Bool) (st : State 120 40)
    (hc : HadamardRow.Sources s (st.restrict hadRegs hadLists))
    (hp : HadamardRow.Payload ((location site x).payload (t := t) (BinaryFieldCode.fieldEquiv t))
      (st.restrict hadRegs hadLists))
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat) :
    (hadCall.run st).1.lists 26 =
      (ComputableHadamardTest.queries (le_refl 1) s).map (address site x) ∧
      (hadCall.run st).1.regs 63 =
        (ComputableHadamardTest.test (le_refl 1) (oracle site qs bs x) s).toNat := by
  have h := HadamardRow.branch_location (BinaryFieldCode.fieldEquiv t)
    (location site x) (le_refl 1) s qs bs (st.restrict hadRegs hadLists) hc hp hq hb
  rw [← hadCall_result] at h
  generalize hout : (hadCall.run st).1 = out at *
  simp only [State.restrict_lists, State.restrict_regs, location_query] at h
  change out.lists 26 = _ ∧ out.regs 63 = _ at h
  have horacle : (fun p : Coefficients t 1 =>
      ((QueryTree.answersOracle qs bs (address site x p)).toNat : ZMod 2)) =
        oracle site qs bs x := by
    funext p
    unfold oracle
    cases QueryTree.answersOracle qs bs (address site x p) <;> rfl
  change _ = _ ∧ _ = (ComputableHadamardTest.test (le_refl 1)
    (fun p => ((QueryTree.answersOracle qs bs (address site x p)).toNat : ZMod 2)) s).toNat at h
  rw [horacle] at h
  exact h

omit [NeZero t] in
theorem hadamard_run (site : StandardCorrection.Site (Field t) n) (x : Point t m)
    (s : Hadamard.TestRandomness t 1) (qs : List ℕ) (bs : List Bool) (st : State 120 40)
    (hc : HadamardRow.Sources s (st.restrict hadRegs hadLists))
    (hp : HadamardRow.Payload ((location site x).payload (t := t) (BinaryFieldCode.fieldEquiv t))
      (st.restrict hadRegs hadLists))
    (hq : st.lists 36 = qs) (hb : st.lists 37 = bs.map Bool.toNat) :
    (hadamard.run st).1.lists 38 =
      (ComputableHadamardTest.queries (le_refl 1) s).map (address site x) ∧
      (hadamard.run st).1.regs 101 =
        (ComputableHadamardTest.test (le_refl 1) (oracle site qs bs x) s).toNat := by
  have hs := prepareHad_sources s st hc
  have hp' := prepareHad_payload _ st hp
  have hh := prepareHad_histories st
  have h := hadCall_run site x s qs bs (prepareHad.run st).1 hs hp'
    (hh.1.trans hq) (hh.2.1.trans hb)
  simp only [hadamard, run_seq_fst]
  generalize hu : (prepareHad.run st).1 = u at *
  generalize hv : (hadCall.run u).1 = v at *
  simpa only [run_copy_fst, run_assign_fst, Expr.eval, setList_regs,
    setReg_lists, setList_lists, setReg_regs, Function.update_self] using h

end PCP.Lang.InnerBranch
