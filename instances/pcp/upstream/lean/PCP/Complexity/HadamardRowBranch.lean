/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardRowAcceptance
import PCP.Complexity.HadamardRowQueriesCost

/-!
# A complete physical Hadamard row branch

This one program computes the actual labels, materializes global proof addresses,
reads the supplied global history with earliest-match precedence, and evaluates
the exact executable Hadamard verdict. All eight physical row locations are covered.
-/

set_option maxRecDepth 4096

namespace PCP.Lang.HadamardRow

open PCP.Algebraic BinaryPolynomialSpace Hadamard HadamardLabel

variable {t r : ℕ}

def rowRegs : Fin 80 → Fin 100 := Fin.castLE (by decide)

def Sources (s : TestRandomness t r) (st : State 100 32) : Prop :=
  Context s (st.restrict rowRegs id)

def labels : Stmt 100 32 := queries.rename rowRegs id

theorem labels_run (hr : 1 ≤ r) (s : TestRandomness t r) (st : State 100 32)
    (hc : Sources s st) :
    Sources s (labels.run st).1 ∧
      (labels.run st).1.lists 24 = (ComputableHadamardTest.queries hr s).map code := by
  have h := congrArg Prod.fst (queries.run_rename rowRegs id
    (Fin.castLE_injective _) Function.injective_id st)
  have hh := queries_run hr s (st.restrict rowRegs id) hc
  rw [show queries.rename rowRegs id = labels from rfl] at h
  generalize hu : (labels.run st).1 = u at *
  rw [← h] at hh
  exact hh

theorem labels_payload (p : Fin 10 → ℕ) (st : State 100 32) (hp : Payload p st) :
    Payload p (labels.run st).1 := by
  intro i
  have hf := queries.run_rename_reg_outside rowRegs id (payloadReg i) (by
    intro j h
    have hh := congrArg Fin.val h
    dsimp [rowRegs, payloadReg] at hh
    omega) st
  simpa only [labels] using hf.trans (hp i)

theorem labels_frame (st : State 100 32) :
    (labels.run st).1.lists 27 = st.lists 27 ∧
      (labels.run st).1.lists 30 = st.lists 30 ∧
      (labels.run st).1.lists 31 = st.lists 31 := by
  exact ⟨run_lists_frame labels 27 (by decide) st,
    run_lists_frame labels 30 (by decide) st,
    run_lists_frame labels 31 (by decide) st⟩

/-- A row oracle induced by the actual physical global history. -/
def receivedOracle (p : Fin 10 → ℕ) (hs : List ℕ) (bs : List Bool)
    (z : Coefficients t r) : ZMod 2 :=
  ((QueryTree.answersOracle hs bs (address p (code z))).toNat : ZMod 2)

theorem receivedOracle_val (p : Fin 10 → ℕ) (hs : List ℕ) (bs : List Bool)
    (z : Coefficients t r) :
    (receivedOracle p hs bs z).val =
      (QueryTree.answersOracle hs bs (address p (code z))).toNat := by
  unfold receivedOracle
  cases QueryTree.answersOracle hs bs (address p (code z)) <;> rfl

/-- Label arithmetic, global addressing, history reads, and the verdict in one fixed program. -/
def branch : Stmt 100 32 :=
  .seq labels (.seq physicalQueries (.seq collectAnswers checkAnswers))

theorem branch_run (hr : 1 ≤ r) (s : TestRandomness t r) (p : Fin 10 → ℕ)
    (hs : List ℕ) (bs : List Bool) (st : State 100 32)
    (hc : Sources s st) (hp : Payload p st)
    (hq : st.lists 30 = hs) (hb : st.lists 31 = bs.map Bool.toNat) :
    (branch.run st).1.lists 26 =
      (ComputableHadamardTest.queries hr s).map (fun z => address p (code z)) ∧
      (branch.run st).1.regs 63 =
        (ComputableHadamardTest.test hr (receivedOracle p hs bs) s).toNat := by
  have hl := labels_run hr s st hc
  have hlp := labels_payload p st hp
  have hlf := labels_frame st
  simp only [branch, run_seq_fst]
  generalize hu : (labels.run st).1 = u at *
  have he : u.lists 7 = [] := hl.1.2.2.1
  have hphys := physicalQueries_run p _ u hlp hl.2 he
  have hpf := physicalQueries_frame u
  have hpr := run_regs_frame physicalQueries 56 (by decide) u
  have hpe := run_lists_frame physicalQueries 7 (by decide) u
  generalize hv : (physicalQueries.run u).1 = v at *
  have hvq : v.lists 30 = hs := hpf.2.1.trans (hlf.2.1.trans hq)
  have hvb : v.lists 31 = bs.map Bool.toNat := hpf.2.2.trans (hlf.2.2.trans hb)
  have hans := collectAnswers_bool _ hs bs v hphys.2 (hpe.trans he) hvq hvb
  have hcf := collectAnswers_frame v
  have hcr := run_regs_frame collectAnswers 56 (by decide) v
  generalize hw : (collectAnswers.run v).1 = w at *
  have htrace : w.lists 29 = (ComputableHadamardTest.queries hr s).map
      (fun z => (receivedOracle p hs bs z).val) := by
    simpa only [List.map_map, Function.comp_def, receivedOracle_val] using hans
  have hdegree : w.regs 56 = r := hcr.trans (hpr.trans hl.1.2.1)
  have htest := checkAnswers_test hr (receivedOracle p hs bs) s w hdegree htrace
  have h26 := run_lists_frame checkAnswers 26 (by decide) w
  refine ⟨?_, htest⟩
  simpa only [List.map_map, Function.comp_def] using h26.trans (hcf.1.trans hphys.2)

/-- The complete immutable seed is retained, including the restored width register. -/
theorem branch_sources (hr : 1 ≤ r) (s : TestRandomness t r) (st : State 100 32)
    (hc : Sources s st) : Sources s (branch.run st).1 := by
  have hh := (labels_run hr s st hc).1
  simp only [branch, run_seq_fst]
  generalize hu : (labels.run st).1 = u at *
  let tail : Stmt 100 32 := .seq physicalQueries (.seq collectAnswers checkAnswers)
  have h20 := run_regs_frame tail 20 (by decide) u
  have h56 := run_regs_frame tail 56 (by decide) u
  have h7 := run_lists_frame tail 7 (by decide) u
  have hL20 := run_lists_frame tail 20 (by decide) u
  have h21 := run_lists_frame tail 21 (by decide) u
  have h22 := run_lists_frame tail 22 (by decide) u
  have h23 := run_lists_frame tail 23 (by decide) u
  change Sources s (tail.run u).1
  generalize hv : (tail.run u).1 = v at *
  exact ⟨h20.trans hh.1, h56.trans hh.2.1, h7.trans hh.2.2.1,
    hL20.trans hh.2.2.2.1, h21.trans hh.2.2.2.2.1,
    h22.trans hh.2.2.2.2.2.1, h23.trans hh.2.2.2.2.2.2⟩

/-- Caller-owned global histories are never changed. -/
theorem branch_history (st : State 100 32) :
    (branch.run st).1.lists 30 = st.lists 30 ∧
      (branch.run st).1.lists 31 = st.lists 31 := by
  exact ⟨run_lists_frame branch 30 (by decide) st,
    run_lists_frame branch 31 (by decide) st⟩

theorem branch_payload (p : Fin 10 → ℕ) (st : State 100 32) (hp : Payload p st) :
    Payload p (branch.run st).1 := by
  have hh := labels_payload p st hp
  simp only [branch, run_seq_fst]
  generalize hu : (labels.run st).1 = u at *
  intro i
  exact (run_regs_frame (.seq physicalQueries (.seq collectAnswers checkAnswers))
    (payloadReg i) (by fin_cases i <;> decide) u).trans (hh i)

/-- Specialization to any of the eight actual production proof tables. -/
theorem branch_location {F : Type*} {q n m c : ℕ} (eF : F ≃ Fin q)
    (loc : Location F n m c r) (hr : 1 ≤ r) (s : TestRandomness t r)
    (hs : List ℕ) (bs : List Bool) (st : State 100 32) (hc : Sources s st)
    (hp : Payload (loc.payload (t := t) eF) st)
    (hq : st.lists 30 = hs) (hb : st.lists 31 = bs.map Bool.toNat) :
    (branch.run st).1.lists 26 = (ComputableHadamardTest.queries hr s).map
      (fun z => (ThreeColorQueryIndex.equiv eF (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) (loc.query z)).val) ∧
      (branch.run st).1.regs 63 = (ComputableHadamardTest.test hr
        (fun z => ((QueryTree.answersOracle hs bs (ThreeColorQueryIndex.equiv eF
          (BooleanCoefficientIndex.coefficientEquiv t 1)
          (BooleanCoefficientIndex.coefficientEquiv t 3)
            (loc.query z)).val).toNat : ZMod 2)) s).toNat := by
  have ho : (receivedOracle (loc.payload (t := t) eF) hs bs : Coefficients t r → ZMod 2) =
      fun z => ((QueryTree.answersOracle hs bs (ThreeColorQueryIndex.equiv eF
        (BooleanCoefficientIndex.coefficientEquiv t 1)
        (BooleanCoefficientIndex.coefficientEquiv t 3) (loc.query z)).val).toNat : ZMod 2) := by
    funext z
    rw [receivedOracle, loc.address_eq]
  have hh := branch_run hr s (loc.payload (t := t) eF) hs bs st hc hp hq hb
  rw [ho] at hh
  simpa only [loc.address_eq] using hh

end PCP.Lang.HadamardRow
