/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.HadamardSeedCardinal

/-!
# Materializing the decoded Hadamard seed

Factor codes remain stored numbers. The three main coefficient words are
serialized into the immutable row-source lists, preserving the field width.
-/

namespace PCP.Lang.HadamardSeed

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList HadamardLabel

variable {t r a : ℕ}

def factorStep : Stmt 100 32 := .seq (.pop 25 64 65) (.push 23 64)

def factors : ℕ → Stmt 100 32
  | 0 => .skip
  | k + 1 => .seq factorStep (factors k)

theorem factors_run (fs cs : List ℕ) (st : State 100 32)
    (hc : st.lists 25 = fs ++ cs) :
    ((factors fs.length).run st).1.lists 25 = cs ∧
      ((factors fs.length).run st).1.lists 23 = fs.reverse ++ st.lists 23 := by
  induction fs generalizing st with
  | nil => simpa [factors, Stmt.run] using hc
  | cons f fs ih =>
      have hf : (factorStep.run st).1.lists 25 = fs ++ cs ∧
          (factorStep.run st).1.lists 23 = f :: st.lists 23 := by
        simp [factorStep, Stmt.run, Function.update, hc]
      have h := ih (factorStep.run st).1 hf.1
      simp only [List.length_cons, factors, run_seq_fst]
      exact ⟨h.1, by simpa [hf.2, List.reverse_cons, List.append_assoc] using h.2⟩

theorem factors_frame (k : ℕ) (st : State 100 32) :
    ((factors k).run st).1.regs 20 = st.regs 20 ∧
      ((factors k).run st).1.lists 7 = st.lists 7 := by
  induction k generalizing st with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      have h := ih (factorStep.run st).1
      simpa only [factors, run_seq_fst,
        run_regs_frame factorStep 20 (by decide) st,
        run_lists_frame factorStep 7 (by decide) st] using h

def splitFactors (r : ℕ) : Stmt 100 32 :=
  .seq (.copy 7 23) (.seq (factors (r - 1)) (.rev 23))

theorem splitFactors_run (s : Hadamard.TestRandomness t r) (cs : List ℕ)
    (st : State 100 32) (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hc : st.lists 25 = HadamardRow.factorCodes s ++ cs) :
    ((splitFactors r).run st).1.lists 23 = HadamardRow.factorCodes s ∧
      ((splitFactors r).run st).1.lists 25 = cs ∧
      ((splitFactors r).run st).1.regs 20 = t ∧
      ((splitFactors r).run st).1.lists 7 = [] := by
  let u := setList st 23 []
  have h := factors_run (HadamardRow.factorCodes s) cs u
    (by simpa [u, Function.update] using hc)
  have hf := factors_frame (r - 1) u
  have hn : (HadamardRow.factorCodes s).length = r - 1 := by
    simp [HadamardRow.factorCodes]
  rw [hn] at h
  simp only [u, setList_lists, Function.update_self, List.append_nil] at h
  have hfe : u.lists 7 = [] := by simpa [u, Function.update] using he
  have hft : u.regs 20 = t := ht
  simp only [splitFactors, run_seq_fst, run_copy_fst, he]
  generalize hv : ((factors (r - 1)).run u).1 = v at *
  simp only [run_rev_fst]
  change (setList v 23 (v.lists 23).reverse).lists 23 = _ ∧ _
  exact ⟨by simp [h.2], by simpa [Function.update] using h.1,
    hf.1.trans hft, by simpa [Function.update] using hf.2.trans hfe⟩

def load : Stmt 100 32 := HadamardFactorLoad.load.rename subRegs id

def loadTo (a : ℕ) (dst : Fin 32) : Stmt 100 32 :=
  .seq (.assign 60 (.const a)) (.seq load (.copy 18 dst))

theorem load_run (p : Coefficients t a) (cs : List ℕ) (st : State 100 32)
    (ht : st.regs 20 = t) (ha : st.regs 60 = a) (he : st.lists 7 = [])
    (hp : st.lists 25 = code p :: cs) :
    (load.run st).1.lists 18 = encode p ∧
      (load.run st).1.regs 20 = t ∧ (load.run st).1.lists 25 = cs := by
  have h := HadamardFactorLoad.load_run p cs (st.restrict subRegs id) ht ha he hp
  have hr := HadamardFactorLoad.load.run_rename subRegs id
    (Fin.castLE_injective _) Function.injective_id st
  rw [← hr] at h
  exact h

theorem loadTo_run (p : Coefficients t a) (cs : List ℕ) (dst : Fin 32)
    (hd7 : dst ≠ 7) (hd25 : dst ≠ 25) (st : State 100 32)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hp : st.lists 25 = code p :: cs) :
    ((loadTo a dst).run st).1.lists dst = encode p ∧
      ((loadTo a dst).run st).1.regs 20 = t ∧
      ((loadTo a dst).run st).1.lists 25 = cs ∧
      ((loadTo a dst).run st).1.lists 7 = [] := by
  have h := load_run p cs (setReg st 60 a) (by simpa [Function.update] using ht)
    (by simp) he hp
  have hf := run_lists_frame load 7 (by decide) (setReg st 60 a)
  simp only [loadTo, run_seq_fst, run_assign_fst, Expr.eval]
  generalize hu : (load.run (setReg st 60 a)).1 = u at *
  simp only [run_copy_fst]
  exact ⟨by simpa using h.1, h.2.1,
    by simpa [Function.update, hd25.symm] using h.2.2,
    by simpa [Function.update, hd7.symm] using hf.trans he⟩

theorem loadTo_list (a : ℕ) (dst L : Fin 32) (hL : 20 ≤ L.val) (h25 : L ≠ 25)
    (hd : L ≠ dst) (st : State 100 32) :
    ((loadTo a dst).run st).1.lists L = st.lists L := by
  have hw : ∀ L : Fin 32, 20 ≤ L.val → L ≠ 25 → L ∉ load.listWrites := by decide
  have h := run_lists_frame load L (hw L hL h25) (setReg st 60 a)
  simp only [loadTo, run_seq_fst, run_assign_fst, Expr.eval, run_copy_fst,
    setList_lists, Function.update_of_ne hd]
  exact h

def words (r : ℕ) : Stmt 100 32 :=
  .seq (loadTo 1 22) (.seq (loadTo r 21) (.seq (loadTo r 20) (.assign 56 (.const r))))

theorem words_run (s : Hadamard.TestRandomness t r) (st : State 100 32)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hf : st.lists 23 = HadamardRow.factorCodes s)
    (hc : st.lists 25 = [code s.linear, code s.auxiliary, code s.base]) :
    HadamardRow.Context s (((words r).run st).1.restrict subRegs id) := by
  have h1 := loadTo_run s.linear _ 22 (by decide) (by decide) st ht he hc
  have f1 := loadTo_list 1 22 23 (by decide) (by decide) (by decide) st
  simp only [words, run_seq_fst]
  generalize hu : ((loadTo 1 22).run st).1 = u at *
  have h2 := loadTo_run s.auxiliary _ 21 (by decide) (by decide) u h1.2.1 h1.2.2.2 h1.2.2.1
  have f2 := loadTo_list r 21 23 (by decide) (by decide) (by decide) u
  have f2' := loadTo_list r 21 22 (by decide) (by decide) (by decide) u
  generalize hv : ((loadTo r 21).run u).1 = v at *
  have h3 := loadTo_run s.base [] 20 (by decide) (by decide) v h2.2.1 h2.2.2.2 h2.2.2.1
  have f3 := loadTo_list r 20 23 (by decide) (by decide) (by decide) v
  have f3' := loadTo_list r 20 22 (by decide) (by decide) (by decide) v
  have f3'' := loadTo_list r 20 21 (by decide) (by decide) (by decide) v
  generalize hw : ((loadTo r 20).run v).1 = w at *
  change HadamardRow.Context s ((setReg w 56 r).restrict subRegs id)
  refine ⟨?_, ?_, h3.2.2.2, h3.1, f3''.trans h2.1,
    f3'.trans (f2'.trans h1.1), f3.trans (f2.trans (f1.trans hf))⟩
  · simpa [State.restrict, subRegs, Function.update] using h3.2.1
  · rfl

/-- The decoded factor codes followed by linear, auxiliary and base codes become row sources. -/
def materialize (r : ℕ) : Stmt 100 32 := .seq (splitFactors r) (words r)

theorem materialize_run (s : Hadamard.TestRandomness t r) (st : State 100 32)
    (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hc : st.lists 25 = HadamardRow.factorCodes s ++
      [code s.linear, code s.auxiliary, code s.base]) :
    HadamardRow.Context s (((materialize r).run st).1.restrict subRegs id) := by
  have h := splitFactors_run s _ st ht he hc
  rw [materialize, run_seq_fst]
  exact words_run s _ h.2.2.1 h.2.2.2 h.1 h.2.1

end PCP.Lang.HadamardSeed
