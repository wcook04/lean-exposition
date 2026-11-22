/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryRootPredicateCost
import PCP.Algebraic.FiniteRootSearchOrder
import PCP.Algebraic.FiniteGeneratorSearchOrder
import PCP.Complexity.BinaryGeneratorPredicateCost

/-!
# Bounded search for the production cube root and multiplicative generator

A natural counter visits each field code. A stored minimum records the first
successful code, using the concrete stored-power test at every iteration.
-/

namespace PCP.Lang.BinaryRootSearch

open PCP.Algebraic BinaryField BinaryFieldWordCode BinaryRootPredicate
open BinaryPolynomialSelector BooleanLoops

def RootCandidate (t : ℕ) [NeZero t] (full : Bool)
    (z : BinaryMaterializedField.Element t) : Prop :=
  if full then FiniteGeneratorSearch.Candidate (2^t-1) z else FiniteRootSearch.Candidate 3 z

instance (t : ℕ) [NeZero t] (full : Bool) (z : BinaryMaterializedField.Element t) :
    Decidable (RootCandidate t full z) := by unfold RootCandidate; infer_instance

/-- The numeric predicate is false outside the fixed-width field code domain. -/
def CodeCandidate (t : ℕ) [NeZero t] (full : Bool) (n : ℕ) : Prop :=
  if hn : n < 2 ^ t then
    RootCandidate t full (⟨word t ⟨n, hn⟩⟩ : BinaryMaterializedField.Element t)
  else False

instance (t : ℕ) [NeZero t] (full : Bool) (n : ℕ) : Decidable (CodeCandidate t full n) := by
  unfold CodeCandidate
  infer_instance

theorem codeCandidate_iff {t : ℕ} [NeZero t] (full : Bool) (i : Fin (2 ^ t)) :
    CodeCandidate t full i.val ↔
      RootCandidate t full
        (⟨word t i⟩ : BinaryMaterializedField.Element t) := by
  simp only [CodeCandidate, i.isLt, dite_eq_left]

/-- Reuse the checked minimum-update code, reserving `33` for the tested field address. -/
def tailRegs (r : Fin 36) : Fin 36 :=
  if r = 33 then 35 else if r = 35 then 31 else if r = 31 then 33 else r

theorem tailRegs_injective : Function.Injective tailRegs := by decide

def tailLists : Fin 2 → Fin 11 := Fin.castLE (by decide)
def rootSearchTail : Stmt 36 11 := candidateTail.rename tailRegs tailLists

theorem rootSearchTail_step (st : State 36 11) (h31 : st.regs 31 = 1)
    (P : Prop) [Decidable P] (h27 : st.regs 27 = truth P) :
    (rootSearchTail.run st).1.regs 35 =
      (if P then min (st.regs 35) (st.regs 32) else st.regs 35) ∧
    (rootSearchTail.run st).1.regs 32 = st.regs 32 + 1 := by
  have h := candidateTail.run_rename tailRegs tailLists tailRegs_injective
    (Fin.castLE_injective _) st
  have h35 := congrArg (fun z : State 36 2 × ℕ => z.1.regs 33) h
  have h32 := congrArg (fun z : State 36 2 × ℕ => z.1.regs 32) h
  have hs := candidateTail_step (st.restrict tailRegs tailLists) h31 P h27
  exact ⟨h35.trans hs.1, h32.trans hs.2⟩

def checkRoot (full : Bool) : Stmt 36 11 :=
  if full then BinaryGeneratorPredicate.program else testRoot

theorem checkRoot_run {t : ℕ} [NeZero t] (full : Bool) (st : State 36 11)
    (i : Fin (2^t)) (h20 : st.regs 20 = t) (h33 : st.regs 33 = i.val)
    (h28 : st.regs 28 = 2^t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((checkRoot full).run st).1.regs 27 = truth
      (RootCandidate t full (⟨word t i⟩ : BinaryMaterializedField.Element t)) := by
  cases full
  · exact testRoot_run st i h20 h33 hm he
  · exact BinaryGeneratorPredicate.program_run ⟨word t i⟩ st h20
      (by simpa [BinaryFieldCode.fieldEquiv, BinaryFieldCode.code_word] using h33) h28 hm he

def checkAddress (full : Bool) : Stmt 36 11 :=
  .seq (.assign 33 (.var 32)) (checkRoot full)
def searchBody (full : Bool) : Stmt 36 11 := .seq (checkAddress full) rootSearchTail

theorem checkAddress_run {t : ℕ} [NeZero t] (full : Bool) (st : State 36 11)
    (h20 : st.regs 20 = t) (h28 : st.regs 28 = 2 ^ t) (hi : st.regs 32 < 2 ^ t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((checkAddress full).run st).1.regs 27 = truth (CodeCandidate t full (st.regs 32)) := by
  simp only [checkAddress, run_seq_fst, run_assign_fst, Expr.eval]
  rw [checkRoot_run full _ ⟨st.regs 32, hi⟩
    (by simpa [Function.update] using h20) (by simp)
    (by simpa [Function.update] using h28) (by simpa using hm) (by simpa using he)]
  congr 1
  exact propext (codeCandidate_iff full ⟨_, hi⟩).symm

def RootContext (t : ℕ) [NeZero t] (st : State 36 11) : Prop :=
  st.regs 20 = t ∧ st.regs 28 = 2 ^ t ∧ st.regs 31 = 1 ∧
    st.lists 3 = encode (BinaryWordMaterialization.modulus t) ∧ st.lists 7 = []

theorem searchBody_step {t : ℕ} [NeZero t] (full : Bool) (st : State 36 11)
    (hc : RootContext t st) (hi : st.regs 32 < 2 ^ t) :
    ((searchBody full).run st).1.regs 35 =
      (if CodeCandidate t full (st.regs 32) then min (st.regs 35) (st.regs 32)
        else st.regs 35) ∧
    ((searchBody full).run st).1.regs 32 = st.regs 32 + 1 := by
  have hs27 := checkAddress_run full st hc.1 hc.2.1 hi hc.2.2.2.1 hc.2.2.2.2
  have hs31 := run_regs_frame (checkAddress full) 31 (by cases full <;> decide) st
  have hs32 := run_regs_frame (checkAddress full) 32 (by cases full <;> decide) st
  have hs35 := run_regs_frame (checkAddress full) 35 (by cases full <;> decide) st
  simp only [searchBody, run_seq_fst]
  generalize hs : ((checkAddress full).run st).1 = s at *
  have h := rootSearchTail_step s (hs31.trans hc.2.2.1) _ hs27
  simpa only [hs32, hs35] using h

theorem searchBody_frame (full : Bool) (st : State 36 11) (r : Fin 36)
    (hr : r ∈ ([20, 28, 31] : List (Fin 36))) :
    ((searchBody full).run st).1.regs r = st.regs r := by
  apply run_regs_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> cases full <;> decide

theorem searchBody_context {t : ℕ} [NeZero t] (full : Bool) (st : State 36 11)
    (hc : RootContext t st) : RootContext t ((searchBody full).run st).1 := by
  unfold RootContext at hc ⊢
  rw [searchBody_frame full st 20 (by decide), searchBody_frame full st 28 (by decide),
    searchBody_frame full st 31 (by decide),
    run_lists_frame (searchBody full) 3 (by cases full <;> decide) st,
    run_lists_frame (searchBody full) 7 (by cases full <;> decide) st]
  exact hc

theorem searchBody_inv {t : ℕ} [NeZero t] (full : Bool) (n : ℕ) (st : State 36 11)
    (hn : n < 2 ^ t) (hc : RootContext t st) (hi : st.regs 32 = n)
    (hm : LeastInv (CodeCandidate t full) (2 ^ t) n (st.regs 35)) :
    RootContext t ((searchBody full).run st).1 ∧
      ((searchBody full).run st).1.regs 32 = n + 1 ∧
      LeastInv (CodeCandidate t full) (2 ^ t) (n + 1) (((searchBody full).run st).1.regs 35) := by
  have hs := searchBody_step full st hc (hi ▸ hn)
  refine ⟨searchBody_context full st hc, hs.2.trans (by rw [hi]), ?_⟩
  rw [hs.1, hi]
  exact leastInv_step _ _ n _ hn hm

/-- Input field size `28`, degree `20`, stored modulus `3`, empty list `7`.
The resulting minimum code occupies register `35`. -/
def searchRoot (full : Bool) : Stmt 36 11 :=
  .seq (.assign 32 (.const 0)) (.seq (.assign 35 (.var 28))
    (.seq (.assign 31 (.const 1)) (.loop 28 (searchBody full))))

theorem searchRoot_invariant {t : ℕ} [NeZero t] (full : Bool) (st : State 36 11)
    (h20 : st.regs 20 = t) (h28 : st.regs 28 = 2 ^ t)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    LeastInv (CodeCandidate t full) (2 ^ t) (2 ^ t) (((searchRoot full).run st).1.regs 35) := by
  let q := 2 ^ t
  let s := setReg (setReg (setReg st 32 0) 35 q) 31 1
  have h := iterate_inv (searchBody full).run (Nat.size q + 1) q
    (fun n u => RootContext t u ∧ u.regs 32 = n ∧
      LeastInv (CodeCandidate t full) q n (u.regs 35))
    (fun n u hn hu => searchBody_inv full n u hn hu.1 hu.2.1 hu.2.2) s
    (by simp [s, RootContext, Function.update, h20, h28, q, hm, he, leastInv_zero])
  simp only [searchRoot, run_seq_fst, run_assign_fst, Expr.eval, run_loop_fst,
    setReg_regs, Function.update, Fin.reduceEq, dite_false, h28]
  exact h.2.2

/-- Numeric order uniquely identifies the same root chosen by the production search. -/
theorem searchRoot_run (k : ℕ) (full : Bool) (st : State 36 11)
    (h20 : st.regs 20 = 4 * (k + 1)) (h28 : st.regs 28 = 2 ^ (4 * (k + 1)))
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus (4 * (k + 1))))
    (he : st.lists 7 = []) :
    ((searchRoot full).run st).1.regs 35 =
      (ThreeColorFields.fieldCode k (if full then ThreeColorFields.generator k
        else ThreeColorFields.cubeRoot k)).val := by
  let t := 4 * (k + 1)
  let e := ThreeColorFields.fieldCode k
  let z := if full then ThreeColorFields.generator k else ThreeColorFields.cubeRoot k
  have hp : RootCandidate t full z := by
    cases full
    · exact (FiniteRootSearch.candidate_iff_primitive (by decide) _).mpr
        (ThreeColorFields.cubeRoot_spec k)
    · have hpos : 0 < 2^t-1 := by
        have htwo : 2 ≤ 2^t := (by norm_num : 2 ≤ 2^1).trans
          (Nat.pow_le_pow_right (by decide) (by dsimp [t]; omega))
        omega
      apply (FiniteGeneratorSearch.candidate_iff_primitive hpos _).mpr
      simpa [z, t, ThreeColorFields.FieldFamily, BinaryMaterializedField.card_element] using
        ThreeColorFields.generator_spec k
  have hz : CodeCandidate t full (e z).val := by
    rw [codeCandidate_iff, ← fieldCode_symm]
    simpa [e] using hp
  have h := searchRoot_invariant full st h20 h28 hm he
  have hle := h.2.2 (e z).val (e z).isLt hz
  have hlt : ((searchRoot full).run st).1.regs 35 < 2 ^ t := lt_of_le_of_lt hle (e z).isLt
  let i : Fin (2 ^ t) := ⟨_, hlt⟩
  have hi : RootCandidate t full (e.symm i) := by
    rw [fieldCode_symm]
    exact (codeCandidate_iff full i).mp (h.2.1 hlt)
  have hge : (e z).val ≤ i.val := by
    let : DecidableEq (ThreeColorFields.FieldFamily k) := e.decidableEq
    cases full
    · have hminimal := FiniteRootSearch.root_le e 3 (e.symm i) hi
      simpa [z, e, ThreeColorFields.cubeRoot] using hminimal
    · have hminimal := FiniteGeneratorSearch.root_le e (2^t-1) (e.symm i) hi
      simpa [z, e, t, ThreeColorFields.generator, ThreeColorFields.FieldFamily,
        BinaryMaterializedField.card_element] using hminimal
  exact Nat.le_antisymm hle hge

end PCP.Lang.BinaryRootSearch
