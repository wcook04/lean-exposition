/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryRootSearchCost

/-!
# Complete construction of the production roots from the field degree

The program selects and stores the modulus, searches the coordinate-ordered
field, and materializes the chosen root. No field data is supplied as input.
-/

namespace PCP.Lang.BinaryRootSearch

open PCP.Algebraic BinaryField BinaryFieldWordCode BinaryRootPredicate
open BinaryPolynomialSelector

def modulusLists (L : Fin 2) : Fin 11 := if L = 0 then 7 else 3

theorem modulusLists_injective : Function.Injective modulusLists := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [modulusLists]

def buildModulus : Stmt 36 11 := fieldModulus.rename id modulusLists

theorem buildModulus_run {t : ℕ} [NeZero t] (st : State 36 11)
    (h20 : st.regs 20 = t) (he : st.lists 7 = []) :
    (buildModulus.run st).1.lists 3 = encode (BinaryWordMaterialization.modulus t) := by
  have h := congrArg (fun z : State 36 2 × ℕ => z.1.lists 1)
    (fieldModulus.run_rename id modulusLists Function.injective_id modulusLists_injective st)
  exact h.trans (fieldModulus_run t _ h20 he)

theorem fieldModulus_cardinality (st : State 36 2) :
    (fieldModulus.run st).1.regs 28 = 2 ^ st.regs 20 := by
  simp only [fieldModulus, run_seq_fst, run_regs_frame materialize 28 (by decide),
    selectPolynomial, run_regs_frame selectMask 28 (by decide), cardinality_run]

theorem buildModulus_cardinality (st : State 36 11) :
    (buildModulus.run st).1.regs 28 = 2 ^ st.regs 20 := by
  have h := congrArg (fun z : State 36 2 × ℕ => z.1.regs 28)
    (fieldModulus.run_rename id modulusLists Function.injective_id modulusLists_injective st)
  exact h.trans (fieldModulus_cardinality _)

theorem buildModulus_cost (t : ℕ) (ht : 0 < t) (st : State 36 11)
    (h20 : st.regs 20 = t) (he : st.lists 7 = []) :
    (buildModulus.run st).2 ≤ 7000000 * (2 ^ t + 1) ^ 7 := by
  rw [buildModulus, Stmt.run_rename_cost fieldModulus id modulusLists
    Function.injective_id modulusLists_injective]
  exact fieldModulus_cost t ht _ h20 he

/-- Materialize the minimum found in register `35`, leaving it as a word in list `8`. -/
def storeRoot : Stmt 36 11 := .seq (.assign 33 (.var 35)) serialize

theorem storeRoot_run (st : State 36 11) (he : st.lists 7 = []) :
    (storeRoot.run st).1.lists 8 = digits (st.regs 20) (st.regs 35) := by
  simp only [storeRoot, run_seq_fst, run_assign_fst, Expr.eval]
  rw [serialize_run _ (by simpa using he)]
  simp [Function.update]

theorem storeRoot_cost (st : State 36 11) (he : st.lists 7 = []) :
    (storeRoot.run st).2 ≤ 200 * (st.regs 20 + Nat.size (st.regs 35) + 1) ^ 2 := by
  let s := setReg st 33 (st.regs 35)
  have hs := serialize_cost s (by simpa [s] using he)
  have hs20 : s.regs 20 = st.regs 20 := by simp [s, Function.update]
  have hs33 : s.regs 33 = st.regs 35 := by simp [s]
  rw [hs20, hs33] at hs
  simp only [storeRoot, run_seq_snd, run_assign_fst, Expr.eval]
  change (Expr.var 35).cost st.regs + (serialize.run s).2 + 1 ≤ _
  simp only [Expr.cost, Expr.readSize, Expr.eval]
  nlinarith [Nat.zero_le ((st.regs 20) ^ 2), Nat.zero_le ((Nat.size (st.regs 35)) ^ 2)]

/-- Select the modulus, find the root, and store its coefficients, from degree alone. -/
def constructRoot (full : Bool) : Stmt 36 11 :=
  .seq buildModulus (.seq (searchRoot full) storeRoot)

/-- The result matches the actual root field element used in the verifier. -/
theorem constructRoot_run (k : ℕ) (full : Bool) (st : State 36 11)
    (h20 : st.regs 20 = 4 * (k + 1)) (he : st.lists 7 = []) :
    ((constructRoot full).run st).1.lists 8 = encode
      (if full then (ThreeColorFields.generator k).coefficients
        else (ThreeColorFields.cubeRoot k).coefficients) := by
  have hs3 := buildModulus_run st h20 he
  have hs20 := run_regs_frame buildModulus 20 (by decide) st
  have hs28 := buildModulus_cardinality st
  have hs7 := run_lists_frame buildModulus 7 (by decide) st
  rw [h20] at hs28
  simp only [constructRoot, run_seq_fst]
  generalize hs : (buildModulus.run st).1 = s at *
  have hu35 := searchRoot_run k full s (hs20.trans h20) hs28 hs3 (hs7.trans he)
  have hu20 := run_regs_frame (searchRoot full) 20 (by cases full <;> decide) s
  have hu7 := run_lists_frame (searchRoot full) 7 (by cases full <;> decide) s
  generalize hu : ((searchRoot full).run s).1 = u at *
  rw [storeRoot_run u (hu7.trans (hs7.trans he)), hu20, hs20, h20, hu35, ← encode_word]
  congr 1
  have hh := fieldCode_symm k (ThreeColorFields.fieldCode k
    (if full then ThreeColorFields.generator k else ThreeColorFields.cubeRoot k))
  have hcoeff := congrArg BinaryMaterializedField.Element.coefficients hh
  simpa only [Equiv.symm_apply_apply, apply_ite] using hcoeff.symm

/-- Modulus construction dominates this explicit polynomial in field cardinality. -/
theorem constructRoot_cost (k : ℕ) (full : Bool) (st : State 36 11)
    (h20 : st.regs 20 = 4 * (k + 1)) (he : st.lists 7 = []) :
    ((constructRoot full).run st).2 ≤ 500000000 * (2 ^ (4 * (k + 1)) + 4) ^ 7 := by
  let t := 4 * (k + 1)
  let q := 2 ^ t
  have hbuild := buildModulus_cost t (ThreeColorFields.extensionDegree_pos k) st h20 he
  have hs3 := buildModulus_run st h20 he
  have hs20 := run_regs_frame buildModulus 20 (by decide) st
  have hs28 := buildModulus_cardinality st
  have hs7 := run_lists_frame buildModulus 7 (by decide) st
  rw [h20] at hs28
  simp only [constructRoot, run_seq_snd]
  generalize hs : (buildModulus.run st).1 = s at *
  have hsearch := searchRoot_cost full s (hs20.trans h20) hs28 hs3 (hs7.trans he)
  have hu35 := searchRoot_run k full s (hs20.trans h20) hs28 hs3 (hs7.trans he)
  have hu20 := run_regs_frame (searchRoot full) 20 (by cases full <;> decide) s
  have hu7 := run_lists_frame (searchRoot full) 7 (by cases full <;> decide) s
  generalize hu : ((searchRoot full).run s).1 = u at *
  have hstore := storeRoot_cost u (hu7.trans (hs7.trans he))
  have hsize : Nat.size (u.regs 35) ≤ t := by
    rw [hu35]
    exact Nat.size_le.mpr (Fin.isLt _)
  have hstore' : (storeRoot.run u).2 ≤ 200 * (2 * t + 1) ^ 2 := by
    rw [hu20, hs20, h20] at hstore
    exact hstore.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have htq : t ≤ q := (Nat.lt_two_pow_self (n := t)).le
  have hstore'' : (storeRoot.run u).2 ≤ 200 * (2 * q + 1) ^ 2 :=
    hstore'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  change _ ≤ 500000000 * (q + 4) ^ 7
  change (buildModulus.run st).2 ≤ 7000000 * (q + 1) ^ 7 at hbuild
  change ((searchRoot full).run s).2 ≤ 300000000 * (q + 4) ^ 6 at hsearch
  nlinarith [Nat.zero_le (q ^ 7), Nat.zero_le (q ^ 6), Nat.zero_le (q ^ 5),
    Nat.zero_le (q ^ 4), Nat.zero_le (q ^ 3), Nat.zero_le (q ^ 2)]

end PCP.Lang.BinaryRootSearch
