/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BinaryFieldWordCode

/-!
# Stored prime-order root tests

A candidate code is serialized, raised to the fixed third power with
stored field arithmetic, and decoded. The Boolean result is exactly the
production root predicate. The modulus is supplied once as a stored list.
-/

namespace PCP.Lang.BinaryRootPredicate

open PCP.Algebraic BinaryField BinaryFieldWordCode BooleanLoops

def serialLists (L : Fin 2) : Fin 11 := if L = 0 then 7 else 8

theorem serialLists_injective : Function.Injective serialLists := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [serialLists]

def serialize : Stmt 36 11 := BinaryPolynomialSelector.materialize.rename id serialLists

def powerRegs : Fin 8 → Fin 36 := Fin.castLE (by decide)
def power36 : Stmt 36 11 := BinaryFieldPower.power.rename powerRegs id

def decodeRegs : Fin 5 → Fin 36 := Fin.castLE (by decide)
def decodeLists (_ : Fin 1) : Fin 11 := 1

def decode36 : Stmt 36 11 := WordCodec.decode.rename decodeRegs decodeLists

theorem serialize_run (st : State 36 11) (he : st.lists 7 = []) :
    (serialize.run st).1.lists 8 =
      BinaryPolynomialSelector.digits (st.regs 20) (st.regs 33) := by
  have h := congrArg (fun z : State 36 2 × ℕ => z.1.lists 1)
    (BinaryPolynomialSelector.materialize.run_rename id serialLists
      Function.injective_id serialLists_injective st)
  exact h.trans (BinaryPolynomialSelector.materialize_run _ he)

theorem power36_run {t : ℕ} [NeZero t] (st : State 36 11)
    (w : BinaryWordMaterialization.Word t) (p : ℕ)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t))
    (hw : st.lists 8 = encode w) (hp : st.lists 9 = p.bits.map Bool.toNat)
    (he : st.lists 7 = []) :
    (power36.run st).1.lists 1 = encode (BinaryWordMaterialization.fieldPower w p) := by
  have h := congrArg (fun z : State 8 11 × ℕ => z.1.lists 1)
    (BinaryFieldPower.power.run_rename powerRegs id (Fin.castLE_injective _)
      Function.injective_id st)
  exact h.trans (BinaryFieldPower.power_run_encode _ _ _ w p
    (BinaryWordMaterialization.toWord_ofWord _) hm hw hp he)

theorem decode36_run (st : State 36 11) :
    (decode36.run st).1.regs 1 = WordCodec.value (st.lists 1) := by
  have h := congrArg (fun z : State 5 1 × ℕ => z.1.regs 1)
    (WordCodec.decode.run_rename decodeRegs decodeLists (Fin.castLE_injective _)
      (Function.injective_of_subsingleton _) st)
  exact h.trans (WordCodec.decode_run _).1

/-- Store the binary exponent three as part of the fixed program. -/
def exponent : Stmt 36 11 :=
  .seq (.copy 7 9) (.seq (.assign 6 (.const 1)) (.seq (.push 9 6) (.push 9 6)))

theorem exponent_run (st : State 36 11) (he : st.lists 7 = []) :
    (exponent.run st).1.lists 9 = (3 : ℕ).bits.map Bool.toNat := by
  simp [exponent, Stmt.run, Expr.eval, Function.update, he,
    show (3 : ℕ).bits.map Bool.toNat = [1, 1] by decide]

/-- Serialize and power a field address while preserving the address itself. -/
def rootPower : Stmt 36 11 := .seq serialize (.seq (exponent) power36)

theorem rootPower_run {t : ℕ} [NeZero t] (st : State 36 11)
    (i : Fin (2 ^ t)) (h20 : st.regs 20 = t) (h33 : st.regs 33 = i.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((rootPower).run st).1.lists 1 =
      encode (BinaryWordMaterialization.fieldPower (word t i) (3)) := by
  have hs8 := serialize_run st he
  rw [h20, h33, ← encode_word] at hs8
  have hs3 := run_lists_frame serialize 3 (by decide) st
  have hs7 := run_lists_frame serialize 7 (by decide) st
  simp only [rootPower, run_seq_fst]
  generalize hs : (serialize.run st).1 = s at *
  have hu9 := exponent_run s (hs7.trans he)
  have hu3 := run_lists_frame (exponent) 3 (by decide) s
  have hu7 := run_lists_frame (exponent) 7 (by decide) s
  have hu8 := run_lists_frame (exponent) 8 (by decide) s
  generalize hu : ((exponent).run s).1 = u at *
  exact power36_run u (word t i) (3) (hu3.trans (hs3.trans hm))
    (hu8.trans hs8) hu9 (hu7.trans (hs7.trans he))

def rootTail : Stmt 36 11 :=
  .seq (.assign 0 (.const 1)) (.seq (.assign 1 (.eq 1 0)) (.seq (.assign 2 (.eq 33 0))
    (.seq (.assign 2 (.sub 0 2)) (.assign 27 (.mul 1 2)))))

theorem rootTail_run (st : State 36 11) :
    (rootTail.run st).1.regs 27 = truth (st.regs 1 = 1 ∧ st.regs 33 ≠ 1) := by
  simp only [rootTail, run_seq_fst, run_assign_fst, Expr.eval,
    setReg_regs, Function.update, Fin.reduceEq, dite_true, dite_false, truth]
  split_ifs <;> simp_all

def testRoot : Stmt 36 11 :=
  .seq (rootPower) (.seq decode36 rootTail)

theorem testRoot_run {t : ℕ} [NeZero t] (st : State 36 11)
    (i : Fin (2 ^ t)) (h20 : st.regs 20 = t) (h33 : st.regs 33 = i.val)
    (hm : st.lists 3 = encode (BinaryWordMaterialization.modulus t)) (he : st.lists 7 = []) :
    ((testRoot).run st).1.regs 27 = truth
      (FiniteRootSearch.Candidate (3)
        (⟨word t i⟩ : BinaryMaterializedField.Element t)) := by
  have hs1 := rootPower_run st i h20 h33 hm he
  have hs33 := run_regs_frame (rootPower) 33 (by decide) st
  simp only [testRoot, run_seq_fst]
  generalize hs : ((rootPower).run st).1 = s at *
  have hu1 := decode36_run s
  rw [hs1] at hu1
  have hu33 := run_regs_frame decode36 33 (by decide) s
  rw [hs33, h33] at hu33
  rw [rootTail_run, hu1, hu33]
  congr 1
  simp only [FiniteRootSearch.Candidate, value_power_eq_one_iff, ne_eq,
    element_word_eq_one_iff (Nat.pos_of_ne_zero (NeZero.ne t))]

end PCP.Lang.BinaryRootPredicate
