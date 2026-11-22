/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanLabelConstructorsCost
import PCP.Complexity.BooleanCoefficientCode
import PCP.Algebraic.ComputableHadamardTest

/-!
# Stored label adapters for the Hadamard row verifier

These source-preserving helpers compute coefficient sums and append their exact
production numeric codes to a query accumulator. The large fixed state leaves
room for the row seed and the eventual answer-history scan.
-/

namespace PCP.Lang.HadamardLabel

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList

variable {t a b r : ℕ}

def code (p : Coefficients t r) : ℕ := (BooleanCoefficientIndex.coefficientEquiv t r p).val

theorem value_encode (p : Coefficients t r) : WordCodec.value (encode p) = code p := by
  rw [← digits_code]
  exact BinaryFieldWordCode.value_digits _ _
    (BooleanCoefficientIndex.coefficientEquiv t r p).isLt

theorem code_size (p : Coefficients t r) : Nat.size (code p) ≤ 2 ^ t := by
  have h : Nat.size (code p) ≤ BooleanCoefficientIndex.dimension t r :=
    Nat.size_le.mpr (BooleanCoefficientIndex.coefficientEquiv t r p).isLt
  have hd := BooleanCoefficientTransform.masks_length_le t r
  rw [BooleanMask.masks_length] at hd
  exact h.trans hd

def decodeRegs : Fin 5 → Fin 80 := Fin.castLE (by decide)
def decodeLists : Fin 1 → Fin 32 := fun _ => 0

def decode : Stmt 80 32 := WordCodec.decode.rename decodeRegs decodeLists

theorem decode_run (p : Coefficients t r) (st : State 80 32)
    (hp : st.lists 0 = encode p) : (decode.run st).1.regs 1 = code p := by
  have h := congrArg (fun z : State 5 1 × ℕ => z.1.regs 1)
    (WordCodec.decode.run_rename decodeRegs decodeLists (Fin.castLE_injective _)
      (by intro i j _; exact Subsingleton.elim i j) st)
  have hh := h.trans (WordCodec.decode_run (st.restrict decodeRegs decodeLists)).1
  rw [show (st.restrict decodeRegs decodeLists).lists 0 = st.lists 0 from rfl,
    hp, value_encode] at hh
  unfold decode
  simpa only [State.restrict_regs, show decodeRegs 1 = (1 : Fin 80) from rfl] using hh

/-- Copy a source word, consume its work copy, and prepend its numeric query code. -/
def emit (L : Fin 32) : Stmt 80 32 :=
  .seq (.copy L 0) (.seq decode (.push 24 1))

theorem emit_run (L : Fin 32) (p : Coefficients t r) (st : State 80 32)
    (hp : st.lists L = encode p) :
    ((emit L).run st).1.lists 24 = code p :: st.lists 24 := by
  let s := setList st 0 (st.lists L)
  have hc := decode_run p s (by simpa [s] using hp)
  have hs24 := run_lists_frame decode 24 (by decide) s
  dsimp only [s] at hc hs24
  simp only [emit, run_seq_fst, run_copy_fst]
  generalize hu : (decode.run (setList st 0 (st.lists L))).1 = u at *
  simp [run_push_fst, Function.update, hc, hs24]

def addRegs : Fin 8 → Fin 80 := Fin.castLE (by decide)
def addLists : Fin 8 → Fin 32 := ![0, 1, 2, 3, 28, 29, 6, 7]

theorem addLists_injective : Function.Injective addLists := by decide

def add : Stmt 80 32 := BooleanLabelAddition.add.rename addRegs addLists

theorem add_run (p q : Coefficients t r) (st : State 80 32)
    (hp : st.lists 28 = encode p) (hq : st.lists 29 = encode q) (he : st.lists 7 = []) :
    (add.run st).1.lists 1 = encode (p + q) := by
  have h := congrArg (fun z : State 8 8 × ℕ => z.1.lists 1)
    (BooleanLabelAddition.add.run_rename addRegs addLists
      (Fin.castLE_injective _) addLists_injective st)
  have hh := h.trans (BooleanLabelAddition.add_run p q (st.restrict addRegs addLists) hp hq he)
  unfold add
  simpa only [State.restrict_lists, show addLists 1 = (1 : Fin 32) from rfl] using hh

/-- The right source cannot be the work slot overwritten while copying the left source. -/
def sum (L K : Fin 32) : Stmt 80 32 := .seq (.copy L 28) (.seq (.copy K 29) add)

theorem sum_run (L K : Fin 32) (hK : K ≠ 28) (p q : Coefficients t r)
    (st : State 80 32) (hp : st.lists L = encode p) (hq : st.lists K = encode q)
    (he : st.lists 7 = []) :
    ((sum L K).run st).1.lists 1 = encode (p + q) := by
  simp only [sum, run_seq_fst, run_copy_fst]
  apply add_run
  · simp [Function.update, hp]
  · simp [Function.update, hK, hq]
  · simp [Function.update, he]

def emitSum (L K : Fin 32) : Stmt 80 32 := .seq (sum L K) (emit 1)

theorem emitSum_run (L K : Fin 32) (hK : K ≠ 28) (p q : Coefficients t r)
    (st : State 80 32) (hp : st.lists L = encode p) (hq : st.lists K = encode q)
    (he : st.lists 7 = []) :
    ((emitSum L K).run st).1.lists 24 = code (p + q) :: st.lists 24 := by
  have hh := sum_run L K hK p q st hp hq he
  have h24 := run_lists_frame (sum L K) 24
    (by simp only [sum, Stmt.listWrites]; decide) st
  simp only [emitSum, run_seq_fst]
  generalize hs : ((sum L K).run st).1 = s at *
  rw [emit_run 1 (p + q) s hh, h24]

def transformRegs : Fin 57 → Fin 80 := Fin.castLE (by decide)
def transformLists : Fin 20 → Fin 32 := Fin.castLE (by decide)

def embed : Stmt 80 32 := BooleanLabelTransform.embed.rename transformRegs transformLists

def product : Stmt 80 32 :=
  (BooleanLabelTransform.query true).rename transformRegs transformLists

def constant : Stmt 80 32 :=
  BooleanLabelConstructors.constant.rename transformRegs transformLists

theorem embed_run (h : a ≤ r) (p : Coefficients t a) (st : State 80 32)
    (ht : st.regs 20 = t) (ha : st.regs 54 = a) (hr : st.regs 56 = r)
    (he : st.lists 7 = []) (hp : st.lists 13 = encode p) :
    (embed.run st).1.lists 5 = encode (BooleanCoefficientArithmetic.embed h p) := by
  have hh := congrArg (fun z : State 57 20 × ℕ => z.1.lists 5)
    (BooleanLabelTransform.embed.run_rename transformRegs transformLists
      (Fin.castLE_injective _) (Fin.castLE_injective _) st)
  have hhh := hh.trans (BooleanLabelTransform.embed_run h p
    (st.restrict transformRegs transformLists) ht ha hr he hp)
  unfold embed
  simpa only [State.restrict_lists, show transformLists 5 = (5 : Fin 32) from rfl] using hhh

theorem product_run (h : a + b ≤ r) (p : Coefficients t a) (q : Coefficients t b)
    (st : State 80 32) (ht : st.regs 20 = t) (ha : st.regs 54 = a)
    (hb : st.regs 55 = b) (hr : st.regs 56 = r) (he : st.lists 7 = [])
    (hp : st.lists 13 = encode p) (hq : st.lists 18 = encode q) :
    (product.run st).1.lists 5 = encode (BooleanCoefficientArithmetic.mixedProduct h p q) := by
  have hh := congrArg (fun z : State 57 20 × ℕ => z.1.lists 5)
    ((BooleanLabelTransform.query true).run_rename transformRegs transformLists
      (Fin.castLE_injective _) (Fin.castLE_injective _) st)
  have hhh := hh.trans (BooleanLabelTransform.query_product h p q
    (st.restrict transformRegs transformLists) ht ha hb hr he hp hq)
  unfold product
  simpa only [State.restrict_lists, show transformLists 5 = (5 : Fin 32) from rfl] using hhh

theorem constant_run (z : ZMod 2) (st : State 80 32)
    (ht : st.regs 20 = t) (hr : st.regs 56 = r) (hz : st.regs 51 = z.val)
    (he : st.lists 7 = []) :
    (constant.run st).1.lists 5 =
      encode (BooleanCoefficientArithmetic.constant (t := t) (r := r) z) := by
  have hh := congrArg (fun z : State 57 20 × ℕ => z.1.lists 5)
    (BooleanLabelConstructors.constant.run_rename transformRegs transformLists
      (Fin.castLE_injective _) (Fin.castLE_injective _) st)
  have hhh := hh.trans (BooleanLabelConstructors.constant_run z
    (st.restrict transformRegs transformLists) ht hr hz he)
  unfold constant
  simpa only [State.restrict_lists, show transformLists 5 = (5 : Fin 32) from rfl] using hhh

end PCP.Lang.HadamardLabel
