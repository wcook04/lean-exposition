/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientList
import PCP.Complexity.BinaryFieldLang

/-!
# Addition of stored coefficient labels

The same stored binary-word adder works for every degree bound. Source labels
are retained in lists `4` and `5`; an empty list `7` initializes output list `1`.
-/

namespace PCP.Lang.BooleanLabelAddition

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientList
open BooleanCoefficientIndex (dimension)

variable {t r : ℕ}

@[simp] theorem encode_add (p q : Coefficients t r) :
    encode (p + q) = BinaryField.addWords (encode p) (encode q) := by
  apply List.ext_getElem
  · simp [BinaryField.addWords]
  · intro i hi hi'
    simp [encode, BinaryField.addWords, ZMod.val_add]

/-- Source-preserving addition of dense binary coefficient words. -/
def add : Stmt 8 8 :=
  .seq (.copy 4 0) (.seq (.copy 5 2) (.seq (.copy 7 1) BinaryField.add))

theorem add_run (p q : Coefficients t r) (st : State 8 8)
    (hp : st.lists 4 = encode p) (hq : st.lists 5 = encode q) (he : st.lists 7 = []) :
    (add.run st).1.lists 1 = encode (p + q) := by
  simp only [add, run_seq_fst, run_copy_fst]
  rw [encode_add]
  apply BinaryField.add_run
  · simp [hp, Function.update]
  · simp [hq, Function.update]
  · simp [he, Function.update]
  · simp

theorem add_source (st : State 8 8) :
    (add.run st).1.lists 4 = st.lists 4 ∧
    (add.run st).1.lists 5 = st.lists 5 ∧
    (add.run st).1.lists 7 = st.lists 7 := by
  exact ⟨run_lists_frame add 4 (by decide) st,
    run_lists_frame add 5 (by decide) st, run_lists_frame add 7 (by decide) st⟩

/-- The charged cost is quadratic in the actual coefficient-word length. -/
theorem add_cost (p q : Coefficients t r) (st : State 8 8)
    (hp : st.lists 4 = encode p) (hq : st.lists 5 = encode q) (he : st.lists 7 = []) :
    (add.run st).2 ≤ 60 * (dimension t r + 1) ^ 2 := by
  let s := setList (setList (setList st 0 (st.lists 4)) 2 (st.lists 5)) 1 []
  have hc := BinaryField.add_cost s (encode p) (encode q)
    (by simp [s, hp, Function.update]) (by simp [s, hq, Function.update])
    (by simp [s]) (by simp) (encode_bits p) (encode_bits q)
  have hps := BinaryField.listSize_bits (encode_bits p)
  have hqs := BinaryField.listSize_bits (encode_bits q)
  simp only [encode_length] at hc hps hqs
  simp only [add, run_seq_snd, run_copy_fst, run_copy_snd, setList_lists,
    Function.update, Fin.reduceEq, dite_false, he]
  change (listSize (st.lists 4) + 1) + ((listSize (st.lists 5) + 1) +
    ((listSize ([] : List ℕ) + 1) + (BinaryField.add.run s).2 + 1) + 1) + 1 ≤ _
  rw [hp, hq]
  simp only [show listSize ([] : List ℕ) = 0 from rfl]
  nlinarith

end PCP.Lang.BooleanLabelAddition
