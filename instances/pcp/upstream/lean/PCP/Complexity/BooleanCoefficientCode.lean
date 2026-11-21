/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.BooleanCoefficientList
import PCP.Complexity.BinaryFieldCodeSemantics

/-!
# Numeric codecs for stored Boolean coefficient vectors

The fixed-width serializer directly materializes production coefficient indices.
The numeric point convention also matches the production materialized field's
binary coordinates.
-/

namespace PCP.Lang.BooleanCoefficientList

open PCP.Algebraic BinaryPolynomialSpace BooleanCoefficientIndex BinaryPolynomialSelector

/-- Fixed-width digits of the coefficient index are the actual stored coefficient word. -/
theorem digits_code {t r : ℕ} (p : Coefficients t r) :
    digits (dimension t r) (coefficientEquiv t r p).val = encode p := by
  rw [digits_ofFn, encode]
  apply congrArg List.ofFn
  funext i
  have h := congrFun ((@finFunctionFinEquiv 2 (dimension t r)).symm_apply_apply
    (fun j => (ZMod.finEquiv 2).symm (wordEquiv t r p j))) i
  exact congrArg Fin.val h

/-- The existing charged serializer realizes the coefficient codec without enumeration. -/
theorem materialize_coefficients {t r : ℕ} (p : Coefficients t r) (st : State 36 2)
    (hn : st.regs 20 = dimension t r) (hc : st.regs 33 = (coefficientEquiv t r p).val)
    (he : st.lists 0 = []) :
    (materialize.run st).1.lists 1 = encode p := by
  rw [materialize_run st he, hn, hc, digits_code]

/-- Point masks denote exactly the stored field coordinates. -/
theorem point_word (t : ℕ) (x : Fin (2 ^ t)) :
    point t x = BinaryWordMaterialization.toWord (BinaryFieldWordCode.word t x) := by
  funext i
  rw [BinaryFieldWordCode.word, BinaryWordMaterialization.toWord_ofWord]
  change (if i ∈ BooleanCoefficientIndex.unmask ((@finFunctionFinEquiv 2 t).symm x)
    then (1 : ZMod 2) else 0) = (ZMod.finEquiv 2) ((@finFunctionFinEquiv 2 t).symm x i)
  simp only [BooleanCoefficientIndex.unmask, Finset.mem_filter, Finset.mem_univ, true_and]
  generalize (@finFunctionFinEquiv 2 t).symm x i = bit
  fin_cases bit <;> rfl

theorem point_fieldEquiv {t : ℕ} [NeZero t] (a : BinaryMaterializedField.Element t) :
    point t (BinaryFieldCode.fieldEquiv t a) = BinaryMaterializedField.coordinates t a := by
  rw [point_word]
  change BinaryWordMaterialization.toWord
    (BinaryFieldWordCode.word t ⟨BinaryFieldCode.code a.coefficients,
      BinaryFieldCode.code_lt a.coefficients⟩) = BinaryWordMaterialization.toWord a.coefficients
  rw [BinaryFieldCode.word_code]

end PCP.Lang.BooleanCoefficientList
