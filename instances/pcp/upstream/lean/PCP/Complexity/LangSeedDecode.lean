import PCP.Complexity.LangMixedRadixDecode
import PCP.Algebraic.ThreeColorSeedIndex

/-!
# Materialized decoding agrees with the actual verifier seed codec

The generic digit decoder reads exactly the mixed-radix coordinates used by
`finPiFinEquiv` and `ThreeColorSeedIndex.Codec.piFin`.
-/

namespace PCP.Lang.MixedRadixDecode

open scoped BigOperators

private theorem take_ofFn_eq {n : ℕ} (rs : Fin n → ℕ) (i : ℕ) (hi : i ≤ n) :
    (List.ofFn rs).take i = List.ofFn (fun j : Fin i => rs (Fin.castLE hi j)) := by
  apply List.ext_getElem
  · simp [hi]
  · intro j h1 h2
    simp

/-- The runtime prefix-product formula is the inverse of the production heterogeneous codec. -/
theorem split_finPi {n : ℕ} (rs : Fin n → ℕ) (code : Fin (∏ i, rs i)) :
    (split code.val (List.ofFn rs)).1 =
      List.ofFn (fun i => ((finPiFinEquiv.symm code) i).val) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    have hs := split_getD code.val (List.ofFn rs) i (by simpa using hi)
    rw [take_ofFn_eq rs i hi.le, List.prod_ofFn] at hs
    simp only [List.getElem_ofFn]
    change _ = (code.val / ∏ j : Fin i, rs (Fin.castLE hi.le j)) % rs ⟨i, hi⟩
    simpa [List.getD_eq_getElem?_getD, hi] using hs

/-- Uniform radices recover the actual finite-function coordinate order. -/
theorem split_finFunction (base n : ℕ) (code : Fin (base ^ n)) :
    (split code.val (List.replicate n base)).1 =
      List.ofFn (fun i : Fin n => ((finFunctionFinEquiv.symm code) i).val) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    have hs := split_getD code.val (List.replicate n base) i (by simpa using hi)
    simp only [List.getElem_ofFn]
    change _ = code.val / base ^ i % base
    simpa [List.getD_eq_getElem?_getD, hi, Nat.min_eq_left hi.le] using hs

/-- The actual decoding program computes every heterogeneous component code. -/
theorem program_finPi {n : ℕ} (rs : Fin n → ℕ) (code : Fin (∏ i, rs i))
    (st : State 5 2) (h0 : st.regs 0 = code.val)
    (hL : st.lists 0 = List.ofFn rs) (hA : st.lists 1 = []) :
    (program.run st).1.lists 1 =
      List.ofFn (fun i => ((finPiFinEquiv.symm code) i).val) ∧
    (program.run st).1.regs 0 = 0 ∧ (program.run st).1.lists 0 = [] := by
  obtain ⟨hq, hE, hD⟩ := program_run st
  refine ⟨?_, ?_, hE⟩
  · simpa [h0, hL, hA, split_finPi] using hD
  · rw [hq, h0, hL, split_quotient, List.prod_ofFn]
    exact Nat.div_eq_of_lt code.isLt

/-- Component codes computed by the actual verifier's generic heterogeneous codec. -/
theorem program_codecPi {n : ℕ} {A : Fin n → Type*}
    (cs : ∀ i, PCP.Algebraic.ThreeColorSeedIndex.Codec (A i))
    (code : Fin (∏ i, (cs i).size)) (st : State 5 2)
    (h0 : st.regs 0 = code.val) (hL : st.lists 0 = List.ofFn (fun i => (cs i).size))
    (hA : st.lists 1 = []) :
    (program.run st).1.lists 1 = List.ofFn (fun i => ((cs i).equiv
      (((PCP.Algebraic.ThreeColorSeedIndex.Codec.piFin cs).equiv.symm code) i)).val) := by
  have h := (program_finPi (fun i => (cs i).size) code st h0 hL hA).1
  rw [h]
  congr 1
  funext i
  change _ = ((cs i).equiv ((cs i).equiv.symm (finPiFinEquiv.symm code i))).val
  rw [Equiv.apply_symm_apply]

/-- Ordered-pair seeds use the right component as their least-significant radix. -/
theorem split_codecProd {A B : Type*}
    (a : PCP.Algebraic.ThreeColorSeedIndex.Codec A)
    (b : PCP.Algebraic.ThreeColorSeedIndex.Codec B) (code : Fin (a.size * b.size)) :
    (split code.val [b.size, a.size]).1 =
      [((b.equiv (((a.prod b).equiv.symm code).2))).val,
        ((a.equiv (((a.prod b).equiv.symm code).1))).val] := by
  change [code.val % b.size, (code.val / b.size) % a.size] =
    [(b.equiv (b.equiv.symm code.modNat)).val,
      (a.equiv (a.equiv.symm code.divNat)).val]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change [code.val % b.size, (code.val / b.size) % a.size] =
    [code.val % b.size, code.val / b.size]
  rw [Nat.mod_eq_of_lt (show code.val / b.size < a.size from code.divNat.isLt)]

end PCP.Lang.MixedRadixDecode
