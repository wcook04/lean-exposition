import PCP.Complexity.GridTensorLang

/-!
# Exact agreement of the stored-vector tensor program with grid interpolation
-/

namespace PCP.Lang.GridTensor

open PCP.Algebraic BinaryFieldCode

variable {t h d : ℕ} [NeZero t]

omit [NeZero t] in
/-- Recover an actual prefix-alphabet element from its numeric alphabet code. -/
theorem node_alphabetCode (hh : h ≤ 2 ^ t)
    (a : FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) :
    GridFactor.node t ((FiniteAlphabetIndex.code (fieldEquiv t) hh) a).val = a.val := by
  apply (fieldEquiv t).injective
  apply Fin.ext
  rw [GridFactor.code_node _ (lt_of_lt_of_le
    ((FiniteAlphabetIndex.code (fieldEquiv t) hh) a).isLt hh)]
  rfl

/-- The source lists encode point coordinates and the matching alphabet-node indices. -/
def coordinates (hh : h ≤ 2 ^ t)
    (a : Fin d → FiniteAlphabetIndex.alphabet (fieldEquiv t) hh)
    (x : Fin d → BinaryMaterializedField.Element t) :
    List (BinaryMaterializedField.Element t × Fin h) :=
  List.ofFn (fun i => (x i, (FiniteAlphabetIndex.code (fieldEquiv t) hh) (a i)))

/-- The list product is the exact tensor Lagrange basis in the semantic verifier. -/
theorem value_coordinates (hh : h ≤ 2 ^ t)
    (a : Fin d → FiniteAlphabetIndex.alphabet (fieldEquiv t) hh)
    (x : Fin d → BinaryMaterializedField.Element t) :
    value (coordinates hh a x) =
      FieldQueryArithmetic.gridBasis (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) a x := by
  simp only [value, coordinates, List.map_ofFn, Fin.prod_ofFn, FieldQueryArithmetic.gridBasis]
  apply Finset.prod_congr rfl
  intro i _
  dsimp only [Function.comp_apply]
  rw [GridBasisCoordinate.value_eq_alphabet _ h hh, node_alphabetCode hh (a i)]

theorem program_run_gridBasis (hh : h ≤ 2 ^ t)
    (a : Fin d → FiniteAlphabetIndex.alphabet (fieldEquiv t) hh)
    (x : Fin d → BinaryMaterializedField.Element t)
    (st : State 50 16) (hc : Context t h st)
    (hx : st.lists 12 = List.ofFn (fun i => (fieldEquiv t (x i)).val))
    (hk : st.lists 13 = List.ofFn
      (fun i => ((FiniteAlphabetIndex.code (fieldEquiv t) hh) (a i)).val)) :
    (program.run st).1.regs 40 = (fieldEquiv t
      (FieldQueryArithmetic.gridBasis
        (FiniteAlphabetIndex.alphabet (fieldEquiv t) hh) a x)).val := by
  have hp := (program_run (coordinates hh a x) hh st hc
    (by simpa [pointCodes, coordinates, Function.comp_def] using hx)
    (by simpa [nodeCodes, coordinates, Function.comp_def] using hk)).1
  rwa [value_coordinates] at hp

end PCP.Lang.GridTensor
