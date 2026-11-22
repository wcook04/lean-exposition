import PCP.Complexity.GridFactorCost
import PCP.Complexity.GridTensorCost
import PCP.Complexity.GridTensorSemantics
import PCP.Algebraic.ThreeColorParameters

/-!
# Grid programs at the actual verifier parameters

These adapters identify the numeric field and alphabet codes used by the concrete
programs with the exact production field family, grid, and coordinate order.
-/

namespace PCP.Lang.ProductionGrid

open PCP.Algebraic BinaryFieldCode ThreeColorParameters

instance dimensionNeZero (a : ℕ) : NeZero (binaryDimension a) :=
  ⟨by rw [binaryDimension_eq]; omega⟩

/-- The program's word codec is the verifier's production coordinate codec. -/
theorem fieldEquiv_eq_fieldCode (a : ℕ) :
    fieldEquiv (binaryDimension a) = fieldCode a :=
  fieldEquiv_production (fieldIndex a)

/-- The actual grid is the initial code alphabet supplied to the loop. -/
theorem grid_eq_alphabet (a : ℕ) :
    grid a = FiniteAlphabetIndex.alphabet (fieldEquiv (binaryDimension a))
      (size_le_fieldCode a) := by
  rw [fieldEquiv_eq_fieldCode]
  rfl

/-- Concrete grid-factor computation agrees with the verifier's coordinate recovery map. -/
theorem factor_run (a : ℕ) (z : Field a) (st : State 39 12)
    (hz : st.regs 0 = (fieldCode a z).val) (ht : st.regs 23 = binaryDimension a)
    (hc : st.regs 31 = size a)
    (hm : st.lists 3 = BinaryField.encode (BinaryWordMaterialization.modulus (binaryDimension a)))
    (he : st.lists 7 = []) :
    (GridFactor.program.run st).1.regs 2 =
      (fieldCode a (∏ b ∈ grid a, (z - b))).val := by
  have hz' : st.regs 0 = (fieldEquiv (binaryDimension a) z).val := by
    rwa [fieldEquiv_eq_fieldCode]
  have hp := (GridFactor.program_run (t := binaryDimension a) z (size a)
    (size_le_fieldCode a) st hz' ht hc hm he).2.2.1
  rw [GridFactor.value_eq_alphabet (t := binaryDimension a) z (size a) (size_le_fieldCode a),
    ← grid_eq_alphabet, fieldEquiv_eq_fieldCode] at hp
  exact hp

/-- The stored-vector routine evaluates the production grid's full tensor basis. -/
theorem tensor_run (a d : ℕ) (v : Fin d → grid a) (x : Fin d → Field a)
    (st : State 50 16) (hc : GridTensor.Context (binaryDimension a) (size a) st)
    (hx : st.lists 12 = List.ofFn (fun i => (fieldCode a (x i)).val))
    (hv : st.lists 13 = List.ofFn (fun i => (gridCode a (v i)).val)) :
    (GridTensor.program.run st).1.regs 40 =
      (fieldCode a (FieldQueryArithmetic.gridBasis (grid a) v x)).val := by
  have hp := @GridTensor.program_run_gridBasis (binaryDimension a) (size a) d _
    (size_le_fieldCode a)
  rw [fieldEquiv_eq_fieldCode] at hp
  exact hp v x st hc hx hv

end PCP.Lang.ProductionGrid
