import PCP.Complexity.LangQueryAddress

/-!
# Numeric concatenation of the verifier's disjoint coordinate blocks
-/

namespace PCP.Lang.QueryAddress

open PCP.Algebraic ThreeColorQueryIndex

/-- The finite-sum tuple order concatenates left coordinates before right coordinates. -/
theorem tupleIndex_sum {F : Type*} {q a b : ℕ} (eF : F ≃ Fin q)
    (u : Fin a → F) (v : Fin b → F) :
    (tupleIndex finSumFinEquiv eF (Sum.elim u v)).val =
      (vertexIndex eF a u).val + q ^ a * (vertexIndex eF b v).val := by
  rw [tupleIndex_value]
  have h : (fun i : Fin (a + b) => (eF (Sum.elim u v (finSumFinEquiv.symm i))).val) =
      Fin.append (fun i => (eF (u i)).val) (fun i => (eF (v i)).val) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp
    · intro j
      simp
  rw [h, List.ofFn_fin_append, RadixCodec.value_append, List.length_ofFn]
  rw [vertexIndex, tupleIndex_value, vertexIndex, tupleIndex_value]
  rfl

/-- The difference branch's paired point is packed from its two sampled point codes. -/
theorem pairIndex_sum {F : Type*} {q n : ℕ} (eF : F ≃ Fin q)
    (u v : Fin n → F) :
    (pairIndex eF n (Sum.elim u v)).val =
      (vertexIndex eF n u).val + q ^ n * (vertexIndex eF n v).val :=
  tupleIndex_sum eF u v

end PCP.Lang.QueryAddress
