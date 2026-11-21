import Mathlib

namespace Breakdown

open Module End

theorem isUnit_one_add_of_isCompactOperator_of_injective {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (K : F →L[ℝ] F) (hK : IsCompactOperator K)
    (hinj : Function.Injective ((1 : F →L[ℝ] F) + K)) :
    IsUnit ((1 : F →L[ℝ] F) + K) := by
  have hneg : IsCompactOperator (-K) := hK.neg
  rcases hneg.hasEigenvalue_or_mem_resolventSet (μ := (1 : ℝ)) one_ne_zero with h | h
  · exfalso
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    have h1 : -K x = x := by
      have := hx.apply_eq_smul
      simpa using this
    have h1' : K x = -x := by rw [← neg_neg (K x), h1]
    have h2 : ((1 : F →L[ℝ] F) + K) x = ((1 : F →L[ℝ] F) + K) 0 := by
      simp [h1']
    exact hx.2 (hinj h2)
  · rw [spectrum.mem_resolventSet_iff] at h
    convert h using 1
    rw [Algebra.algebraMap_eq_smul_one, one_smul, sub_neg_eq_add]

theorem exists_equiv_of_injective_compact_perturbation {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L₀ : E ≃L[ℝ] F) (C : E →L[ℝ] F)
    (hC : IsCompactOperator (C.comp (L₀.symm : F →L[ℝ] E)))
    (hinj : Function.Injective ((L₀ : E →L[ℝ] F) + C)) :
    ∃ e : E ≃L[ℝ] F, ∀ x, e x = L₀ x + C x := by
  set K : F →L[ℝ] F := C.comp (L₀.symm : F →L[ℝ] E) with hKdef
  have hK : ∀ y, ((1 : F →L[ℝ] F) + K) y = ((L₀ : E →L[ℝ] F) + C) (L₀.symm y) := by
    intro y
    simp [K]
  have hinjK : Function.Injective ((1 : F →L[ℝ] F) + K) := by
    intro y₁ y₂ hy
    rw [hK, hK] at hy
    exact L₀.symm.injective (hinj hy)
  have hu := isUnit_one_add_of_isCompactOperator_of_injective K hC hinjK
  refine ⟨L₀.trans (ContinuousLinearEquiv.unitsEquiv ℝ F hu.unit), fun x => ?_⟩
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.unitsEquiv_apply, IsUnit.unit_spec,
    hK, ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem exists_equiv_of_injective_sum_compact_perturbation {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L₀ : E ≃L[ℝ] F) (A B : E →L[ℝ] F)
    (hA : IsCompactOperator (A.comp (L₀.symm : F →L[ℝ] E)))
    (hB : IsCompactOperator (B.comp (L₀.symm : F →L[ℝ] E)))
    (hinj : Function.Injective ((L₀ : E →L[ℝ] F) + (A + B))) :
    ∃ e : E ≃L[ℝ] F, ∀ x, e x = L₀ x + (A x + B x) := by
  have hC : IsCompactOperator ((A + B).comp (L₀.symm : F →L[ℝ] E)) := by
    rw [ContinuousLinearMap.add_comp]
    exact hA.add hB
  obtain ⟨e, he⟩ := exists_equiv_of_injective_compact_perturbation L₀ (A + B) hC hinj
  exact ⟨e, fun x => by simp [he]⟩

end Breakdown
