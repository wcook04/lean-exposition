import Mathlib.Analysis.InnerProductSpace.LaxMilgram

open scoped InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Restrict the domain to a closed subspace and orthogonally project the image onto it. -/
noncomputable def projectedHilbertOperator (H : Submodule ℝ E) (hH : IsClosed (H : Set E))
    (A : E →L[ℝ] E) : H →L[ℝ] H := by
  letI : CompleteSpace H := hH.completeSpace_coe
  exact H.orthogonalProjectionOnto.comp (A.comp H.subtypeL)

theorem inner_projectedHilbertOperator (H : Submodule ℝ E) (hH : IsClosed (H : Set E))
    (A : E →L[ℝ] E) (u w : H) :
    ⟪projectedHilbertOperator H hH A u, w⟫_ℝ = ⟪A (u : E), (w : E)⟫_ℝ := by
  let : CompleteSpace H := hH.completeSpace_coe
  exact H.inner_orthogonalProjectionOnto_eq_of_mem_right w (A (u : E))

private noncomputable def projectedHilbertBilin (H : Submodule ℝ E)
    (hH : IsClosed (H : Set E)) (A : E →L[ℝ] E) : H →L[ℝ] H →L[ℝ] ℝ :=
  (innerSL ℝ).comp (projectedHilbertOperator H hH A)

private theorem projectedHilbertBilin_coercive (H : Submodule ℝ E)
    (hH : IsClosed (H : Set E)) (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u : H, c * ‖u‖ ^ 2 ≤ ⟪A (u : E), (u : E)⟫_ℝ) :
    IsCoercive (projectedHilbertBilin H hH A) := by
  refine ⟨c, hc, fun u => ?_⟩
  change c * ‖u‖ * ‖u‖ ≤ ⟪projectedHilbertOperator H hH A u, u⟫_ℝ
  rw [inner_projectedHilbertOperator, mul_assoc, ← pow_two]
  exact hA u

/-- The compressed operator is a continuous linear equivalence by Lax–Milgram.
For the projected endpoint equation in Appendix A, the ambient operator is
`K - J ∘L Ω` and the ambient right-hand side is `-L`. -/
noncomputable def projectedHilbertEquiv (H : Submodule ℝ E) (hH : IsClosed (H : Set E))
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u : H, c * ‖u‖ ^ 2 ≤ ⟪A (u : E), (u : E)⟫_ℝ) : H ≃L[ℝ] H := by
  letI : CompleteSpace H := hH.completeSpace_coe
  exact (projectedHilbertBilin_coercive H hH A hc hA).continuousLinearEquivOfBilin

theorem projectedHilbertEquiv_apply (H : Submodule ℝ E) (hH : IsClosed (H : Set E))
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u : H, c * ‖u‖ ^ 2 ≤ ⟪A (u : E), (u : E)⟫_ℝ) (u : H) :
    projectedHilbertEquiv H hH A hc hA u = projectedHilbertOperator H hH A u := by
  let : CompleteSpace H := hH.completeSpace_coe
  exact ((projectedHilbertBilin_coercive H hH A hc hA).unique_continuousLinearEquivOfBilin
    (v := u) (f := projectedHilbertOperator H hH A u) (fun _ => rfl)).symm

/-- Solving the projected equation is equivalent to testing the ambient equation on the
subspace. -/
theorem projectedHilbertOperator_eq_projection_iff (H : Submodule ℝ E)
    (hH : IsClosed (H : Set E)) (A : E →L[ℝ] E) (u : H) (f : E) :
    letI : CompleteSpace H := hH.completeSpace_coe
    projectedHilbertOperator H hH A u = H.orthogonalProjectionOnto f ↔
      ∀ w : H, ⟪A (u : E), (w : E)⟫_ℝ = ⟪f, (w : E)⟫_ℝ := by
  let : CompleteSpace H := hH.completeSpace_coe
  simp only [← inner_projectedHilbertOperator H hH A u,
    ← H.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact ⟨fun h w => congrArg (fun x : H => ⟪x, w⟫_ℝ) h,
    fun h => ext_inner_right ℝ h⟩

/-- The abstract projected Hilbert solution exists uniquely and has norm at most
`‖f‖ / c`. Applying this result to Appendix A requires the closed solenoidal,
zero-time-mean subspace and coercivity of the concrete operator on it.
Spatial Hölder estimates are a separate step. -/
theorem exists_projectedHilbertSolution (H : Submodule ℝ E) (hH : IsClosed (H : Set E))
    (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u : H, c * ‖u‖ ^ 2 ≤ ⟪A (u : E), (u : E)⟫_ℝ) (f : E) :
    ∃ u : H, (∀ w : H, ⟪A (u : E), (w : E)⟫_ℝ = ⟪f, (w : E)⟫_ℝ) ∧
      ‖u‖ ≤ ‖f‖ / c ∧
      ∀ v : H, (∀ w : H, ⟪A (v : E), (w : E)⟫_ℝ = ⟪f, (w : E)⟫_ℝ) → v = u := by
  let : CompleteSpace H := hH.completeSpace_coe
  let e := projectedHilbertEquiv H hH A hc hA
  let u := e.symm (H.orthogonalProjectionOnto f)
  have hp : projectedHilbertOperator H hH A u = H.orthogonalProjectionOnto f := by
    rw [← projectedHilbertEquiv_apply H hH A hc hA]
    exact e.apply_symm_apply _
  have hu := (projectedHilbertOperator_eq_projection_iff H hH A u f).mp hp
  refine ⟨u, hu, ?_, fun v hv => ?_⟩
  · by_cases hzero : u = 0
    · rw [hzero, norm_zero]
      exact div_nonneg (norm_nonneg _) hc.le
    · have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hzero
      have hbound : c * ‖u‖ ^ 2 ≤ ‖f‖ * ‖u‖ := by
        calc
          c * ‖u‖ ^ 2 ≤ ⟪A (u : E), (u : E)⟫_ℝ := hA u
          _ = ⟪f, (u : E)⟫_ℝ := hu u
          _ ≤ ‖f‖ * ‖u‖ := real_inner_le_norm f (u : E)
      rw [pow_two, ← mul_assoc] at hbound
      exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using (le_of_mul_le_mul_right hbound hnorm))
  · apply e.injective
    change projectedHilbertEquiv H hH A hc hA v = projectedHilbertEquiv H hH A hc hA u
    rw [projectedHilbertEquiv_apply, projectedHilbertEquiv_apply, hp]
    exact (projectedHilbertOperator_eq_projection_iff H hH A v f).mpr hv

end TorusEuler
