import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

open ContinuousLinearMap
open scoped InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The frozen mode operator acts by compression on the projected space and by the identity
on its orthogonal complement. -/
def frozenSymbol (r B : E →L[ℝ] E) : E →L[ℝ] E := r * B * r + (1 - r)

theorem frozenSymbol_apply (r B : E →L[ℝ] E) (v : E) :
    frozenSymbol r B v = r (B (r v)) + (v - r v) := rfl

theorem frozenSymbol_apply_of_fixed {r B : E →L[ℝ] E} {v : E} (hv : r v = v) :
    frozenSymbol r B v = r (B v) := by
  rw [frozenSymbol_apply, hv, sub_self, add_zero]

theorem frozenSymbol_apply_of_proj_eq_zero {r B : E →L[ℝ] E} {v : E} (hv : r v = 0) :
    frozenSymbol r B v = v := by
  simp [frozenSymbol_apply, hv]

private theorem projection_apply_fixed {r : E →L[ℝ] E}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection) (v : E) : r (r v) = r v :=
  DFunLike.congr_fun hr.isIdempotentElem v

private theorem inner_projection_complement {r : E →L[ℝ] E}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection) (v : E) :
    ⟪r v, v - r v⟫_ℝ = 0 := by
  rw [hr.isSymmetric.apply_clm v, map_sub, projection_apply_fixed hr, sub_self, inner_zero_right]

theorem frozenSymbol_commutes_projection {r B : E →L[ℝ] E}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection) : Commute (frozenSymbol r B) r := by
  ext v
  change frozenSymbol r B (r v) = r (frozenSymbol r B v)
  rw [frozenSymbol_apply_of_fixed (projection_apply_fixed hr v), frozenSymbol_apply,
    map_add, map_sub, projection_apply_fixed hr, projection_apply_fixed hr, sub_self, add_zero]

/-- The quadratic form splits over the projection and its orthogonal complement. -/
theorem inner_frozenSymbol_eq {r B : E →L[ℝ] E}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection) (v : E) :
    ⟪frozenSymbol r B v, v⟫_ℝ = ⟪B (r v), r v⟫_ℝ + ‖v - r v‖ ^ 2 := by
  have horth := inner_projection_complement hr v
  have hsum : r v + (v - r v) = v := add_sub_cancel _ _
  have hcompl : ⟪v - r v, v⟫_ℝ = ‖v - r v‖ ^ 2 := calc
    ⟪v - r v, v⟫_ℝ = ⟪v - r v, r v + (v - r v)⟫_ℝ :=
      congrArg (fun w : E => ⟪v - r v, w⟫_ℝ) hsum.symm
    _ = _ := by
      rw [inner_add_right, real_inner_comm (r v) (v - r v), horth, zero_add,
        real_inner_self_eq_norm_sq]
  rw [frozenSymbol_apply, inner_add_left, hr.isSymmetric.apply_clm (B (r v)), hcompl]

/-- Coercivity of `B` on the projected subspace suffices for the frozen mode bound on the full space. -/
theorem frozenSymbol_coercive {r B : E →L[ℝ] E} {μ : ℝ}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection)
    (hB : ∀ v, r v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) (v : E) :
    min 1 μ * ‖v‖ ^ 2 ≤ ⟪frozenSymbol r B v, v⟫_ℝ := by
  have hnorm : ‖r v‖ ^ 2 + ‖v - r v‖ ^ 2 = ‖v‖ ^ 2 := by
    simp only [pow_two]
    rw [← norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (r v) (v - r v)
      (inner_projection_complement hr v), add_sub_cancel]
  calc
    min 1 μ * ‖v‖ ^ 2 = min 1 μ * ‖r v‖ ^ 2 + min 1 μ * ‖v - r v‖ ^ 2 := by
      rw [← mul_add, hnorm]
    _ ≤ μ * ‖r v‖ ^ 2 + 1 * ‖v - r v‖ ^ 2 := add_le_add
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
    _ ≤ _ := by
      rw [inner_frozenSymbol_eq hr, one_mul]
      exact add_le_add (hB (r v) (projection_apply_fixed hr v)) le_rfl

theorem norm_frozenSymbol_lower_bound {r B : E →L[ℝ] E} {μ : ℝ}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection)
    (hB : ∀ v, r v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) (v : E) :
    min 1 μ * ‖v‖ ≤ ‖frozenSymbol r B v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp
  rw [mul_assoc, ← pow_two]
  exact (frozenSymbol_coercive hr hB v).trans (real_inner_le_norm _ _)

private theorem frozenSymbol_isCoercive {r B : E →L[ℝ] E} {μ : ℝ}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection) (hμ : 0 < μ)
    (hB : ∀ v, r v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) :
    IsCoercive ((innerSL ℝ).comp (frozenSymbol r B)) := by
  refine ⟨min 1 μ, lt_min zero_lt_one hμ, fun v => ?_⟩
  change min 1 μ * ‖v‖ * ‖v‖ ≤ ⟪frozenSymbol r B v, v⟫_ℝ
  rw [mul_assoc, ← pow_two]
  exact frozenSymbol_coercive hr hB v

/-- The variation of the frozen symbol with respect to the projection. -/
noncomputable def frozenSymbolDerivative (r B : E →L[ℝ] E) :
    (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  (mul ℝ (E →L[ℝ] E)).flip (B * r) + mul ℝ (E →L[ℝ] E) (r * B) -
    ContinuousLinearMap.id ℝ (E →L[ℝ] E)

theorem frozenSymbolDerivative_apply (r B H : E →L[ℝ] E) :
    frozenSymbolDerivative r B H = H * (B * r) + (r * B) * H - H := rfl

theorem hasFDerivAt_frozenSymbol (r B : E →L[ℝ] E) :
    HasFDerivAt (fun s => frozenSymbol s B) (frozenSymbolDerivative r B) r := by
  have hid := hasFDerivAt_id (𝕜 := ℝ) r
  have hprod := (hid.mul_const' B).mul' hid
  have hsub := (hasFDerivAt_const (𝕜 := ℝ) (x := r) (1 : E →L[ℝ] E)).sub hid
  convert hprod.add hsub using 1 <;> try rfl
  ext H : 1
  change H * (B * r) + (r * B) * H - H = (r * B) * H + (H * B) * r + (0 - H)
  rw [zero_sub, ← sub_eq_add_neg, mul_assoc H, add_comm (H * (B * r))]

variable [CompleteSpace E]

/-- The frozen mode operator is invertible by Lax–Milgram. -/
theorem frozenSymbol_isUnit {r B : E →L[ℝ] E} {μ : ℝ}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection) (hμ : 0 < μ)
    (hB : ∀ v, r v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) : IsUnit (frozenSymbol r B) := by
  let h := frozenSymbol_isCoercive hr hμ hB
  refine ⟨h.continuousLinearEquivOfBilin.toUnit, ?_⟩
  ext v
  apply ext_inner_right ℝ
  intro w
  exact h.continuousLinearEquivOfBilin_apply v w

/-- The inverse on the full space has the uniform mode bound used in Appendix A. -/
theorem norm_frozenSymbol_inverse_le {r B : E →L[ℝ] E} {μ : ℝ}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection) (hμ : 0 < μ)
    (hB : ∀ v, r v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) :
    ‖Ring.inverse (frozenSymbol r B)‖ ≤ (min 1 μ)⁻¹ := by
  have hpos : 0 < min 1 μ := lt_min zero_lt_one hμ
  apply opNorm_le_bound _ (inv_nonneg.mpr hpos.le)
  intro v
  have hright : frozenSymbol r B (Ring.inverse (frozenSymbol r B) v) = v :=
    DFunLike.congr_fun (Ring.mul_inverse_cancel _ (frozenSymbol_isUnit hr hμ hB)) v
  apply (le_inv_mul_iff₀ hpos).mpr
  simpa only [hright] using
    norm_frozenSymbol_lower_bound hr hB (Ring.inverse (frozenSymbol r B) v)

/-- The resolvent bound for two coercive frozen modes. -/
theorem norm_frozenSymbol_inverse_sub_le {r s B C : E →L[ℝ] E} {μ ν : ℝ}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection) (hs : (s : E →ₗ[ℝ] E).IsSymmetricProjection)
    (hμ : 0 < μ) (hν : 0 < ν)
    (hB : ∀ v, r v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ)
    (hC : ∀ v, s v = v → ν * ‖v‖ ^ 2 ≤ ⟪C v, v⟫_ℝ) :
    ‖Ring.inverse (frozenSymbol r B) - Ring.inverse (frozenSymbol s C)‖ ≤
      (min 1 μ)⁻¹ * ‖frozenSymbol s C - frozenSymbol r B‖ * (min 1 ν)⁻¹ := by
  rw [Ring.inverse_sub_inverse (iff_of_true (frozenSymbol_isUnit hr hμ hB) (frozenSymbol_isUnit hs hν hC))]
  calc
    _ ≤ ‖Ring.inverse (frozenSymbol r B)‖ * ‖frozenSymbol s C - frozenSymbol r B‖ *
        ‖Ring.inverse (frozenSymbol s C)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ _ := by
      gcongr
      · exact norm_frozenSymbol_inverse_le hr hμ hB
      · exact norm_frozenSymbol_inverse_le hs hν hC

/-- Fréchet differentiation of the frozen inverse gives the negative product of the inverse,
the symbol variation, and the inverse. -/
theorem hasFDerivAt_frozenSymbol_inverse {r B : E →L[ℝ] E} {μ : ℝ}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection) (hμ : 0 < μ)
    (hB : ∀ v, r v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) :
    let inv := Ring.inverse (frozenSymbol r B)
    HasFDerivAt (fun s => Ring.inverse (frozenSymbol s B))
      ((-mulLeftRight ℝ (E →L[ℝ] E) inv inv).comp (frozenSymbolDerivative r B)) r := by
  obtain ⟨u, hu⟩ := frozenSymbol_isUnit hr hμ hB
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [← Ring.inverse_unit u, hu] at hinv
  exact hinv.comp r (hasFDerivAt_frozenSymbol r B)

theorem fderiv_frozenSymbol_inverse_apply {r B : E →L[ℝ] E} {μ : ℝ}
    (hr : (r : E →ₗ[ℝ] E).IsSymmetricProjection) (hμ : 0 < μ)
    (hB : ∀ v, r v = v → μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫_ℝ) (H : E →L[ℝ] E) :
    let inv := Ring.inverse (frozenSymbol r B)
    fderiv ℝ (fun s => Ring.inverse (frozenSymbol s B)) r H =
      -(inv * frozenSymbolDerivative r B H * inv) := by
  dsimp only
  rw [(hasFDerivAt_frozenSymbol_inverse hr hμ hB).fderiv]
  rfl

end TorusEuler
