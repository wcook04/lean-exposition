/-
Copyright 2026 Anthropic, PBC
SPDX-License-Identifier: Apache-2.0

The rank-one curl and cross-product orthogonality adapt `CCPoint.Exact.antisymmVec_dyad`
and `CCPoint.Exact.inner_cross3_left` from
`sources/ccpoint-lean/CCPoint/Exact/Algebra3.lean`.
The projection argument adapts `CCPoint.Construction.norm_twoLayerCurl_lower` from
`sources/ccpoint-lean/CCPoint/Lib/R03/PointFrame.lean`.
The signed lower bound follows the frozen paper, §8.2, (8.1)–(8.2).
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.LinearAlgebra.CrossProduct

open scoped InnerProductSpace
open NormedSpace (normalize)

namespace TorusEuler

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The standard oriented cross product on three-dimensional Euclidean space. -/
noncomputable def cross3 (k a : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (crossProduct k.ofLp a.ofLp)

/-- The coordinate curl of the rank-one gradient `a ⊗ k` is `k × a`. -/
theorem coordinateCurl_rankOne (a k : ℝ³) :
    let D := (innerSL ℝ k).smulRight a
    let D₀ := D (EuclideanSpace.single 0 1)
    let D₁ := D (EuclideanSpace.single 1 1)
    let D₂ := D (EuclideanSpace.single 2 1)
    WithLp.toLp 2 ![D₁ 2 - D₂ 1, D₂ 0 - D₀ 2, D₀ 1 - D₁ 0] = cross3 k a := by
  dsimp only
  simp [cross3, cross_apply, EuclideanSpace.inner_single_right]

@[simp] theorem inner_cross3_left (k a : ℝ³) : ⟪k, cross3 k a⟫_ℝ = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, cross3,
    WithLp.ofLp_toLp, dotProduct_comm]
  exact dot_self_cross k.ofLp a.ofLp

/-- The newest layer has zero curl component along its normalized wave vector. -/
@[simp] theorem inner_normalize_cross3_left (k a : ℝ³) :
    ⟪normalize k, cross3 k a⟫_ℝ = 0 := by
  rw [NormedSpace.normalize, real_inner_smul_left, inner_cross3_left, mul_zero]

/-- A lower bound on the newest scaled wave vector's component along the preceding
frame axis gives the signed projection onto the normalized newest direction. -/
theorem inner_normalize_cross3_ge_of_frame {k a k' frameAxis : ℝ³}
    {strength carrier component lengthBound : ℝ} (hk' : k' ≠ 0)
    (hframe : cross3 k a = strength • frameAxis) (hstrength : 0 ≤ strength)
    (hcarrier : 0 < carrier) (hcomponent : 0 ≤ component)
    (haxis : component ≤ ⟪carrier⁻¹ • k', frameAxis⟫_ℝ)
    (hlength : ‖carrier⁻¹ • k'‖ ≤ lengthBound) :
    strength * (component / lengthBound) ≤ ⟪normalize k', cross3 k a⟫_ℝ := by
  let scaled := carrier⁻¹ • k'
  have hcarrierInv : 0 < carrier⁻¹ := inv_pos.mpr hcarrier
  have hscaled : 0 < ‖scaled‖ := norm_pos_iff.mpr (smul_ne_zero hcarrierInv.ne' hk')
  have hratio : component / lengthBound ≤ ⟪scaled, frameAxis⟫_ℝ / ‖scaled‖ :=
    (div_le_div_of_nonneg_left hcomponent hscaled hlength).trans
      (div_le_div_of_nonneg_right haxis hscaled.le)
  calc
    strength * (component / lengthBound) ≤
        strength * (⟪scaled, frameAxis⟫_ℝ / ‖scaled‖) :=
      mul_le_mul_of_nonneg_left hratio hstrength
    _ = ⟪normalize k', cross3 k a⟫_ℝ := by
      rw [← NormedSpace.normalize_smul_of_pos hcarrierInv k', hframe]
      change _ = ⟪normalize scaled, strength • frameAxis⟫_ℝ
      simp only [real_inner_smul_right, NormedSpace.normalize, real_inner_smul_left, div_eq_inv_mul]

/-- The projected curl is independent of the newest layer's cutoff coefficient. -/
theorem inner_normalize_twoLayerCurl (b k a k' a' : ℝ³) (cutoff : ℝ) :
    ⟪normalize k', b + cross3 k a + cutoff • cross3 k' a'⟫_ℝ =
      ⟪normalize k', b⟫_ℝ + ⟪normalize k', cross3 k a⟫_ℝ := by
  simp [inner_add_right, real_inner_smul_right]

/-- The full curl norm is bounded below by the signed projection of the preceding
layer minus a norm bound for the older curl and errors. -/
theorem norm_twoLayerCurl_ge_of_projection {b k a k' a' : ℝ³}
    {backgroundBound signedLower : ℝ} (cutoff : ℝ) (hk' : k' ≠ 0)
    (hb : ‖b‖ ≤ backgroundBound) (hprojection : signedLower ≤ ⟪normalize k', cross3 k a⟫_ℝ) :
    signedLower - backgroundBound ≤ ‖b + cross3 k a + cutoff • cross3 k' a'‖ := by
  have hunit : ‖normalize k'‖ = 1 := NormedSpace.norm_normalize hk'
  have hbackground : -backgroundBound ≤ ⟪normalize k', b⟫_ℝ := by
    have habs := abs_real_inner_le_norm (normalize k') b
    rw [hunit, one_mul] at habs
    exact neg_le_of_abs_le (habs.trans hb)
  calc
    signedLower - backgroundBound = -backgroundBound + signedLower := sub_eq_neg_add _ _
    _ ≤ ⟪normalize k', b⟫_ℝ + ⟪normalize k', cross3 k a⟫_ℝ :=
      add_le_add hbackground hprojection
    _ = ⟪normalize k', b + cross3 k a + cutoff • cross3 k' a'⟫_ℝ :=
      (inner_normalize_twoLayerCurl b k a k' a' cutoff).symm
    _ ≤ ‖b + cross3 k a + cutoff • cross3 k' a'‖ := by
      simpa only [hunit, one_mul] using
        real_inner_le_norm (normalize k') (b + cross3 k a + cutoff • cross3 k' a')

end TorusEuler
