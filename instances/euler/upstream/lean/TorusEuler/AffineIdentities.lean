/-
Copyright 2026 Anthropic, PBC
SPDX-License-Identifier: Apache-2.0

The orthogonality calculation is adapted from `CCPoint.Exact.perp_deriv_coeff`
and `CCPoint.Exact.pressureCoeff_cancels` in
`sources/ccpoint-lean/CCPoint/Exact/Layer.lean`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Ring

open scoped InnerProductSpace

namespace TorusEuler

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {a k : ℝ → E} {s : Set ℝ} {t : ℝ} {D : E →L[ℝ] E} {p : ℝ}

/-- The derivative of the wave polarization pairing for an arbitrary pressure coefficient. -/
theorem hasDerivWithinAt_affineWavePairing
    (hk : HasDerivWithinAt k (-(D.adjoint (k t))) s t)
    (ha : HasDerivWithinAt a (-(D (a t)) + p • k t) s t) :
    HasDerivWithinAt (fun τ => ⟪k τ, a τ⟫_ℝ)
      (-2 * ⟪k t, D (a t)⟫_ℝ + p * ‖k t‖ ^ 2) s t := by
  refine (hk.inner ℝ ha).congr_deriv ?_
  rw [inner_add_right, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    inner_neg_left, ContinuousLinearMap.adjoint_inner_left]
  ring

/-- The pointwise derivative of the pairing in Lemma 2.1. -/
theorem hasDerivAt_affineWavePairing
    (hk : HasDerivAt k (-(D.adjoint (k t))) t)
    (ha : HasDerivAt a (-(D (a t)) + p • k t) t) :
    HasDerivAt (fun τ => ⟪k τ, a τ⟫_ℝ)
      (-2 * ⟪k t, D (a t)⟫_ℝ + p * ‖k t‖ ^ 2) t := by
  simpa only [hasDerivWithinAt_univ] using
    hasDerivWithinAt_affineWavePairing (s := Set.univ) hk.hasDerivWithinAt ha.hasDerivWithinAt

/-- The pressure coefficient in (2.1) makes the pairing derivative vanish. -/
theorem hasDerivWithinAt_affineWavePairing_zero
    (hk₀ : k t ≠ 0) (hk : HasDerivWithinAt k (-(D.adjoint (k t))) s t)
    (ha : HasDerivWithinAt a
      (-(D (a t)) + (2 * ⟪k t, D (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) s t) :
    HasDerivWithinAt (fun τ => ⟪k τ, a τ⟫_ℝ) 0 s t := by
  refine (hasDerivWithinAt_affineWavePairing hk ha).congr_deriv ?_
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hk₀))]
  ring

/-- The pointwise pressure cancellation in the proof of Lemma 2.1. -/
theorem hasDerivAt_affineWavePairing_zero
    (hk₀ : k t ≠ 0) (hk : HasDerivAt k (-(D.adjoint (k t))) t)
    (ha : HasDerivAt a (-(D (a t)) + (2 * ⟪k t, D (a t)⟫_ℝ / ‖k t‖ ^ 2) • k t) t) :
    HasDerivAt (fun τ => ⟪k τ, a τ⟫_ℝ) 0 t := by
  simpa only [hasDerivWithinAt_univ] using
    hasDerivWithinAt_affineWavePairing_zero hk₀ (s := Set.univ)
      hk.hasDerivWithinAt ha.hasDerivWithinAt

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {a k : ℝ → E} {s : Set ℝ} {t : ℝ} {D : E →L[ℝ] E} {p : ℝ}

/-- Half the squared amplitude norm has the strain derivative of §2.1. -/
theorem hasDerivWithinAt_affineWaveHalfNormSq
    (ha : HasDerivWithinAt a (-(D (a t)) + p • k t) s t)
    (hperp : ⟪k t, a t⟫_ℝ = 0) :
    HasDerivWithinAt (fun τ => (1 / 2 : ℝ) * ‖a τ‖ ^ 2) (-⟪a t, D (a t)⟫_ℝ) s t := by
  refine (ha.norm_sq.const_mul (1 / 2)).congr_deriv ?_
  rw [inner_add_right, inner_neg_right, real_inner_smul_right, real_inner_comm (k t) (a t),
    hperp]
  ring

/-- The pointwise amplitude growth identity of §2.1. -/
theorem hasDerivAt_affineWaveHalfNormSq
    (ha : HasDerivAt a (-(D (a t)) + p • k t) t)
    (hperp : ⟪k t, a t⟫_ℝ = 0) :
    HasDerivAt (fun τ => (1 / 2 : ℝ) * ‖a τ‖ ^ 2) (-⟪a t, D (a t)⟫_ℝ) t := by
  simpa only [hasDerivWithinAt_univ] using
    hasDerivWithinAt_affineWaveHalfNormSq (s := Set.univ) ha.hasDerivWithinAt hperp

end

end TorusEuler
