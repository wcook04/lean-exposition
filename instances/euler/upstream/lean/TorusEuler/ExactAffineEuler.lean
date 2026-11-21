/-
Copyright 2026 Anthropic, PBC
SPDX-License-Identifier: Apache-2.0

The affine time derivative and pressure calculation are adapted from
`CCPoint.Exact.hasDerivWithinAt_fullField` and `CCPoint.Exact.pressure_pd3` in
`sources/ccpoint-lean/CCPoint/Exact/Layer.lean`.
-/
import TorusEuler.AffineWave
import TorusEuler.Statement
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open scoped InnerProductSpace

namespace TorusEuler

/-- The affine velocity plus one plane wave in Lemma 2.1 (cc:lem:wave). -/
noncomputable def affineWaveVelocity (F : ℝ → ℝ) (D : ℝ → Vec3 →L[ℝ] Vec3) (k a : ℝ → Vec3) :
    Velocity :=
  fun t x => D t x + F ⟪k t, x⟫_ℝ • a t

/-- The coefficient of the wave pressure in (cc:eq:wave-ode). -/
noncomputable def affineWavePressureCoeff (D : Vec3 →L[ℝ] Vec3) (k a : Vec3) : ℝ :=
  2 * ⟪k, D a⟫_ℝ / ‖k‖ ^ 2

/-- The pressure at a fixed time in Lemma 2.1, with `S = D' + D²`. -/
noncomputable def affineWavePressure (P : ℝ → ℝ) (S : Vec3 →L[ℝ] Vec3)
    (p : ℝ) (k : Vec3) (x : Vec3) : ℝ :=
  -(1 / 2 : ℝ) * ⟪x, S x⟫_ℝ - p * P ⟪k, x⟫_ℝ

section

variable {F : ℝ → ℝ} {D : ℝ → Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3} {t : ℝ}
  {s : Set ℝ} {D' : Vec3 →L[ℝ] Vec3} {k' a' : Vec3} {dF : ℝ} {x : Vec3}

/-- The spatial derivative of the affine velocity plus the wave. -/
theorem hasFDerivAt_affineWaveVelocity (hF : HasDerivAt F dF ⟪k t, x⟫_ℝ) :
    HasFDerivAt (affineWaveVelocity F D k a t)
      (D t + (dF • innerSL ℝ (k t)).smulRight (a t)) x :=
  (D t).hasFDerivAt.add (hasFDerivAt_planeWave F (a t) (k t) x dF hF)

/-- The time derivative of the affine velocity plus the wave, with position fixed. -/
theorem hasDerivWithinAt_affineWaveVelocity
    (hD : HasDerivWithinAt D D' s t) (hk : HasDerivWithinAt k k' s t)
    (ha : HasDerivWithinAt a a' s t) (hF : HasDerivAt F dF ⟪k t, x⟫_ℝ) :
    HasDerivWithinAt (fun r => affineWaveVelocity F D k a r x)
      (D' x + (F ⟪k t, x⟫_ℝ • a' + (dF * ⟪k', x⟫_ℝ) • a t)) s t := by
  have hlinear : HasDerivWithinAt (fun r => D r x) (D' x) s t := by
    simpa using hD.clm_apply (hasDerivWithinAt_const t s x)
  have hphase : HasDerivWithinAt (fun r => ⟪k r, x⟫_ℝ) ⟪k', x⟫_ℝ s t := by
    simpa using hk.inner ℝ (hasDerivWithinAt_const t s x)
  exact HasDerivWithinAt.add hlinear ((hF.comp_hasDerivWithinAt t hphase).smul ha)

end

/-- A transverse plane wave has zero self-advection. -/
theorem planeWave_selfAdvection {F : ℝ → ℝ} {a k x : Vec3} {dF : ℝ}
    (hF : HasDerivAt F dF ⟪k, x⟫_ℝ) (hperp : ⟪k, a⟫_ℝ = 0) :
    fderiv ℝ (fun y => F ⟪k, y⟫_ℝ • a) x (F ⟪k, x⟫_ℝ • a) = 0 := by
  rw [(hasFDerivAt_planeWave F a k x dF hF).fderiv]
  simp [hperp]

section

variable {F : ℝ → ℝ} {D : ℝ → Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3}
  {t : ℝ} {s : Set ℝ} {D' : Vec3 →L[ℝ] Vec3} {a' : Vec3} {dF : ℝ} {x : Vec3}

/-- The wave-vector ODE cancels phase transport, and perpendicularity
    cancels self-advection in the material acceleration. -/
theorem affineWave_materialAcceleration (hs : UniqueDiffWithinAt ℝ s t)
    (hD : HasDerivWithinAt D D' s t)
    (hk : HasDerivWithinAt k (-((D t).adjoint (k t))) s t)
    (ha : HasDerivWithinAt a a' s t) (hF : HasDerivAt F dF ⟪k t, x⟫_ℝ)
    (hperp : ⟪k t, a t⟫_ℝ = 0) :
    derivWithin (fun r => affineWaveVelocity F D k a r x) s t +
      fderiv ℝ (affineWaveVelocity F D k a t) x (affineWaveVelocity F D k a t x) =
      (D' + (D t).comp (D t)) x + F ⟪k t, x⟫_ℝ • (a' + D t (a t)) := by
  rw [(hasDerivWithinAt_affineWaveVelocity hD hk ha hF).derivWithin hs,
    (hasFDerivAt_affineWaveVelocity (D := D) (a := a) hF).fderiv]
  simp only [affineWaveVelocity, add_apply, ContinuousLinearMap.comp_apply,
    map_add, map_smul, ContinuousLinearMap.smulRight_apply, smul_apply,
    innerSL_apply_apply, hperp, mul_zero, zero_smul, add_zero,
    smul_add, smul_eq_mul, inner_neg_left, ContinuousLinearMap.adjoint_inner_left, mul_neg,
    neg_smul]
  abel

/-- The divergence is the background trace plus the rank-one wave trace. -/
theorem divergence_affineWaveVelocity (hF : HasDerivAt F dF ⟪k t, x⟫_ℝ) :
    divergence (affineWaveVelocity F D k a t) x =
      LinearMap.trace ℝ Vec3 (D t : Vec3 →ₗ[ℝ] Vec3) + dF * ⟪k t, a t⟫_ℝ := by
  rw [divergence, (hasFDerivAt_affineWaveVelocity (D := D) (a := a) hF).fderiv]
  let M := D t + (dF • innerSL ℝ (k t)).smulRight (a t)
  change ∑ i : Fin 3, (M (EuclideanSpace.single i 1)) i = _
  have htrace : ∑ i : Fin 3, (M (EuclideanSpace.single i 1)) i =
      LinearMap.trace ℝ Vec3 (M : Vec3 →ₗ[ℝ] Vec3) := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  rw [htrace]
  change LinearMap.trace ℝ Vec3 ((D t : Vec3 →ₗ[ℝ] Vec3) +
    ((dF • innerSL ℝ (k t) : Vec3 →L[ℝ] ℝ) : Vec3 →ₗ[ℝ] ℝ).smulRight (a t)) = _
  rw [map_add, LinearMap.trace_smulRight]
  rfl

end

/-- The gradient of the quadratic background pressure and the wave primitive. -/
theorem hasGradientAt_affineWavePressure {F P : ℝ → ℝ} {S : Vec3 →L[ℝ] Vec3}
    (hS : IsSelfAdjoint S) (p : ℝ) (k x : Vec3)
    (hP : HasDerivAt P (F ⟪k, x⟫_ℝ) ⟪k, x⟫_ℝ) :
    HasGradientAt (affineWavePressure P S p k)
      (-(S x + F ⟪k, x⟫_ℝ • (p • k))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hq := (hasFDerivAt_id x).inner ℝ S.hasFDerivAt
  have hw := hP.comp_hasFDerivAt x (innerSL ℝ k).hasFDerivAt
  refine ((hq.const_mul (-(1 / 2) : ℝ)).sub (hw.const_mul p)).congr_fderiv ?_
  ext v
  have hsymm : ⟪x, S v⟫_ℝ = ⟪v, S x⟫_ℝ := by
    rw [← S.adjoint_inner_left, hS.adjoint_eq, real_inner_comm]
  simp [fderivInnerCLM_apply, hsymm, real_inner_comm v (S x)]
  ring

/-- The exact affine plane wave in Lemma 2.1 satisfies the momentum and
    incompressibility equations on ℝ³ for any time set with unique time derivatives. -/
theorem affineWave_solvesEulerOn {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    {F P : ℝ → ℝ} (hF : Differentiable ℝ F) (hP : ∀ z, HasDerivAt P (F z) z)
    {D D' : ℝ → Vec3 →L[ℝ] Vec3} {k a : ℝ → Vec3}
    (hD : ∀ t ∈ s, HasDerivWithinAt D (D' t) s t)
    (hS : ∀ t ∈ s, IsSelfAdjoint (D' t + (D t).comp (D t)))
    (htr : ∀ t ∈ s, LinearMap.trace ℝ Vec3 (D t : Vec3 →ₗ[ℝ] Vec3) = 0)
    (hk : ∀ t ∈ s, HasDerivWithinAt k (-((D t).adjoint (k t))) s t)
    (ha : ∀ t ∈ s, HasDerivWithinAt a
      (-(D t (a t)) + affineWavePressureCoeff (D t) (k t) (a t) • k t) s t)
    (hperp : ∀ t ∈ s, ⟪k t, a t⟫_ℝ = 0) :
    ∀ t ∈ s, ∀ x,
      derivWithin (fun r => affineWaveVelocity F D k a r x) s t +
        fderiv ℝ (affineWaveVelocity F D k a t) x (affineWaveVelocity F D k a t x) +
        gradient (affineWavePressure P (D' t + (D t).comp (D t))
          (affineWavePressureCoeff (D t) (k t) (a t)) (k t)) x = 0 ∧
      divergence (affineWaveVelocity F D k a t) x = 0 := by
  intro t ht x
  have hFx := (hF ⟪k t, x⟫_ℝ).hasDerivAt
  constructor
  · rw [affineWave_materialAcceleration (hs t ht) (hD t ht) (hk t ht) (ha t ht) hFx
      (hperp t ht), (hasGradientAt_affineWavePressure (hS t ht) _ _ _ (hP _)).gradient]
    simp
  · rw [divergence_affineWaveVelocity hFx, htr t ht, hperp t ht, mul_zero, add_zero]

end TorusEuler
