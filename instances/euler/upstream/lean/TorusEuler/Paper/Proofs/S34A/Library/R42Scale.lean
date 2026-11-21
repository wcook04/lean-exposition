import TorusEuler.Paper.S34A.Statements

/-! Glue for the proof of **Theorem 4.2** (package S34A): the time rescaling
`τ = t/T` of the endpoint system (4.9) (sections/06b_mean_inverse.tex:175–177), the
congruence of (4.9) in its coefficients, and comparison of closed-time norms under
rescaling. No numbered result is used. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

/-- Normed group structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance r42SolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
/-- Real normed space structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance r42SolenoidalNormedSpace : NormedSpace ℝ S := inferInstance


/-- The scaling `τ ↦ σ τ` maps `[0,T₂]` into `[0,T₁]` when `σ T₂ = T₁`. -/
theorem mapsTo_scale {σ T₁ T₂ : ℝ} (hσ : 0 < σ) (hT : σ * T₂ = T₁) :
    MapsTo (fun τ : ℝ => σ * τ) (Icc 0 T₂) (Icc 0 T₁) := fun _ hτ =>
  ⟨mul_nonneg hσ.le hτ.1, hT ▸ mul_le_mul_of_nonneg_left hτ.2 hσ.le⟩

/-- Coefficient multiplication is linear in the coefficient. -/
theorem coefficientMul_smul (σ : ℝ) (B : K½) (w : C½) :
    (σ • B).coefficientMul w = σ • B.coefficientMul w :=
  HalfHolder.ext fun a => by
    simp only [HalfHolder.eval_coefficientMul, map_smul, _root_.smul_apply]

/-- The left side of (4.9) under the time rescaling `t = σ τ`, with coefficients
`K(στ)`, `σ Ω(στ)` and source `src(στ)`: the integral `∫_0^{στ} Ω v` becomes
`∫_0^τ σ Ω(σs) v(σs) ds`. -/
theorem integratedMomentum_scale {σ : ℝ} (K Ω : ℝ → K½) (src : ℝ → C½) (v : ℝ → S) (τ : ℝ) :
    paperMeanIntegratedMomentum (fun s => K (σ * s)) (fun s => σ • Ω (σ * s))
        (fun s => src (σ * s)) (fun s => v (σ * s)) τ =
      paperMeanIntegratedMomentum K Ω src v (σ * τ) := by
  unfold paperMeanIntegratedMomentum endpointPrimitive
  congr 2
  simp only [coefficientMul_smul]
  rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left
    (fun r => (Ω r).coefficientMul (v r).val) σ, mul_zero]

/-- The endpoint system (4.9) is invariant under the time rescaling `t = σ τ`
(sections/06b_mean_inverse.tex:175–176: `τ = t/T`, `Z(τ) = z(t)/T`, `Z_τ = v`): a solution
on `[0,T₁]` gives the solution `(σ⁻¹ z(σ·), v(σ·), c, φ(σ·), ∇φ(σ·))` on `[0,T₂]` for the
coefficients `K(σ·)`, `σ Ω(σ·)` and the source `src(σ·)`, where `σ T₂ = T₁`. -/
theorem endpointSystemSolution_scale {σ T₁ T₂ : ℝ} (hσ : 0 < σ) (hT : σ * T₂ = T₁)
    {K Ω : ℝ → K½} {src : ℝ → C½} {z v : ℝ → S} {c : S} {φ : Pressure} {G : ℝ → C½}
    (hs : EndpointSystemSolution T₁ K Ω src z v c φ G) :
    EndpointSystemSolution T₂ (fun τ => K (σ * τ)) (fun τ => σ • Ω (σ * τ))
      (fun τ => src (σ * τ)) (fun τ => σ⁻¹ • z (σ * τ)) (fun τ => v (σ * τ)) c
      (fun τ => φ (σ * τ)) (fun τ => G (σ * τ)) := by
  have hmap := mapsTo_scale hσ hT
  have hlin : Continuous (fun τ : ℝ => σ * τ) := continuous_const.mul continuous_id
  refine ⟨hs.velocity_continuous.comp hlin.continuousOn hmap, ?_, ?_, ?_,
    hs.gradient_continuous.comp hlin.continuousOn hmap, fun τ hτ => hs.potential _ (hmap hτ),
    fun τ hτ => ?_⟩
  · intro τ hτ
    have hd : HasDerivWithinAt (fun τ : ℝ => σ * τ) σ (Icc 0 T₂) τ := by
      simpa using ((hasDerivAt_id τ).const_mul σ).hasDerivWithinAt
    have h := ((hs.displacement_deriv _ (hmap hτ)).scomp τ hd hmap).const_smul σ⁻¹
    rw [smul_smul, inv_mul_cancel₀ hσ.ne', one_smul] at h
    exact h
  · simp only [mul_zero, hs.initial, smul_zero]
  · simp only [hT, hs.terminal, smul_zero]
  · rw [integratedMomentum_scale]
    exact hs.equation _ (hmap hτ)

/-- (4.9) depends on the coefficients and the source only through their values on `I`. -/
theorem integratedMomentum_congr {T : ℝ} {K K' Ω Ω' : ℝ → K½} {src src' : ℝ → C½}
    (v : ℝ → S) (hK : EqOn K K' (Icc 0 T)) (hΩ : EqOn Ω Ω' (Icc 0 T))
    (hs : EqOn src src' (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, paperMeanIntegratedMomentum K Ω src v t =
      paperMeanIntegratedMomentum K' Ω' src' v t := by
  intro t ht
  unfold paperMeanIntegratedMomentum
  rw [hK ht, hs ht]
  congr 2
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht.1]
  intro r hr
  change (Ω r).coefficientMul (v r).val = (Ω' r).coefficientMul (v r).val
  rw [hΩ ⟨hr.1, hr.2.trans ht.2⟩]

/-- Congruence of the solution class of (4.9) in the coefficients and the source. -/
theorem EndpointSystemSolution.congr {T : ℝ} {K K' Ω Ω' : ℝ → K½} {src src' : ℝ → C½}
    {z v : ℝ → S} {c : S} {φ : Pressure} {G : ℝ → C½}
    (hs : EndpointSystemSolution T K Ω src z v c φ G) (hK : EqOn K K' (Icc 0 T))
    (hΩ : EqOn Ω Ω' (Icc 0 T)) (hsrc : EqOn src src' (Icc 0 T)) :
    EndpointSystemSolution T K' Ω' src' z v c φ G :=
  ⟨hs.velocity_continuous, hs.displacement_deriv, hs.initial, hs.terminal,
    hs.gradient_continuous, hs.potential, fun t ht => by
      rw [← integratedMomentum_congr v hK hΩ hsrc t ht]
      exact hs.equation t ht⟩

/-- The closed-time norm does not increase under the rescaling `τ ↦ σ τ` of
`[0,T₂]` into `[0,T₁]`. -/
theorem endpointClosedTimeNorm_scale_le {E : Type*} [NormedAddCommGroup E] {σ T₁ T₂ : ℝ}
    (hσ : 0 < σ) (hT : σ * T₂ = T₁) (hT₂ : 0 ≤ T₂) {f : ℝ → E}
    (hf : ContinuousOn f (Icc 0 T₁)) :
    endpointClosedTimeNorm T₂ (fun τ => f (σ * τ)) ≤ endpointClosedTimeNorm T₁ f :=
  endpointClosedTimeNorm_le hT₂ fun _ hτ =>
    norm_le_endpointClosedTimeNorm hf (mapsTo_scale hσ hT hτ)

end

end TorusEuler.Paper.Lib.S34A
