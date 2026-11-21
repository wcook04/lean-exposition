import TorusEuler.LocalizedSeedRegularity

/-! The unswitched leading wave in the homogeneous case of Lemma 5.5. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.LocalizedAmplitude.SeedOn

variable {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
  {center : ℝ → Vec3} {t₀ T ell D C h : ℝ}

private theorem deriv_leadingPressure (w : SeedOn M κ center t₀ T ell D C)
    (hh : 0 < h) (hh₁ : h ≤ 1) (t : ℝ) (a : Vec3) (s : ℝ) :
    deriv (w.leadingPressure h t a) s =
      (radialEnvelope ell a * waveProfile h s) *
        oscillatoryPressureSlope (M t a) (κ t a) 0 (w.amplitude t a) := by
  have hd := ((hasDerivAt_wavePressurePrimitive hh hh₁ s).const_mul
    (-wavePressureCoefficient (radialEnvelope ell a) (κ t a) (w.amplitude t a) (M t a))).deriv
  change deriv (w.leadingPressure h t a) s = _ at hd
  rw [hd]
  simp only [wavePressureCoefficient, oscillatoryPressureSlope, inner_zero_right, zero_sub, div_eq_mul_inv]
  ring

/-- The unswitched leading wave satisfies the homogeneous transverse equation
throughout the closed active interval. -/
theorem hasDerivWithinAt_leading_homogeneous_momentum (w : SeedOn M κ center t₀ T ell D C)
    (hh : 0 < h) (hh₁ : h ≤ 1) {t : ℝ} (ht : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt (fun u => w.leading h u a s)
      (-M t a (w.leading h t a s) - deriv (w.leadingPressure h t a) s • κ t a)
      (Icc t₀ T) t := by
  let b := radialEnvelope ell a * waveProfile h s
  have hAmp := (w.equation a t ht).const_smul b
  have hOp := affineWaveAmplitudeOperator_add_transverseProjection (M t a) (κ t a) 0 (w.amplitude t a)
  simp only [map_zero, add_zero, zero_sub] at hOp
  apply hAmp.congr_deriv
  rw [hOp, deriv_leadingPressure w hh hh₁]
  simp only [b, SeedOn.leading, map_smul, smul_sub, smul_neg, smul_smul]

/-- The unswitched case of Lemma 5.5 has zero forcing and the required
transversality and phase normalizations. -/
theorem paper_hierarchy_leading_homogeneous (w : SeedOn M κ center t₀ T ell D C)
    (hI : t₀ < T) (hh : 0 < h) (hh₁ : h ≤ 1)
    {t : ℝ} (ht : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    (derivWithin (fun u => w.leading h u a s) (Icc t₀ T) t +
      M t a (w.leading h t a s) + deriv (w.leadingPressure h t a) s • κ t a = 0) ∧
      ⟪κ t a, w.leading h t a s⟫_ℝ = 0 ∧
      phaseMean (w.leading h t a) = 0 ∧ phaseMean (w.leadingPressure h t a) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(w.hasDerivWithinAt_leading_homogeneous_momentum hh hh₁ ht a s).derivWithin
      (uniqueDiffOn_Icc hI t ht)]
    abel
  · simp only [SeedOn.leading, real_inner_smul_right, w.transverse a t ht, mul_zero]
  · let L := toSpanSingleton ℝ (radialEnvelope ell a • w.amplitude t a)
    have hL : w.leading h t a = fun s => L (waveProfile h s) := by
      funext s
      change (radialEnvelope ell a * waveProfile h s) • w.amplitude t a =
        waveProfile h s • (radialEnvelope ell a • w.amplitude t a)
      rw [smul_smul, mul_comm]
    rw [hL, phaseMean, L.intervalIntegral_comp_comm
      ((contDiff_waveProfile hh hh₁).continuous.intervalIntegrable 0 1), ← phaseMean,
      phaseMean_waveProfile hh hh₁, map_zero]
  · change phaseMean (fun s =>
      (-wavePressureCoefficient (radialEnvelope ell a) (κ t a) (w.amplitude t a) (M t a)) •
        wavePressurePrimitive h s) = 0
    rw [phaseMean_const_smul, phaseMean_wavePressurePrimitive hh hh₁, smul_zero]

end TorusEuler.LocalizedAmplitude.SeedOn
