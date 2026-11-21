import TorusEuler.TerminalRelayCoefficientProfiles
import TorusEuler.TerminalScheduledParentCoefficients

/-! Coefficient bounds for the same normalized relay used in each selected stage. -/

open Set
open scoped ContDiff

namespace TorusEuler.ScheduledEulerConstruction

open HierarchyTwistedProfile

noncomputable section

set_option maxHeartbeats 900000 in
/-- The exact selected parent coframe and normalized covector supply all
seven relay coefficient bounds. The exponent depends only on the parent
jet power and the fixed envelope radius. -/
theorem exists_scheduledWaveRelayTimeCoefficients (q E : ℕ) (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m) :
    ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
      ∀ {P : InductiveEulerParameters} (c : ScheduledEulerConstruction P) (n : ℕ), 16 ≤ c.radiusExponent →
        c.ScheduledParentCoefficientTimeBounds n q E C →
        let d := (c.selectedStep n).selected
        let geom := d.parent.geometry
        let D := P.frequency (n + 1) ^ (9 : ℕ)
        let exponent := max (6 * E) (c.radiusExponent + 2 * E)
        ∃ R : WaveRelayTimeCoefficients geom.inverse geom.strain geom.covector d.radius (P.frequency (n + 2)),
          ∀ m, WaveRelayTimeCoefficientBudget R d.time_pos d.width (q + 1) m (K m * D ^ exponent) := by
  obtain ⟨Ki, Ko, hKi, hKo, hRelay⟩ := WaveRelayTimeCoefficients.exists_of_parentMixedJetBounds C hC (q + 1)
  refine ⟨fun m => Ki m + Ko m, fun m => add_nonneg (hKi m) (hKo m), ?_⟩
  intro P c n hRadius hb d geom D exponent
  let freq := P.frequency (n + 2)
  have hf : 0 < freq := zero_lt_one.trans_le d.child_frequency_ge_one
  have hD : 1 ≤ D := one_le_two.trans d.parent_scale_ge_two
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have ht : 0 < c.construction.slab (n + 2) := d.time_pos
  have hG := hb.inverse.congr (fun t htime a => (geom.inverse_value (t,a,0) ⟨htime, mem_univ _⟩).symm)
  have hM := hb.gradient.congr (fun t htime a => (geom.strain_value (t,a,0) ⟨htime, mem_univ _⟩).symm)
  have hκeq (t : ℝ) (htime : t ∈ Icc 0 (c.construction.slab (n + 2))) (a : Vec3) :
      c.scheduledParentCovector n t a = freq⁻¹ • geom.covector.val.val.val (t,a,0) :=
    congrArg (fun v : Vec3 => freq⁻¹ • v) (geom.covector_value (t,a,0) ⟨htime, mem_univ _⟩).symm
  have hκ := hb.covector.congr hκeq
  have hι := hb.reciprocal.congr fun t htime a =>
    congrArg (fun v : Vec3 => (‖v‖ ^ 2)⁻¹) (hκeq t htime a)
  have hGPhase := geom.mean.inverse_independent
  have hMPhase : HierarchyPeriodicProfile.PhaseIndependent geom.strain.val.val := by
    intro x hx s
    exact (geom.strain_value (x.1,x.2.1,s) ⟨hx.1, mem_univ _⟩).trans (geom.strain_value x hx).symm
  have hκPhase := geom.oscillation.covector_independent
  have hκne (t : ℝ) (htime : t ∈ Icc 0 (c.construction.slab (n + 2))) (a : Vec3) :
      freq⁻¹ • geom.covector.val.val.val (t,a,0) ≠ 0 :=
    smul_ne_zero (inv_ne_zero hf.ne') (geom.oscillation.covector_ne_zero t htime a)
  obtain ⟨R, hbudget⟩ := hRelay (G := geom.inverse) (M := geom.strain) (κ := geom.covector)
    (ell := d.radius) (h := d.width) (freq := freq) ht d.time_le_one hD (one_le_pow₀ hD : 1 ≤ D ^ E)
    d.regularity.envelope_pos.le (d.radius_mul_parent_power hRadius)
    hGPhase hMPhase hκPhase hκne hG hM hκ hι
  refine ⟨R, fun m => ?_⟩
  have hOuter : ‖d.radius⁻¹‖ * (D ^ E) ^ 2 ≤ D ^ exponent := by
    rw [d.radius_inv, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hD₀ _)]
    change D ^ c.radiusExponent * (D ^ E) ^ 2 ≤ D ^ exponent
    rw [← pow_mul D E 2, ← pow_add D]
    apply pow_le_pow_right₀ hD
    dsimp only [exponent]
    rw [Nat.mul_comm E 2]
    exact le_max_right _ _
  have hInner : (D ^ E) ^ 6 ≤ D ^ exponent := by
    rw [← pow_mul, Nat.mul_comm E 6]
    exact pow_le_pow_right₀ hD (le_max_left _ _)
  have hK : Ki m * (D ^ E) ^ 6 + Ko m * (‖d.radius⁻¹‖ * (D ^ E) ^ 2) ≤
      (Ki m + Ko m) * D ^ exponent := by
    rw [add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hInner (hKi m))
      (mul_le_mul_of_nonneg_left hOuter (hKo m))
  let bound := hbudget m
  exact ⟨bound.potential.trans hK, bound.potentialTime.trans hK, bound.pressureAmplitude.trans hK,
    bound.pressureSource.trans hK, fun i => (bound.curl i).trans hK,
    fun i => (bound.material i).trans hK, fun i => (bound.gradient i).trans hK⟩

end

end TorusEuler.ScheduledEulerConstruction
