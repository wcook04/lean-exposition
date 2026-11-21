import TorusEuler.CurlProjection
import TorusEuler.PhaseCalculus

open scoped InnerProductSpace

namespace TorusEuler

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

def cross3Left (κ : ℝ³) : ℝ³ →L[ℝ] ℝ³ :=
  let coordinates := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  coordinates.symm.toContinuousLinearMap.comp
    ((crossProduct κ.ofLp).toContinuousLinearMap.comp coordinates.toContinuousLinearMap)

theorem cross3Left_apply (κ v : ℝ³) : cross3Left κ v = cross3 κ v :=
  rfl

/-- The oriented vector triple product on the Euclidean space used for the wave. -/
theorem cross3_cross3 (κ u v : ℝ³) :
    cross3 κ (cross3 u v) = ⟪κ, v⟫_ℝ • u - ⟪u, κ⟫_ℝ • v := by
  apply WithLp.ofLp_injective
  simp only [cross3, WithLp.ofLp_toLp, WithLp.ofLp_sub, WithLp.ofLp_smul,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm v.ofLp κ.ofLp, dotProduct_comm κ.ofLp u.ofLp]
  exact cross_cross_eq_smul_sub_smul' κ.ofLp u.ofLp v.ofLp

/-- The normalized negative cross product is a right inverse of the fast curl on transverse vectors. -/
theorem cross3_neg_inv_norm_sq_smul {κ v : ℝ³} (hκ : κ ≠ 0) (htrans : ⟪κ, v⟫_ℝ = 0) :
    cross3 κ ((-(‖κ‖ ^ 2)⁻¹) • cross3 κ v) = v := by
  have hnorm : ‖κ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hκ)
  rw [← cross3Left_apply, map_smul, cross3Left_apply, cross3_cross3, htrans,
    real_inner_self_eq_norm_sq, zero_smul, zero_sub, smul_neg, ← neg_smul, neg_neg,
    smul_smul, inv_mul_cancel₀ hnorm, one_smul]

/-- The normalized periodic potential of the transverse profile in (3.5). -/
def wavePotential (κ : ℝ³) (V : ℝ → ℝ³) : ℝ → ℝ³ :=
  phasePrimitive (fun s => (-(‖κ‖ ^ 2)⁻¹) • cross3 κ (V s))

private theorem continuous_wavePotential_profile (κ : ℝ³) {V : ℝ → ℝ³} (hV : Continuous V) :
    Continuous (fun s => (-(‖κ‖ ^ 2)⁻¹) • cross3 κ (V s)) := by
  change Continuous (fun s => (-(‖κ‖ ^ 2)⁻¹) • cross3Left κ (V s))
  exact ((cross3Left κ).continuous.comp hV).const_smul (-(‖κ‖ ^ 2)⁻¹)

theorem phaseMean_wavePotential (κ : ℝ³) {V : ℝ → ℝ³} (hV : Continuous V) :
    phaseMean (wavePotential κ V) = 0 :=
  phaseMean_phasePrimitive (continuous_wavePotential_profile κ hV)

theorem periodic_wavePotential (κ : ℝ³) {V : ℝ → ℝ³} (hV : Continuous V)
    (hperiodic : Function.Periodic V 1) (hmean : phaseMean V = 0) :
    Function.Periodic (wavePotential κ V) 1 := by
  apply periodic_phasePrimitive (continuous_wavePotential_profile κ hV)
  · intro s
    simp only [hperiodic s]
  · rw [phaseMean_const_smul]
    have hcross : phaseMean (fun s => cross3 κ (V s)) = cross3 κ (phaseMean V) := by
      simpa only [phaseMean, Function.comp_apply, cross3Left_apply] using
        (cross3Left κ).intervalIntegral_comp_comm (hV.intervalIntegrable 0 1)
    rw [hcross, hmean, ← cross3Left_apply, map_zero, smul_zero]

theorem hasDerivAt_wavePotential (κ : ℝ³) {V : ℝ → ℝ³} (hV : Continuous V) (s : ℝ) :
    HasDerivAt (wavePotential κ V) ((-(‖κ‖ ^ 2)⁻¹) • cross3 κ (V s)) s :=
  hasDerivAt_phasePrimitive (continuous_wavePotential_profile κ hV) s

/-- The fast curl of the potential recovers the transverse oscillation in (3.5). -/
theorem wavePotential_fast_curl {κ : ℝ³} {V : ℝ → ℝ³} (hκ : κ ≠ 0) (hV : Continuous V)
    (htrans : ∀ s, ⟪κ, V s⟫_ℝ = 0) (s : ℝ) :
    cross3 κ (deriv (wavePotential κ V) s) = V s := by
  rw [(hasDerivAt_wavePotential κ hV s).deriv]
  exact cross3_neg_inv_norm_sq_smul hκ (htrans s)

/-- Recover the longitudinal component in (3.6) from its phase derivative and zero phase mean. -/
theorem waveCorrection_longitudinal {κ : ℝ³} {C : ℝ → ℝ³} {divV : ℝ → ℝ}
    (hderiv : ∀ s, HasDerivAt (fun r => ⟪κ, C r⟫_ℝ) (-divV s) s)
    (hdiv : Continuous divV) (hmean : phaseMean (fun s => ⟪κ, C s⟫_ℝ) = 0) (s : ℝ) :
    ⟪κ, C s⟫_ℝ = -phasePrimitive divV s := by
  have hneg : ∀ s, HasDerivAt (fun r => -⟪κ, C r⟫_ℝ) (divV s) s :=
    fun s => by simpa only [neg_neg] using (hderiv s).fun_neg
  have hmean_neg : phaseMean (fun r => -⟪κ, C r⟫_ℝ) = 0 := by
    rw [phaseMean, intervalIntegral.integral_neg, ← phaseMean, hmean, neg_zero]
  have hprimitive := congrFun (phasePrimitive_deriv hneg hdiv) s
  simpa only [phaseOscillation, hmean_neg, sub_zero, neg_neg] using
    (congrArg Neg.neg hprimitive).symm

/-- A zero-mean continuous correction has a zero-mean longitudinal component. -/
theorem waveCorrection_longitudinal_of_mean_zero {κ : ℝ³} {C : ℝ → ℝ³} {divV : ℝ → ℝ}
    (hderiv : ∀ s, HasDerivAt (fun r => ⟪κ, C r⟫_ℝ) (-divV s) s)
    (hdiv : Continuous divV) (hC : Continuous C) (hmean : phaseMean C = 0) (s : ℝ) :
    ⟪κ, C s⟫_ℝ = -phasePrimitive divV s := by
  apply waveCorrection_longitudinal hderiv hdiv
  change (∫ r in (0 : ℝ)..1, (innerSL ℝ κ) (C r)) = 0
  rw [(innerSL ℝ κ).intervalIntegral_comp_comm (hC.intervalIntegrable 0 1),
    ← phaseMean, hmean, map_zero]

end

end TorusEuler
