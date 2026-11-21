import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.FarField.Internal

private theorem quarticRadial_antideriv_hasDerivAt {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun t : ℝ => -(t + a)⁻¹ + a * ((t + a)⁻¹) ^ 2 - a ^ 2 / 3 * ((t + a)⁻¹) ^ 3)
      (r ^ 2 * ((r + a) ^ 4)⁻¹) r := by
  have hne : r + a ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => t + a) 1 r := (hasDerivAt_id' r).add_const a
  have hu : HasDerivAt (fun t : ℝ => (t + a)⁻¹) (-(1 : ℝ) / (r + a) ^ 2) r := h1.inv hne
  have h := ((hu.neg).add ((hu.pow 2).const_mul a)).sub ((hu.pow 3).const_mul (a ^ 2 / 3))
  refine h.congr_deriv ?_
  rw [show (2 : ℕ) - 1 = 1 from rfl, show (3 : ℕ) - 1 = 2 from rfl, inv_pow]
  push_cast
  field_simp
  ring

private theorem quarticRadial_antideriv_tendsto {a : ℝ} :
    Tendsto (fun t : ℝ => -(t + a)⁻¹ + a * ((t + a)⁻¹) ^ 2 - a ^ 2 / 3 * ((t + a)⁻¹) ^ 3)
      atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => (t + a)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ a tendsto_id)
  have hP : Continuous (fun u : ℝ => -u + a * u ^ 2 - a ^ 2 / 3 * u ^ 3) := by fun_prop
  convert (hP.tendsto 0).comp hu using 2 <;> simp

private theorem quarticRadial_integral {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r ^ 2 * ((r + a) ^ 4)⁻¹) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), r ^ 2 * ((r + a) ^ 4)⁻¹ = (3 * a)⁻¹ := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt
      (fun t : ℝ => -(t + a)⁻¹ + a * ((t + a)⁻¹) ^ 2 - a ^ 2 / 3 * ((t + a)⁻¹) ^ 3)
      (x ^ 2 * ((x + a) ^ 4)⁻¹) x := fun x hx => quarticRadial_antideriv_hasDerivAt ha hx
  have hp : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ x ^ 2 * ((x + a) ^ 4)⁻¹ := by
    intro x hx
    have : 0 < x + a := by linarith [hx.out]
    positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp quarticRadial_antideriv_tendsto, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hp quarticRadial_antideriv_tendsto]
  have : a ≠ 0 := ha.ne'
  field_simp
  ring

end Breakdown.FarField.Internal

namespace Breakdown.FarField

open Internal in
theorem kernelMassBound_holds : KernelMassBound := by
  intro τ hτ y
  have ha : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  set a := Real.sqrt τ with ha_def
  obtain ⟨hint, hval⟩ := quarticRadial_integral ha
  have hfin : Module.finrank ℝ Space = 3 := by simp
  have hI : Integrable (fun x : Space => ((‖x‖ + a) ^ 4)⁻¹) := by
    rw [integrable_fun_norm_addHaar volume (f := fun r : ℝ => ((r + a) ^ 4)⁻¹), hfin]
    simpa only [smul_eq_mul] using hint
  have hV : volume.real (Metric.ball (0 : Space) 1) = π * 4 / 3 := by
    rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
    simp [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ π * 4 / 3)]
  have hE : ∫ x : Space, ((‖x‖ + a) ^ 4)⁻¹ = 4 * π / (3 * a) := by
    rw [integral_fun_norm_addHaar volume (fun r : ℝ => ((r + a) ^ 4)⁻¹), hfin, hV]
    simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
    rw [hval]
    field_simp
  refine ⟨?_, ?_⟩
  · exact hI.comp_sub_left y
  · rw [integral_sub_left_eq_self (fun x : Space => ((‖x‖ + a) ^ 4)⁻¹) volume y, hE]
    rw [div_le_iff₀ (by positivity)]
    have := Real.pi_lt_d2
    field_simp
    nlinarith

end Breakdown.FarField
