import Breakdown.CellReduction.AdjointRemainderAzimuthalParts

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

namespace Internal.ModePairing

open CellCert.Reduction

theorem exp_neg_mul_exp (k : ℤ) (θ : ℝ) :
    Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

theorem norm_exp_mode (k : ℤ) (θ : ℝ) : ‖Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)‖ = 1 := by
  have e : (k : ℂ) * (θ : ℂ) = ((k * θ : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

theorem conj_exp_mode (k : ℤ) (θ : ℝ) :
    starRingEnd ℂ (Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) =
      Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I]

theorem mode_of_turn (B : Space → ℂ) (k : ℤ)
    (hB : ∀ ρ θ z : ℝ, B (ringPoint ρ θ z) =
      Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) * B (ringPoint ρ 0 z))
    (ρ z : ℝ) : angularMode B k ρ z = B (ringPoint ρ 0 z) := by
  unfold angularMode
  have e : ∀ θ : ℝ, Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * B (ringPoint ρ θ z) =
      B (ringPoint ρ 0 z) := by
    intro θ
    rw [hB ρ θ z, ← mul_assoc, exp_neg_mul_exp, one_mul]
  simp_rw [e]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

theorem slice_eq (u B : Space → ℂ) (k : ℤ)
    (hturn : ∀ ρ θ z : ℝ, B (ringPoint ρ θ z) =
      Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) * angularMode B k ρ z) (ρ z : ℝ) :
    ∫ θ in Ioc (-Real.pi) Real.pi, starRingEnd ℂ (u (ringPoint ρ θ z)) * B (ringPoint ρ θ z) =
      starRingEnd ℂ (((2 * Real.pi : ℝ) : ℂ) * angularMode u k ρ z) * angularMode B k ρ z := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have e : ∀ θ : ℝ, starRingEnd ℂ (u (ringPoint ρ θ z)) * B (ringPoint ρ θ z) =
      starRingEnd ℂ (Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * u (ringPoint ρ θ z)) *
        angularMode B k ρ z := by
    intro θ
    rw [hturn, map_mul, conj_exp_mode]
    ring
  simp_rw [e]
  have hJ : ∫ θ in Ioc (-Real.pi) Real.pi, Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) * u (ringPoint ρ θ z) =
      ((2 * Real.pi : ℝ) : ℂ) * angularMode u k ρ z := by
    unfold angularMode
    rw [intervalIntegral.integral_of_le hpi]
    have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [← mul_assoc, show ((2 * Real.pi : ℝ) : ℂ) * (1 / (2 * Real.pi) : ℂ) = 1 by push_cast; field_simp,
      one_mul]
  rw [integral_mul_const, integral_conj, hJ]

end Internal.ModePairing

open CellCert.Reduction CellCert.Reduction.ModeMeasurableInternal CellCert.Reduction.ModePairingInternal
  CellCert.Reduction.GradientModeSumInternal Internal.ModePairing in
theorem modePairing : ModePairingHolds := by
  intro u B k hu hB hrot
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hν : volume.restrict (Ioc (-Real.pi) Real.pi) = volume.restrict (Ioo (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  by_cases hi : Integrable (fun y => starRingEnd ℂ (u y) * B y)
  swap
  · rw [integral_undef hi, norm_zero, ENNReal.ofReal_zero]
    simp
  have hturn : ∀ ρ θ z : ℝ, B (ringPoint ρ θ z) =
      Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) * angularMode B k ρ z := by
    intro ρ θ z
    rw [mode_of_turn B k hrot]
    exact hrot ρ θ z
  have hsl : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      IntegrableOn (fun θ => starRingEnd ℂ (u (ringPoint q.1 θ q.2)) * B (ringPoint q.1 θ q.2))
        (Ioc (-Real.pi) Real.pi) := by
    have hm := (hi.1.comp_quasiMeasurePreserving ringMap_qmp).prodMk_left
    filter_upwards [hm, slice_fin (fun y => ‖starRingEnd ℂ (u y) * B y‖) hi.norm] with q hq hfin
    unfold IntegrableOn
    rw [hν]
    exact ⟨hq, (hasFiniteIntegral_iff_norm _).mpr hfin⟩
  set I : ℂ := ∫ y, starRingEnd ℂ (u y) * B y with hI
  have hgi : Integrable (fun y => (starRingEnd ℂ I * (starRingEnd ℂ (u y) * B y)).re) :=
    (hi.const_mul (starRingEnd ℂ I)).re
  have hIsq : ‖I‖ ^ 2 = ∫ y, (starRingEnd ℂ I * (starRingEnd ℂ (u y) * B y)).re := by
    have h1 : ∫ y, (starRingEnd ℂ I * (starRingEnd ℂ (u y) * B y)).re =
        (∫ y, starRingEnd ℂ I * (starRingEnd ℂ (u y) * B y)).re :=
      integral_re (hi.const_mul (starRingEnd ℂ I))
    rw [h1, integral_const_mul, ← hI, mul_comm, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hcr : ∀ r θ z : ℝ, CellCert.Spectral.cylPoint r θ z = ringPoint r θ z := fun _ _ _ => rfl
  rw [CellCert.Spectral.cylIntegral _ hgi] at hIsq
  simp only [hcr] at hIsq
  have hA : ENNReal.ofReal (‖I‖ ^ 2) ≤ ENNReal.ofReal ‖I‖ *
      ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (2 * Real.pi * q.1 * (‖angularMode u k q.1 q.2‖ * ‖angularMode B k q.1 q.2‖)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hIsq]
    refine (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
    filter_upwards [ae_restrict_mem hS, hsl] with q hqS hq
    have hρ : 0 < q.1 := hqS.1
    have e : ∫ θ in (-Real.pi)..Real.pi,
        (starRingEnd ℂ I * (starRingEnd ℂ (u (ringPoint q.1 θ q.2)) * B (ringPoint q.1 θ q.2))).re =
        (starRingEnd ℂ I * (starRingEnd ℂ (((2 * Real.pi : ℝ) : ℂ) * angularMode u k q.1 q.2) *
          angularMode B k q.1 q.2)).re := by
      rw [intervalIntegral.integral_of_le hpi]
      have h1 : ∫ θ in Ioc (-Real.pi) Real.pi,
          (starRingEnd ℂ I * (starRingEnd ℂ (u (ringPoint q.1 θ q.2)) * B (ringPoint q.1 θ q.2))).re =
          (∫ θ in Ioc (-Real.pi) Real.pi,
            starRingEnd ℂ I * (starRingEnd ℂ (u (ringPoint q.1 θ q.2)) * B (ringPoint q.1 θ q.2))).re :=
        integral_re (hq.const_mul (starRingEnd ℂ I))
      rw [h1, integral_const_mul, slice_eq u B k hturn]
    rw [e, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_mul, abs_of_pos hρ]
    calc q.1 * |(starRingEnd ℂ I * (starRingEnd ℂ (((2 * Real.pi : ℝ) : ℂ) * angularMode u k q.1 q.2) *
          angularMode B k q.1 q.2)).re|
        ≤ q.1 * ‖starRingEnd ℂ I * (starRingEnd ℂ (((2 * Real.pi : ℝ) : ℂ) * angularMode u k q.1 q.2) *
          angularMode B k q.1 q.2)‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hρ.le
      _ = ‖I‖ * (2 * Real.pi * q.1 * (‖angularMode u k q.1 q.2‖ * ‖angularMode B k q.1 q.2‖)) := by
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
          ring
  have hmA := (modeMeasurable u hu k).aemeasurable.norm
  have hmB := (modeMeasurable B hB k).aemeasurable.norm
  set F : ℝ × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (Real.sqrt (2 * Real.pi * q.1 / (q.1 ^ 2 + q.2 ^ 2)) * ‖angularMode u k q.1 q.2‖) with hF
  set G : ℝ × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (Real.sqrt (2 * Real.pi * q.1 * (q.1 ^ 2 + q.2 ^ 2)) * ‖angularMode B k q.1 q.2‖) with hG
  have hFm : AEMeasurable F (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) :=
    ((by fun_prop : Measurable fun q : ℝ × ℝ => Real.sqrt (2 * Real.pi * q.1 / (q.1 ^ 2 + q.2 ^ 2))).aemeasurable.mul
      hmA).ennreal_ofReal
  have hGm : AEMeasurable G (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) :=
    ((by fun_prop : Measurable fun q : ℝ × ℝ => Real.sqrt (2 * Real.pi * q.1 * (q.1 ^ 2 + q.2 ^ 2))).aemeasurable.mul
      hmB).ennreal_ofReal
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)))
    Real.HolderConjugate.two_two hFm hGm
  have h1 : ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (2 * Real.pi * q.1 * (‖angularMode u k q.1 q.2‖ * ‖angularMode B k q.1 q.2‖)) ≤
      ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), (F * G) q := by
    refine le_of_eq (setLIntegral_congr_fun hS fun q hq => ?_)
    have hρ : 0 < q.1 := hq.1
    have hs : 0 < q.1 ^ 2 + q.2 ^ 2 := by positivity
    have hAC : Real.sqrt (2 * Real.pi * q.1 / (q.1 ^ 2 + q.2 ^ 2)) *
        Real.sqrt (2 * Real.pi * q.1 * (q.1 ^ 2 + q.2 ^ 2)) = 2 * Real.pi * q.1 := by
      rw [← Real.sqrt_mul (by positivity),
        show 2 * Real.pi * q.1 / (q.1 ^ 2 + q.2 ^ 2) * (2 * Real.pi * q.1 * (q.1 ^ 2 + q.2 ^ 2)) =
          (2 * Real.pi * q.1) ^ 2 by field_simp,
        Real.sqrt_sq (by positivity)]
    rw [Pi.mul_apply, hF, hG, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show Real.sqrt (2 * Real.pi * q.1 / (q.1 ^ 2 + q.2 ^ 2)) * ‖angularMode u k q.1 q.2‖ *
        (Real.sqrt (2 * Real.pi * q.1 * (q.1 ^ 2 + q.2 ^ 2)) * ‖angularMode B k q.1 q.2‖) =
        (Real.sqrt (2 * Real.pi * q.1 / (q.1 ^ 2 + q.2 ^ 2)) *
          Real.sqrt (2 * Real.pi * q.1 * (q.1 ^ 2 + q.2 ^ 2))) *
          (‖angularMode u k q.1 q.2‖ * ‖angularMode B k q.1 q.2‖) by ring, hAC]
  have h2 : ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), F q ^ (2 : ℝ) = modeInverseSquare u k := by
    unfold modeInverseSquare
    refine setLIntegral_congr_fun hS fun q hq => ?_
    have hρ : 0 < q.1 := hq.1
    have hs : 0 < q.1 ^ 2 + q.2 ^ 2 := by positivity
    rw [hF, ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity), mul_pow,
      Real.sq_sqrt (by positivity)]
    congr 1
    ring
  have hfm : AEMeasurable (fun y : Space => ENNReal.ofReal (‖y‖ ^ 2 * ‖B y‖ ^ 2)) volume :=
    ((measurable_norm.pow_const 2).aemeasurable.mul (hB.aemeasurable.norm.pow_const 2)).ennreal_ofReal
  have h3 : ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), G q ^ (2 : ℝ) ≤
      ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖B y‖ ^ 2) := by
    refine le_trans (le_of_eq (setLIntegral_congr_fun hS fun q hq => ?_)) (cyl_le _ hfm)
    have hρ : 0 < q.1 := hq.1
    have e : ∀ θ : ℝ, ENNReal.ofReal (‖ringPoint q.1 θ q.2‖ ^ 2 * ‖B (ringPoint q.1 θ q.2)‖ ^ 2) =
        ENNReal.ofReal ((q.1 ^ 2 + q.2 ^ 2) * ‖angularMode B k q.1 q.2‖ ^ 2) := by
      intro θ
      rw [ring_norm_sq, hturn, norm_mul, norm_exp_mode, one_mul]
    simp only [e]
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo, hG,
      ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hρ.le, mul_pow, Real.sq_sqrt (by positivity)]
    congr 1
    ring
  have hB2 : (∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (2 * Real.pi * q.1 * (‖angularMode u k q.1 q.2‖ * ‖angularMode B k q.1 q.2‖))) ^ 2 ≤
      modeInverseSquare u k * ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ‖B y‖ ^ 2) := by
    calc _ ≤ ((∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), F q ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), G q ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 :=
          pow_le_pow_left₀ zero_le (h1.trans hH) 2
      _ = (∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), F q ^ (2 : ℝ)) *
          ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), G q ^ (2 : ℝ) := by
          rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul]
          norm_num
      _ ≤ _ := by
          rw [h2]
          gcongr
  have hx2 : ENNReal.ofReal ‖I‖ ^ 2 = ENNReal.ofReal (‖I‖ ^ 2) :=
    (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
  rcases eq_or_ne (ENNReal.ofReal ‖I‖) 0 with h0 | h0
  · rw [h0]
    simp
  · have hle : ENNReal.ofReal ‖I‖ ≤ ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
        ENNReal.ofReal (2 * Real.pi * q.1 * (‖angularMode u k q.1 q.2‖ * ‖angularMode B k q.1 q.2‖)) := by
      rw [← ENNReal.mul_le_mul_iff_right h0 ENNReal.ofReal_ne_top, ← sq, hx2]
      exact hA
    exact (pow_le_pow_left₀ zero_le hle 2).trans hB2

end AzimuthalParts

end AdjointDefect

end Breakdown
