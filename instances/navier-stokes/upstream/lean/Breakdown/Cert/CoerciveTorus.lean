import Breakdown.Cert.CoerciveNodes

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace Coercive

namespace TorusInternal

def sliceCoeff (g : ℝ → ℝ → ℝ) (m : ℤ) (τ : ℝ) : ℂ :=
  fourierCoeffOn Real.two_pi_pos (fun φ => (g τ φ : ℂ)) m

theorem tsum_ofReal_sq_transformCoeffOn {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc a b))) :
    ∑' i : ℤ, ENNReal.ofReal (‖fourierCoeffOn hab f i‖ ^ 2) =
      ENNReal.ofReal ((b - a)⁻¹) * ∫⁻ x in Icc a b, ENNReal.ofReal (‖f x‖ ^ 2) := by
  have hres : volume.restrict (Ioc a b) = volume.restrict (Icc a b) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  have hf' : MemLp f 2 (volume.restrict (Ioc a b)) := by rw [hres]; exact hf
  have hs := hasSum_sq_fourierCoeffOn hab hf'
  have hint : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs.summable, hs.tsum_eq,
    intervalIntegral.integral_of_le hab.le, hres, smul_eq_mul,
    ENNReal.ofReal_mul (inv_nonneg.2 (sub_nonneg.2 hab.le)),
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun x => by positivity))]

theorem modeAverage_eq (g : ℝ → ℝ → ℝ) (n m : ℤ) :
    modeAverage (n, m) (fun τ φ (_ : Unit) => g τ φ) () =
      fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) (sliceCoeff g m) n := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hexp : ∀ τ φ : ℝ,
      Complex.exp (-(((2 * Real.pi * (n : ℝ) * τ + (m : ℝ) * φ : ℝ) : ℂ) * Complex.I)) =
        fourier (-n) (τ : AddCircle ((1 : ℝ) - 0)) *
          fourier (-m) (φ : AddCircle (2 * Real.pi - 0)) := by
    intro τ φ
    rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  simp only [modeAverage, sliceCoeff, fourierCoeffOn_eq_integral, hexp, smul_eq_mul,
    Complex.real_smul]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  simp only [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  push_cast
  ring

end TorusInternal

open TorusInternal

theorem torusSquareSumHolds_proof : TorusSquareSumHolds := by
  intro g hg hfin
  have hg2 : AEStronglyMeasurable (fun z : ℝ × ℝ => g z.1 z.2 ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))) :=
    hg.pow 2
  have hI : Integrable (fun z : ℝ × ℝ => g z.1 z.2 ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))) := by
    refine ⟨hg2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _),
      lintegral_prod _ hg2.aemeasurable.ennreal_ofReal]
    exact hfin
  have hsec : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) 1)),
      MemLp (fun φ => (g τ φ : ℂ)) 2 (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [hg.prodMk_left, hI.prod_right_ae] with τ hm hi
    have hm' : AEStronglyMeasurable (fun φ => (g τ φ : ℂ))
        (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hm
    refine (memLp_two_iff_integrable_sq_norm hm').2 ?_
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hi
  have hres2 : volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)) =
      volume.restrict (Icc (0 : ℝ) (2 * Real.pi)) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  have ha_meas : ∀ m : ℤ, AEStronglyMeasurable (sliceCoeff g m) (volume.restrict (Icc (0 : ℝ) 1)) := by
    intro m
    have heq : sliceCoeff g m = fun τ => (1 / (2 * Real.pi - 0)) •
        ∫ φ, fourier (-m) (φ : AddCircle (2 * Real.pi - 0)) • (g τ φ : ℂ)
          ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) := by
      funext τ
      rw [sliceCoeff, fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le Real.two_pi_pos.le,
        hres2]
    rw [heq]
    refine AEStronglyMeasurable.const_smul ?_ (1 / (2 * Real.pi - 0) : ℝ)
    have hc : Continuous (fun z : ℝ × ℝ => fourier (-m) (z.2 : AddCircle (2 * Real.pi - 0))) := by
      simp only [fourier_coe_apply]
      fun_prop
    have hF : AEStronglyMeasurable
        (fun z : ℝ × ℝ => fourier (-m) (z.2 : AddCircle (2 * Real.pi - 0)) • (g z.1 z.2 : ℂ))
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))) :=
      hc.aestronglyMeasurable.smul (Complex.continuous_ofReal.comp_aestronglyMeasurable hg)
    exact hF.integral_prod_right'
  have hB : Integrable (fun τ => (2 * Real.pi - 0)⁻¹ *
      ∫ φ, g τ φ ^ 2 ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    hI.integral_prod_left.const_mul _
  have ha_L2 : ∀ m : ℤ, MemLp (sliceCoeff g m) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
    intro m
    refine (memLp_two_iff_integrable_sq_norm (ha_meas m)).2
      (hB.mono' ((ha_meas m).norm.pow 2) ?_)
    filter_upwards [hsec] with τ hτ
    have hτ' : MemLp (fun φ => (g τ φ : ℂ)) 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
      rw [hres2]; exact hτ
    have hs := hasSum_sq_fourierCoeffOn Real.two_pi_pos hτ'
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, hres2, smul_eq_mul] at hs
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hs
    rw [Real.norm_of_nonneg (by positivity)]
    exact le_hasSum hs m (fun j _ => by positivity)
  have hmode : ∀ ι : ℤ × ℤ, modeAverage ι (fun τ φ (_ : Unit) => g τ φ) () =
      fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) (sliceCoeff g ι.2) ι.1 :=
    fun ι => modeAverage_eq g ι.1 ι.2
  simp_rw [hmode]
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  calc ∑' m : ℤ, ∑' n : ℤ,
        ENNReal.ofReal (‖fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) (sliceCoeff g m) n‖ ^ 2)
      = ∑' m : ℤ, ∫⁻ τ in Icc (0 : ℝ) 1, ENNReal.ofReal (‖sliceCoeff g m τ‖ ^ 2) := by
        refine tsum_congr fun m => ?_
        rw [tsum_ofReal_sq_transformCoeffOn _ (ha_L2 m)]
        simp
    _ = ∫⁻ τ in Icc (0 : ℝ) 1, ∑' m : ℤ, ENNReal.ofReal (‖sliceCoeff g m τ‖ ^ 2) :=
        (lintegral_tsum fun m => ((ha_meas m).norm.pow 2).aemeasurable.ennreal_ofReal).symm
    _ = ∫⁻ τ in Icc (0 : ℝ) 1, ENNReal.ofReal ((2 * Real.pi - 0)⁻¹) *
          ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (‖(g τ φ : ℂ)‖ ^ 2) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hsec] with τ hτ
        exact tsum_ofReal_sq_transformCoeffOn Real.two_pi_pos hτ
    _ = ENNReal.ofReal (1 / (2 * Real.pi)) *
          ∫⁻ τ in Icc (0 : ℝ) 1, ∫⁻ φ in Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (g τ φ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, sub_zero, one_div]
        simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Coercive

end Breakdown
