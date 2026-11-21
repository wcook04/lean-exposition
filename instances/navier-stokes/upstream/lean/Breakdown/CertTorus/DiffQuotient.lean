import Breakdown.CertTorus.ShiftCovariance

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

noncomputable section

namespace Breakdown.FarField

open Freq

namespace Internal.DifferenceQuotient

open Internal.TranslationCovariance

def phaseSlope (c t : ℝ) : ℂ :=
  ((t⁻¹ : ℝ) : ℂ) * (Complex.exp (Complex.I * ((c * t : ℝ) : ℂ)) - 1)

def slopeRemainder (j : Fin 3) (x : X) (t : ℝ) (ξ : Space) : CSpace :=
  (phaseSlope (2 * π * ξ j) t - Complex.I * ((2 * π * ξ j : ℝ) : ℂ)) • symX x ξ

theorem phase_neg_smul_unitVector (j : Fin 3) (t : ℝ) (ξ : Space) :
    phase (-(t • unitVector j)) ξ = Complex.exp (Complex.I * ((2 * π * ξ j * t : ℝ) : ℂ)) := by
  rw [phase]
  congr 1
  have h : inner ℝ (-(t • unitVector j)) ξ = -(t * ξ j) := by
    simp [unitVector, inner_neg_left, inner_smul_left, EuclideanSpace.inner_single_left]
  rw [h]
  push_cast
  ring

theorem monoSymbol_single (j : Fin 3) (ξ : Space) :
    monoSymbol ![j] ξ = Complex.I * ((2 * π * ξ j : ℝ) : ℂ) := by
  rw [monoSymbol, Fin.prod_univ_one]
  simp only [Matrix.cons_val_zero]
  ring

theorem norm_phaseSlope_le (c t : ℝ) : ‖phaseSlope c t‖ ≤ |c| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [phaseSlope]
  rw [phaseSlope, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |t⁻¹| * ‖Complex.exp (Complex.I * ((c * t : ℝ) : ℂ)) - 1‖ ≤ |t⁻¹| * ‖c * t‖ :=
        mul_le_mul_of_nonneg_left Real.norm_exp_I_mul_ofReal_sub_one_le (abs_nonneg _)
    _ = |c| := by
        rw [Real.norm_eq_abs, abs_mul, abs_inv, mul_comm |c|, ← mul_assoc,
          inv_mul_cancel₀ (abs_ne_zero.mpr ht), one_mul]

theorem tendsto_phaseSlope (c : ℝ) :
    Tendsto (phaseSlope c) (𝓝[≠] 0) (𝓝 (Complex.I * (c : ℂ))) := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.I * ((c * t : ℝ) : ℂ)) (Complex.I * (c : ℂ)) 0 := by
    have h0 := (((hasDerivAt_id (0 : ℝ)).const_mul c).ofReal_comp).const_mul Complex.I
    simpa using h0
  have hd := h1.cexp
  rw [hasDerivAt_iff_tendsto_slope_zero] at hd
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • (Complex.exp (Complex.I * ((c * (0 + t) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((c * 0 : ℝ) : ℂ)))) (𝓝[≠] 0) (𝓝 (Complex.I * (c : ℂ))) := by
    simpa using hd
  refine hlim.congr' (Eventually.of_forall fun t => ?_)
  simp [phaseSlope, Complex.real_smul]

theorem quotient_coe_ae (j : Fin 3) (x : X) (t : ℝ) :
    (((t⁻¹ • (shiftX (-(t • unitVector j)) x - x) : X) : L2C) : Space → CSpace) =ᵐ[volume]
      fun ξ => phaseSlope (2 * π * ξ j) t • symX x ξ := by
  rw [Submodule.coe_smul, Submodule.coe_sub, shiftX_coe]
  filter_upwards [Lp.coeFn_smul t⁻¹ (modL2 (-(t • unitVector j)) (x : L2C) - (x : L2C)),
    Lp.coeFn_sub (modL2 (-(t • unitVector j)) (x : L2C)) (x : L2C),
    modL2_ae (-(t • unitVector j)) (x : L2C)] with ξ e1 e2 e3
  rw [e1, Pi.smul_apply, e2, Pi.sub_apply, e3, phase_neg_smul_unitVector, symX, phaseSlope,
    mul_smul, sub_smul, one_smul, Complex.coe_smul]

theorem norm_slopeRemainder_le (j : Fin 3) (x : X) (t : ℝ) (ξ : Space) :
    ‖slopeRemainder j x t ξ‖ ≤ 2 * ‖(Complex.I * ((2 * π * ξ j : ℝ) : ℂ)) • symX x ξ‖ := by
  have h2 : ‖Complex.I * ((2 * π * ξ j : ℝ) : ℂ)‖ = |2 * π * ξ j| := by simp
  rw [slopeRemainder, norm_smul, norm_smul, h2]
  have h1 := norm_phaseSlope_le (2 * π * ξ j) t
  have h3 : ‖phaseSlope (2 * π * ξ j) t - Complex.I * ((2 * π * ξ j : ℝ) : ℂ)‖ ≤
      2 * |2 * π * ξ j| := by
    refine (norm_sub_le _ _).trans ?_
    rw [h2]
    linarith
  calc ‖phaseSlope (2 * π * ξ j) t - Complex.I * ((2 * π * ξ j : ℝ) : ℂ)‖ * ‖symX x ξ‖
      ≤ (2 * |2 * π * ξ j|) * ‖symX x ξ‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ = 2 * (|2 * π * ξ j| * ‖symX x ξ‖) := by ring

theorem continuous_coord (j : Fin 3) : Continuous fun ξ : Space => ξ j := by
  fun_prop

theorem aemeasurable_slopeRemainder (j : Fin 3) (x : X) (t : ℝ) :
    AEMeasurable (fun ξ => ‖slopeRemainder j x t ξ‖ₑ ^ (2 : ℝ)) volume := by
  have hc : Continuous fun ξ : Space =>
      phaseSlope (2 * π * ξ j) t - Complex.I * ((2 * π * ξ j : ℝ) : ℂ) := by
    have hj := continuous_coord j
    unfold phaseSlope
    fun_prop
  have hg : AEStronglyMeasurable (symX x) volume := Lp.aestronglyMeasurable _
  exact (hc.aestronglyMeasurable.smul hg).enorm.pow_const _

theorem tendsto_slopeRemainder (j : Fin 3) (x : X) (ξ : Space) :
    Tendsto (fun t => ‖slopeRemainder j x t ξ‖ₑ ^ (2 : ℝ)) (𝓝[≠] 0) (𝓝 0) := by
  have h1 := (tendsto_phaseSlope (2 * π * ξ j)).sub_const (Complex.I * ((2 * π * ξ j : ℝ) : ℂ))
  rw [sub_self] at h1
  have h2 := (h1.smul_const (symX x ξ))
  rw [zero_smul] at h2
  have h3 := ((continuous_enorm.tendsto _).comp h2)
  rw [enorm_zero] at h3
  have h4 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp h3
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h4
  exact h4

theorem tendsto_of_isDerivX (j : Fin 3) (x y : X) (hy : IsDerivX ![j] x y) :
    Tendsto (fun t : ℝ => t⁻¹ • (shiftX (-(t • unitVector j)) x - x)) (𝓝[≠] 0) (𝓝 y) := by
  rw [tendsto_subtype_rng]
  refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr ?_
  have hcongr : ∀ t : ℝ,
      eLpNorm (⇑((t⁻¹ • (shiftX (-(t • unitVector j)) x - x) : X) : L2C) - ⇑(y : L2C)) 2 volume =
        eLpNorm (slopeRemainder j x t) 2 volume := by
    intro t
    apply eLpNorm_congr_ae
    filter_upwards [quotient_coe_ae j x t, hy] with ξ e1 e2
    rw [Pi.sub_apply, e1, show ((y : L2C) : Space → CSpace) ξ = symX y ξ from rfl, e2,
      monoSymbol_single, slopeRemainder, sub_smul]
  have hbound : ∀ t : ℝ, ∀ᵐ ξ ∂volume,
      ‖slopeRemainder j x t ξ‖ₑ ^ (2 : ℝ) ≤ (2 * ‖symX y ξ‖ₑ) ^ (2 : ℝ) := by
    intro t
    filter_upwards [hy] with ξ hξ
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [hξ, monoSymbol_single, ← ofReal_norm, ← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal (norm_slopeRemainder_le j x t ξ)).trans_eq ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp
  have hfin : ∫⁻ ξ, (2 * ‖symX y ξ‖ₑ) ^ (2 : ℝ) ∂volume ≠ ⊤ := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    rw [lintegral_const_mul' _ _ (by simp)]
    refine ENNReal.mul_ne_top (by simp) ?_
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num) (by norm_num)
      (Lp.eLpNorm_lt_top (y : L2C))
    rw [ENNReal.toReal_ofNat] at h
    exact h.ne
  have hI : Tendsto (fun t => ∫⁻ ξ, ‖slopeRemainder j x t ξ‖ₑ ^ (2 : ℝ) ∂volume) (𝓝[≠] 0)
      (𝓝 (∫⁻ _ : Space, (0 : ℝ≥0∞) ∂volume)) :=
    tendsto_lintegral_filter_of_dominated_convergence' _
      (Eventually.of_forall fun t => aemeasurable_slopeRemainder j x t)
      (Eventually.of_forall hbound) hfin
      (Eventually.of_forall fun ξ => tendsto_slopeRemainder j x ξ)
  rw [lintegral_zero] at hI
  have h4 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto _).comp hI
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h4
  refine h4.congr' (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply]
  beta_reduce
  rw [hcongr t,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ENNReal.toReal_ofNat]

theorem isDerivX_of_tendsto (j : Fin 3) (x y : X)
    (hQ : Tendsto (fun t : ℝ => t⁻¹ • (shiftX (-(t • unitVector j)) x - x)) (𝓝[≠] 0) (𝓝 y)) :
    IsDerivX ![j] x y := by
  have hu0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Eventually.of_forall fun n => by
        simp only [mem_compl_iff, mem_singleton_iff]
        positivity
  have hseq := tendsto_subtype_rng.mp (hQ.comp hu0)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hseq).exists_seq_tendsto_ae
  have hall : ∀ᵐ ξ ∂volume, ∀ n : ℕ,
      ((((1 / ((n : ℝ) + 1))⁻¹ • (shiftX (-((1 / ((n : ℝ) + 1)) • unitVector j)) x - x) : X) :
        L2C) : Space → CSpace) ξ = phaseSlope (2 * π * ξ j) (1 / ((n : ℝ) + 1)) • symX x ξ :=
    ae_all_iff.mpr fun n => quotient_coe_ae j x (1 / ((n : ℝ) + 1))
  filter_upwards [hae, hall] with ξ h1 h2
  rw [monoSymbol_single]
  have h3 : Tendsto (fun i => phaseSlope (2 * π * ξ j) (1 / ((ns i : ℝ) + 1)) • symX x ξ) atTop
      (𝓝 ((Complex.I * ((2 * π * ξ j : ℝ) : ℂ)) • symX x ξ)) :=
    ((tendsto_phaseSlope _).comp (hu0.comp hns.tendsto_atTop)).smul_const _
  refine tendsto_nhds_unique ?_ h3
  exact h1.congr' (Eventually.of_forall fun i => h2 (ns i))

end Internal.DifferenceQuotient

theorem diffQuotient_holds : DiffQuotient := fun j x y =>
  ⟨Internal.DifferenceQuotient.tendsto_of_isDerivX j x y,
    Internal.DifferenceQuotient.isDerivX_of_tendsto j x y⟩

end Breakdown.FarField
