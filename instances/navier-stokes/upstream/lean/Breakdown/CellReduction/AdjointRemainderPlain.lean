import Breakdown.CellReduction.AdjointStatements
import Breakdown.CellReduction.AdjointAssemblyPairing

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

private theorem plainPairing_enorm_le (p q y : Space) (hy : y ≠ 0) :
    ‖inner ℝ p q‖ₑ ≤ ENNReal.ofReal (‖p‖ / ‖y‖) * ENNReal.ofReal (‖y‖ * ‖q‖) := by
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [← ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  have h : ‖p‖ / ‖y‖ * (‖y‖ * ‖q‖) = ‖p‖ * ‖q‖ := by
    field_simp
  rw [h]
  exact abs_real_inner_le_norm p q

private theorem plainSqrt_four_mul (a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (4 * a) ^ (1 / (2 : ℝ)) = ENNReal.ofReal (2 * Real.sqrt a) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by norm_num)]
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h4]

private theorem plainSqrt_sq (b : ℝ) (hb : 0 ≤ b) :
    ENNReal.ofReal (b ^ 2) ^ (1 / (2 : ℝ)) = ENNReal.ofReal b := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hb]

end Internal

theorem remainderPlainHolds_proof : RemainderPlainHolds := by
  intro R ρ hR v G hv hG hgrad h6 hE
  obtain ⟨hρ, hRm, hRb⟩ := hR
  have hWfin : periodLIntegral (fun σ y => ‖y‖ ^ 2 * ‖R σ y‖ ^ 2) < ⊤ :=
    lt_of_le_of_lt hRb ENNReal.ofReal_lt_top
  have hI := weightedPairingIntegrable_proof v R G hv hG hgrad h6 hE hRm hWfin
  refine ⟨hI.prod_right_ae, hI.integral_prod_left, ?_⟩
  set μ : Measure (ℝ × Space) :=
    ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) with hμdef
  have hμ : μ = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [hμdef, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hvμ : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) μ := by
    rw [hμ]; exact hv.restrict
  have hRμ : AEStronglyMeasurable (fun z : ℝ × Space => R z.1 z.2) μ := by
    rw [hμ]; exact hRm.restrict
  have hsnd : AEMeasurable (fun z : ℝ × Space => ‖z.2‖) μ := measurable_snd.norm.aemeasurable
  have hf : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖v z.1 z.2‖ / ‖z.2‖)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hvμ.norm.aemeasurable.div hsnd)
  have hg : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖z.2‖ * ‖R z.1 z.2‖)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hsnd.mul hRμ.norm.aemeasurable)
  have h0 : ∀ᵐ z ∂μ, z.2 ≠ 0 := by
    rw [ae_iff]
    have hz : μ (Set.univ ×ˢ ({0} : Set Space)) = 0 := by
      rw [hμdef, Measure.prod_prod, measure_singleton, mul_zero]
    refine measure_mono_null (fun z hz' => ?_) hz
    simp only [Set.mem_ofPred_eq, not_not] at hz'
    exact ⟨Set.mem_univ _, hz'⟩
  have hpt : ∫⁻ z, ‖inner ℝ (v z.1 z.2) (R z.1 z.2)‖ₑ ∂μ
      ≤ ∫⁻ z, ((fun z : ℝ × Space => ENNReal.ofReal (‖v z.1 z.2‖ / ‖z.2‖))
        * (fun z : ℝ × Space => ENNReal.ofReal (‖z.2‖ * ‖R z.1 z.2‖))) z ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [h0] with z hz
    exact Internal.plainPairing_enorm_le _ _ _ hz
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have hAeq : (fun z : ℝ × Space => ENNReal.ofReal (‖v z.1 z.2‖ / ‖z.2‖) ^ (2 : ℝ))
      = fun z : ℝ × Space => ENNReal.ofReal (‖v z.1 z.2‖ ^ 2 / ‖z.2‖ ^ 2) := by
    funext z
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity), div_pow]
  have hBeq : (fun z : ℝ × Space => ENNReal.ofReal (‖z.2‖ * ‖R z.1 z.2‖) ^ (2 : ℝ))
      = fun z : ℝ × Space => ENNReal.ofReal (‖z.2‖ ^ 2 * ‖R z.1 z.2‖ ^ 2) := by
    funext z
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity), mul_pow]
  have hAm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖v z.1 z.2‖ ^ 2 / ‖z.2‖ ^ 2)) μ := by
    rw [← hAeq]; exact hf.pow_const _
  have hBm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖z.2‖ ^ 2 * ‖R z.1 z.2‖ ^ 2)) μ := by
    rw [← hBeq]; exact hg.pow_const _
  have hvs : ∀ᵐ σ, AEStronglyMeasurable (v σ) volume := hv.prodMk_left
  have hGs : ∀ᵐ σ, AEStronglyMeasurable (G σ) volume := hG.prodMk_left
  have hslice : ∀ᵐ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 2 / ‖y‖ ^ 2)
      ≤ 4 * ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
    filter_upwards [hvs, hGs, hgrad, h6] with σ h1 h2 h3 h4
    exact CertCell.Internal.slice_inverseSquare_lintegral (v σ) (G σ) h1 h2 h3 h4
  have hA : ∫⁻ z, ENNReal.ofReal (‖v z.1 z.2‖ / ‖z.2‖) ^ (2 : ℝ) ∂μ
      ≤ ENNReal.ofReal (4 * (periodLIntegral (fun σ y => matSq (G σ y))).toReal) := by
    rw [hAeq, hμdef, lintegral_prod _ hAm, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_toReal hE.ne]
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    exact lintegral_mono_ae (ae_restrict_of_ae hslice)
  have hB : ∫⁻ z, ENNReal.ofReal (‖z.2‖ * ‖R z.1 z.2‖) ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal ((ρ / 2) ^ 2) := by
    rw [hBeq, hμdef, lintegral_prod _ hBm]
    exact hRb
  have hbound : ∫⁻ z, ‖inner ℝ (v z.1 z.2) (R z.1 z.2)‖ₑ ∂μ ≤ ENNReal.ofReal (ρ * gradientNorm G) := by
    refine hpt.trans (hH.trans ?_)
    have hA' := ENNReal.rpow_le_rpow hA (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hB' := ENNReal.rpow_le_rpow hB (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Internal.plainSqrt_four_mul _ ENNReal.toReal_nonneg] at hA'
    rw [Internal.plainSqrt_sq _ (by positivity)] at hB'
    refine (mul_le_mul' hA' hB').trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    unfold gradientNorm
    ring
  have hint : periodInnerIntegral v R = ∫ z, inner ℝ (v z.1 z.2) (R z.1 z.2) ∂μ := by
    unfold periodInnerIntegral
    rw [hμdef, integral_prod _ hI]
  have hfin := (enorm_integral_le_lintegral_enorm (μ := μ)
    (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (R z.1 z.2))).trans hbound
  rw [← hint, Real.enorm_eq_ofReal_abs] at hfin
  have hc : 0 ≤ ρ * gradientNorm G := mul_nonneg hρ (Real.sqrt_nonneg _)
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 hfin

end AdjointDefect

end Breakdown
