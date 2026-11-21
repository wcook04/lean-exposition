import Breakdown.CellReduction.AdjointAssemblyStatements
import Breakdown.CertCell.FormNegativeInverseSquare

open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

private theorem pairing_le_weighted_sum (a b s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) :
    a * b ≤ a ^ 2 / s ^ 2 + s ^ 2 * b ^ 2 := by
  have h1 : a * b = (a / s) * (s * b) := by field_simp
  have h2 : a ^ 2 / s ^ 2 = (a / s) ^ 2 := by rw [div_pow]
  have h3 : s ^ 2 * b ^ 2 = (s * b) ^ 2 := by rw [mul_pow]
  have h4 : 0 ≤ a / s := div_nonneg ha hs.le
  have h5 : 0 ≤ s * b := mul_nonneg hs.le hb
  rw [h1, h2, h3]
  nlinarith [sq_nonneg (a / s - s * b), mul_nonneg h4 h5]

private theorem pairing_enorm_le (p q y : Space) (hy : y ≠ 0) :
    ‖inner ℝ p q‖ₑ ≤ ENNReal.ofReal (‖p‖ ^ 2 / ‖y‖ ^ 2) + ENNReal.ofReal (‖y‖ ^ 2 * ‖q‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm p q).trans
    (pairing_le_weighted_sum _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_pos_iff.2 hy))

end Internal

theorem weightedPairingIntegrable_proof : WeightedPairingIntegrableHolds := by
  intro v T G hv hG hgrad h6 hE hT hW
  have hμ : ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hvμ : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2)
      (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    rw [hμ]; exact hv.restrict
  have hTμ : AEStronglyMeasurable (fun z : ℝ × Space => T z.1 z.2)
      (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    rw [hμ]; exact hT.restrict
  refine ⟨hvμ.inner hTμ, ?_⟩
  have hsnd : AEMeasurable (fun z : ℝ × Space => ‖z.2‖ ^ 2)
      (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    (measurable_snd.norm.pow_const 2).aemeasurable
  have hAm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖v z.1 z.2‖ ^ 2 / ‖z.2‖ ^ 2))
      (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hvμ.norm.aemeasurable.pow_const 2).div hsnd)
  have hBm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖z.2‖ ^ 2 * ‖T z.1 z.2‖ ^ 2))
      (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hsnd.mul (hTμ.norm.aemeasurable.pow_const 2))
  have hvs : ∀ᵐ σ, AEStronglyMeasurable (v σ) volume := hv.prodMk_left
  have hGs : ∀ᵐ σ, AEStronglyMeasurable (G σ) volume := hG.prodMk_left
  have hpt : ∀ᵐ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 2 / ‖y‖ ^ 2)
      ≤ 4 * ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
    filter_upwards [hvs, hGs, hgrad, h6] with σ h1 h2 h3 h4
    exact CertCell.Internal.slice_inverseSquare_lintegral (v σ) (G σ) h1 h2 h3 h4
  have hA : ∫⁻ z, ENNReal.ofReal (‖v z.1 z.2‖ ^ 2 / ‖z.2‖ ^ 2)
      ∂(((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
      ≤ 4 * periodLIntegral (fun σ y => matSq (G σ y)) := by
    rw [lintegral_prod _ hAm]
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    exact lintegral_mono_ae (ae_restrict_of_ae hpt)
  have hB : ∫⁻ z, ENNReal.ofReal (‖z.2‖ ^ 2 * ‖T z.1 z.2‖ ^ 2)
      ∂(((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
      = periodLIntegral (fun σ y => ‖y‖ ^ 2 * ‖T σ y‖ ^ 2) := by
    rw [lintegral_prod _ hBm]
    rfl
  have h0 : ∀ᵐ z ∂(((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      z.2 ≠ 0 := by
    rw [ae_iff]
    have hset : {z : ℝ × Space | ¬ z.2 ≠ 0} = Set.univ ×ˢ ({0} : Set Space) := by
      ext z
      simp
    rw [hset, Measure.prod_prod, measure_singleton, mul_zero]
  have hle : ∫⁻ z, ‖inner ℝ (v z.1 z.2) (T z.1 z.2)‖ₑ
      ∂(((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))
      ≤ ∫⁻ z, ENNReal.ofReal (‖v z.1 z.2‖ ^ 2 / ‖z.2‖ ^ 2)
          + ENNReal.ofReal (‖z.2‖ ^ 2 * ‖T z.1 z.2‖ ^ 2)
      ∂(((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [h0] with z hz
    exact Internal.pairing_enorm_le _ _ _ hz
  rw [lintegral_add_left' hAm, hB] at hle
  have hfinA : 4 * periodLIntegral (fun σ y => matSq (G σ y)) < ⊤ :=
    ENNReal.mul_lt_top (by norm_num) hE
  exact lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt hA hfinA, hW⟩)

end AdjointDefect

end Breakdown
