import Breakdown.Uniqueness.RegAprioriAuxEnergyPart2
import Breakdown.Uniqueness.RegAprioriAuxEnergyPart3
import Breakdown.Uniqueness.RegPersistAuxMeas

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem lintegral_homNormSq_two_le (m : ℕ) (hm : 3 ≤ m) (M T : ℝ) : ∃ K : ℝ, ∀ T' ∈ Icc 0 T,
    ∀ F : ℝ → Space → CSpace, IsHsCurve m F 0 T' → IsVarConstSymbol F 0 T' →
      (∀ t ∈ Icc 0 T', IsSolenoidalSymbol (F t)) →
      (∀ t ∈ Icc 0 T', homNormSq 1 (F t) ≤ ENNReal.ofReal M) →
      ∫⁻ s in Icc 0 T', homNormSq 2 (F s) ≤ ENNReal.ofReal K := by
  obtain ⟨C, hC⟩ := lintegral_weight_mul_nonlinSymbol_le
  have ha : 0 ≤ 2 * max C 0 * max M 0 ^ (3 / 4 : ℝ) := by positivity
  have hc : 0 ≤ (2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) *
      ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) / (4 * π ^ 2)) ^ 3 := by positivity
  refine ⟨(max M 0 + (2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) *
      ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) / (4 * π ^ 2)) ^ 3 * T) / (4 * π ^ 2), ?_⟩
  intro T' hT' F hF hd hs hM
  rcases eq_or_lt_of_le hT'.1 with h0 | hpos
  · have hz : volume.restrict (Icc (0 : ℝ) T') = 0 := by
      rw [← h0, Icc_self]; exact Measure.restrict_eq_zero.2 Real.volume_singleton
    rw [hz, lintegral_zero_measure]; exact bot_le
  have hT0 : (0 : ℝ) ∈ Icc 0 T' := ⟨le_rfl, hpos.le⟩
  have h1 : IsHsCurve 1 F 0 T' := isHsCurve_of_le (by omega) hF
  have h3 : IsHsCurve 3 F 0 T' := isHsCurve_of_le hm hF
  have hFm := aemeasurable_enorm_apply_of_varConst hpos h1 hd
  have hNm := aemeasurable_enorm_nonlinSymbol h3 hs
  have hw : AEMeasurable (fun p : ℝ × Space => ENNReal.ofReal (‖p.2‖ ^ (2 * 2)))
      ((volume.restrict (Icc 0 T')).prod volume) :=
    (continuous_snd.norm.pow _).measurable.ennreal_ofReal.aemeasurable
  have hw' : AEMeasurable (fun p : ℝ × Space => ENNReal.ofReal (‖p.2‖ ^ (2 * 1)))
      ((volume.restrict (Icc 0 T')).prod volume) :=
    (continuous_snd.norm.pow _).measurable.ennreal_ofReal.aemeasurable
  have hI : (∫⁻ s in Icc 0 T', homNormSq 2 (F s)) =
      ∫⁻ ξ, ∫⁻ s in Icc 0 T', ENNReal.ofReal (‖ξ‖ ^ (2 * 2)) * ‖F s ξ‖ₑ ^ 2 := by
    unfold homNormSq
    exact lintegral_lintegral_swap (f := fun s ξ => ENNReal.ofReal (‖ξ‖ ^ (2 * 2)) * ‖F s ξ‖ₑ ^ 2)
      (hw.mul (hFm.pow_const 2))
  have hJ : ∫⁻ ξ, ∫⁻ s in Icc 0 T', ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) *
        (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) =
      ∫⁻ s in Icc 0 T', ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) *
        (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) :=
    (lintegral_lintegral_swap (f := fun s ξ => ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) *
        (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ)) (hw'.mul (hFm.mul hNm))).symm
  have hm0 : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖F 0 ξ‖ₑ ^ 2) volume :=
    (continuous_norm.pow _).measurable.ennreal_ofReal.aemeasurable.mul
      ((hF.1 0 hT0).1.enorm.pow_const 2)
  have hstep : ENNReal.ofReal (8 * π ^ 2) * (∫⁻ s in Icc 0 T', homNormSq 2 (F s)) ≤
      homNormSq 1 (F 0) + ∫⁻ s in Icc 0 T', 2 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) *
        (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) := by
    rw [hI, lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ← hJ,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), homNormSq,
      ← lintegral_add_left' hm0]
    exact lintegral_mono fun ξ => energy_inequality_apply hpos h1 hd ξ
  have hpt : ∀ s ∈ Icc 0 T', 2 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) *
        (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) ≤
      ENNReal.ofReal (4 * π ^ 2) * homNormSq 2 (F s) +
        ENNReal.ofReal ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) *
          ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) / (4 * π ^ 2)) ^ 3) := by
    intro s hs'
    have hfs := hF.1 s hs'
    have h3s : hsNormSq 3 (F s) < ⊤ := lt_of_le_of_lt (hsNormSq_le_hsNormSq_of_le hm _) hfs.2
    calc 2 * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ)
        ≤ 2 * (ENNReal.ofReal C * homNormSq 1 (F s) ^ (3 / 4 : ℝ) *
            homNormSq 2 (F s) ^ (3 / 4 : ℝ)) := by
          gcongr; exact hC _ hfs.1 (hs s hs') h3s
      _ ≤ 2 * (ENNReal.ofReal (max C 0) * ENNReal.ofReal (max M 0) ^ (3 / 4 : ℝ) *
            homNormSq 2 (F s) ^ (3 / 4 : ℝ)) := by
          gcongr
          · exact le_max_left _ _
          · exact (hM s hs').trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal (2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) *
            homNormSq 2 (F s) ^ (3 / 4 : ℝ) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) (by norm_num),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
          simp only [ENNReal.ofReal_ofNat]
          ring
      _ ≤ _ := ofReal_mul_rpow_three_quarters_le ha _
  have hfin := setLIntegral_homNormSq_two_lt_top (by omega) hF
  have hint : ∫⁻ s in Icc 0 T', (ENNReal.ofReal (4 * π ^ 2) * homNormSq 2 (F s) +
        ENNReal.ofReal ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) *
          ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) / (4 * π ^ 2)) ^ 3)) =
      ENNReal.ofReal (4 * π ^ 2) * (∫⁻ s in Icc 0 T', homNormSq 2 (F s)) +
        ENNReal.ofReal ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) *
          ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) / (4 * π ^ 2)) ^ 3) * ENNReal.ofReal T' := by
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      setLIntegral_const, Real.volume_Icc, sub_zero]
  have hmain : ENNReal.ofReal (8 * π ^ 2) * (∫⁻ s in Icc 0 T', homNormSq 2 (F s)) ≤
      ENNReal.ofReal (max M 0) + (ENNReal.ofReal (4 * π ^ 2) * (∫⁻ s in Icc 0 T', homNormSq 2 (F s)) +
        ENNReal.ofReal ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) *
          ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) / (4 * π ^ 2)) ^ 3) * ENNReal.ofReal T') := by
    refine hstep.trans ?_
    rw [← hint]
    exact add_le_add ((hM 0 hT0).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      (setLIntegral_mono' measurableSet_Icc hpt)
  have hX : ENNReal.ofReal (4 * π ^ 2) * (∫⁻ s in Icc 0 T', homNormSq 2 (F s)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have h8 : ENNReal.ofReal (8 * π ^ 2) * (∫⁻ s in Icc 0 T', homNormSq 2 (F s)) =
      ENNReal.ofReal (4 * π ^ 2) * (∫⁻ s in Icc 0 T', homNormSq 2 (F s)) +
        ENNReal.ofReal (4 * π ^ 2) * (∫⁻ s in Icc 0 T', homNormSq 2 (F s)) := by
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 2; ring
  have hXle : ENNReal.ofReal (4 * π ^ 2) * (∫⁻ s in Icc 0 T', homNormSq 2 (F s)) ≤
      ENNReal.ofReal (max M 0) + ENNReal.ofReal ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) *
          ((2 * max C 0 * max M 0 ^ (3 / 4 : ℝ)) / (4 * π ^ 2)) ^ 3) * ENNReal.ofReal T' := by
    refine (ENNReal.add_le_add_iff_right hX).1 ?_
    calc _ = _ := h8.symm
      _ ≤ _ := hmain
      _ = _ := by ring
  have hpi : 0 < 4 * π ^ 2 := by positivity
  rw [ENNReal.ofReal_div_of_pos hpi, ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.2 hpi).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  refine hXle.trans ?_
  rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (le_max_right _ _) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  gcongr
  exact hT'.2

end Breakdown.SmoothFlow
