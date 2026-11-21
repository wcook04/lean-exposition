import Breakdown.FracCert.StatementsSmooth
import Breakdown.Frac.OpIntegrable

open MeasureTheory Set Real Metric
open scoped ENNReal

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace SmoothSupGainInternal

theorem weighted_bound (f : Space → CSpace) (hf : AEMeasurable (fun ξ => ‖f ξ‖ₑ)) (S : Set Space)
    (a : ℝ) :
    ∫⁻ ξ in S, ‖f ξ‖ₑ ≤ (∫⁻ ξ in S, ENNReal.ofReal (‖ξ‖ ^ (-(2 * a)))) ^ (1 / 2 : ℝ) *
      (∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * a)) * ‖f ξ‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  have hne : ∀ᵐ ξ ∂(volume.restrict S), ξ ≠ (0 : Space) := by
    refine ae_restrict_of_ae ?_
    have := (measure_eq_zero_iff_ae_notMem (μ := (volume : Measure Space)) (s := {0})).1
      (measure_singleton 0)
    simpa using this
  have hpt : ∀ᵐ ξ ∂(volume.restrict S), ‖f ξ‖ₑ = ((fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (-a))) *
      (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ a) * ‖f ξ‖ₑ)) ξ := by
    filter_upwards [hne] with ξ hξ
    have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _), ← Real.rpow_add hpos,
      neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  rw [lintegral_congr_ae hpt]
  have hmF : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (-a))) (volume.restrict S) :=
    (measurable_norm.pow_const _).ennreal_ofReal.aemeasurable
  have hmG : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ a) * ‖f ξ‖ₑ)
      (volume.restrict S) :=
    (measurable_norm.pow_const _).ennreal_ofReal.aemeasurable.mul hf.restrict
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hmF hmG).trans ?_
  refine mul_le_mul' (le_of_eq ?_) (ENNReal.rpow_le_rpow ?_ (by norm_num))
  · congr 2
    funext ξ
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by norm_num),
      ← Real.rpow_mul (norm_nonneg _)]
    ring_nf
  · refine (setLIntegral_le_lintegral S _).trans (le_of_eq (lintegral_congr fun ξ => ?_))
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by norm_num),
      ← Real.rpow_mul (norm_nonneg _), ENNReal.rpow_two]
    ring_nf

theorem symbolX_enorm_aemeasurable (x : X) : AEMeasurable (fun ξ => ‖symbolX x ξ‖ₑ) := by
  have h : AEStronglyMeasurable (symbolX x) := by
    unfold symbolX
    exact ((measurable_const.mul measurable_norm).inv.aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable (x : L2C))
  exact h.enorm

end SmoothSupGainInternal

open SmoothSupGainInternal

theorem supFromGain : SupFromGainStatement := by
  intro s hs
  set A := ∫⁻ ξ in ball (0 : Space) 1, ENNReal.ofReal (‖ξ‖ ^ (-(2 * (1 : ℝ))))
  set B := ∫⁻ ξ in (ball (0 : Space) 1)ᶜ, ENNReal.ofReal (‖ξ‖ ^ (-(2 * s)))
  have hA : A ≠ ⊤ :=
    ((FracInternal.integrableOn_ball_norm_rpow (s := -(2 * (1 : ℝ))) (by norm_num)).lintegral_lt_top).ne
  have hB : B ≠ ⊤ :=
    ((FracInternal.integrableOn_compl_ball_norm_rpow (s := -(2 * s)) (by linarith)).lintegral_lt_top).ne
  have hA' : A ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hA
  have hB' : B ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hB
  refine ⟨(A ^ (1 / 2 : ℝ)).toReal + (B ^ (1 / 2 : ℝ)).toReal, fun x _ => ?_⟩
  have hmeas := symbolX_enorm_aemeasurable x
  have h1 := weighted_bound (symbolX x) hmeas (ball 0 1) 1
  have h2 := weighted_bound (symbolX x) hmeas (ball 0 1)ᶜ s
  have hH : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * (1 : ℝ))) * ‖symbolX x ξ‖ₑ ^ 2 =
      homNormSq 1 (symbolX x) := by
    unfold homNormSq
    refine lintegral_congr fun ξ => ?_
    norm_num
  rw [hH] at h1
  have hwA : A ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal ((A ^ (1 / 2 : ℝ)).toReal + (B ^ (1 / 2 : ℝ)).toReal) := by
    exact (ENNReal.ofReal_toReal hA').symm.le.trans
      (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right ENNReal.toReal_nonneg))
  have hwB : B ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal ((A ^ (1 / 2 : ℝ)).toReal + (B ^ (1 / 2 : ℝ)).toReal) := by
    exact (ENNReal.ofReal_toReal hB').symm.le.trans
      (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left ENNReal.toReal_nonneg))
  unfold freqL1Norm
  rw [← lintegral_add_compl _ measurableSet_ball, mul_add]
  refine add_le_add (h1.trans ?_) (h2.trans ?_)
  · exact mul_le_mul' hwA le_rfl
  · exact mul_le_mul' hwB le_rfl

end Breakdown.FracCert
