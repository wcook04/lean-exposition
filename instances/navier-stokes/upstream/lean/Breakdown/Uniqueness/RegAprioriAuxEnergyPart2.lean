import Breakdown.Uniqueness.RegToolkit
import Breakdown.Uniqueness.RegPersistAuxNonlin

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private lemma aemeasurable_sub_comp {h : Space → ℝ≥0∞} (hh : AEMeasurable h volume) :
    AEMeasurable (fun p : Space × Space => h (p.1 - p.2)) (volume.prod volume) :=
  hh.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)

private lemma aemeasurable_sub_left_comp {h : Space → ℝ≥0∞} (hh : AEMeasurable h volume) (ξ : Space) :
    AEMeasurable (fun η : Space => h (ξ - η)) volume :=
  hh.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume ξ)

private lemma half_rpow_mul_self (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num

private lemma mul_half_rpow_sq (a x : ℝ≥0∞) : (a * x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a ^ 2 * x := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul]
  norm_num

theorem lintegral_mul_conv_le {v g h : Space → ℝ≥0∞} (hv : AEMeasurable v volume)
    (hg : AEMeasurable g volume) (hh : AEMeasurable h volume) :
    ∫⁻ ξ, v ξ * ∫⁻ η, g η * h (ξ - η) ≤
      (∫⁻ ξ, v ξ ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ) * ∫⁻ ξ, h ξ := by
  have hd := aemeasurable_sub_comp hh
  have hA : AEMeasurable (fun p : Space × Space => v p.1 * h (p.1 - p.2) ^ (1 / 2 : ℝ))
      (volume.prod volume) := hv.comp_fst.mul (hd.pow_const _)
  have hB : AEMeasurable (fun p : Space × Space => g p.2 * h (p.1 - p.2) ^ (1 / 2 : ℝ))
      (volume.prod volume) := hg.comp_snd.mul (hd.pow_const _)
  have e1 : ∫⁻ ξ, v ξ * ∫⁻ η, g η * h (ξ - η) =
      ∫⁻ p : Space × Space, v p.1 * h (p.1 - p.2) ^ (1 / 2 : ℝ) *
        (g p.2 * h (p.1 - p.2) ^ (1 / 2 : ℝ)) ∂(volume.prod volume) := by
    rw [lintegral_prod (fun p : Space × Space => v p.1 * h (p.1 - p.2) ^ (1 / 2 : ℝ) *
        (g p.2 * h (p.1 - p.2) ^ (1 / 2 : ℝ))) (by exact hA.mul hB)]
    refine lintegral_congr fun ξ => ?_
    dsimp only
    rw [← lintegral_const_mul'' (v ξ) (f := fun η => g η * h (ξ - η))
      (by exact hg.mul (aemeasurable_sub_left_comp hh ξ))]
    refine lintegral_congr fun η => ?_
    rw [show v ξ * h (ξ - η) ^ (1 / 2 : ℝ) * (g η * h (ξ - η) ^ (1 / 2 : ℝ)) =
      v ξ * (g η * (h (ξ - η) ^ (1 / 2 : ℝ) * h (ξ - η) ^ (1 / 2 : ℝ))) by ring, half_rpow_mul_self]
  have e2 : ∫⁻ p : Space × Space, (v p.1 * h (p.1 - p.2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂(volume.prod volume) =
      (∫⁻ ξ, v ξ ^ 2) * ∫⁻ ξ, h ξ := by
    simp_rw [mul_half_rpow_sq]
    rw [lintegral_prod (fun p : Space × Space => v p.1 ^ 2 * h (p.1 - p.2))
      (by exact (hv.comp_fst.pow_const 2).mul hd), ← lintegral_mul_const'' _ (hv.pow_const 2)]
    refine lintegral_congr fun ξ => ?_
    dsimp only
    rw [lintegral_const_mul'' _ (aemeasurable_sub_left_comp hh ξ), lintegral_sub_left_eq_self]
  have e3 : ∫⁻ p : Space × Space, (g p.2 * h (p.1 - p.2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂(volume.prod volume) =
      (∫⁻ η, g η ^ 2) * ∫⁻ ξ, h ξ := by
    simp_rw [mul_half_rpow_sq]
    rw [lintegral_prod_symm (fun p : Space × Space => g p.2 ^ 2 * h (p.1 - p.2))
      (by exact (hg.comp_snd.pow_const 2).mul hd), ← lintegral_mul_const'' _ (hg.pow_const 2)]
    refine lintegral_congr fun η => ?_
    dsimp only
    rw [lintegral_const_mul'' _ (f := fun x => h (x - η)) (by exact (hh.comp_quasiMeasurePreserving (measurePreserving_sub_right volume η).quasiMeasurePreserving)),
      lintegral_sub_right_eq_self]
  rw [e1]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hA hB).trans (le_of_eq ?_)
  beta_reduce
  rw [e2, e3, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  calc (∫⁻ ξ, v ξ ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ ξ, h ξ) ^ (1 / 2 : ℝ) *
        ((∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ ξ, h ξ) ^ (1 / 2 : ℝ))
      = (∫⁻ ξ, v ξ ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ η, g η ^ 2) ^ (1 / 2 : ℝ) *
          ((∫⁻ ξ, h ξ) ^ (1 / 2 : ℝ) * (∫⁻ ξ, h ξ) ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [half_rpow_mul_self]

theorem ofReal_norm_mul_lintegral_le {h : Space → ℝ≥0∞} (hh : AEMeasurable h volume) (ξ : Space) :
    ENNReal.ofReal ‖ξ‖ * ∫⁻ η, h η * h (ξ - η) ≤
      2 * ∫⁻ η, ENNReal.ofReal ‖η‖ * h η * h (ξ - η) := by
  have hs := aemeasurable_sub_left_comp hh ξ
  have hm : AEMeasurable (fun η : Space => ENNReal.ofReal ‖η‖ * h η * h (ξ - η)) volume :=
    (continuous_norm.measurable.ennreal_ofReal.aemeasurable.mul hh).mul hs
  calc ENNReal.ofReal ‖ξ‖ * ∫⁻ η, h η * h (ξ - η)
      = ∫⁻ η, ENNReal.ofReal ‖ξ‖ * (h η * h (ξ - η)) := (lintegral_const_mul'' _ (hh.mul hs)).symm
    _ ≤ ∫⁻ η, (ENNReal.ofReal ‖η‖ * h η * h (ξ - η) +
          ENNReal.ofReal ‖ξ - η‖ * h (ξ - η) * h (ξ - (ξ - η))) := by
        refine lintegral_mono fun η => ?_
        rw [sub_sub_cancel]
        calc ENNReal.ofReal ‖ξ‖ * (h η * h (ξ - η))
            ≤ (ENNReal.ofReal ‖η‖ + ENNReal.ofReal ‖ξ - η‖) * (h η * h (ξ - η)) := by
              gcongr
              rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
              exact ENNReal.ofReal_le_ofReal (norm_le_norm_add_norm_sub' ξ η)
          _ = _ := by ring
    _ = (∫⁻ η, ENNReal.ofReal ‖η‖ * h η * h (ξ - η)) +
          ∫⁻ η, ENNReal.ofReal ‖ξ - η‖ * h (ξ - η) * h (ξ - (ξ - η)) := lintegral_add_left' hm _
    _ = 2 * ∫⁻ η, ENNReal.ofReal ‖η‖ * h η * h (ξ - η) := by
        rw [lintegral_sub_left_eq_self (fun η => ENNReal.ofReal ‖η‖ * h η * h (ξ - η)) ξ, two_mul]

private lemma rpow_half_mul_quarter (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (3 / 4 : ℝ) := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num

theorem lintegral_weight_mul_nonlinSymbol_le : ∃ C : ℝ, ∀ f : Space → CSpace,
    AEStronglyMeasurable f volume → IsSolenoidalSymbol f → hsNormSq 3 f < ⊤ →
      ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * (‖f ξ‖ₑ * ‖nonlinSymbol f ξ‖ₑ) ≤
        ENNReal.ofReal C * homNormSq 1 f ^ (3 / 4 : ℝ) * homNormSq 2 f ^ (3 / 4 : ℝ) := by
  obtain ⟨C0, hC0⟩ := enorm_nonlinSymbol_le
  obtain ⟨CA, hCA⟩ := freqL1Norm_le_supBound
  refine ⟨2 * max C0 0 * max CA 0, fun f hf hsol h3 => ?_⟩
  have hh : AEMeasurable (fun η => ‖f η‖ₑ) volume := hf.enorm
  have hv : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖f ξ‖ₑ) volume :=
    (continuous_norm.pow _).measurable.ennreal_ofReal.aemeasurable.mul hh
  have hg : AEMeasurable (fun η : Space => ENNReal.ofReal ‖η‖ * ‖f η‖ₑ) volume :=
    continuous_norm.measurable.ennreal_ofReal.aemeasurable.mul hh
  have hpt : ∀ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * (‖f ξ‖ₑ * ‖nonlinSymbol f ξ‖ₑ) ≤
      ENNReal.ofReal (2 * max C0 0) * ((ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖f ξ‖ₑ) *
        ∫⁻ η, (ENNReal.ofReal ‖η‖ * ‖f η‖ₑ) * ‖f (ξ - η)‖ₑ) := by
    intro ξ
    have h1 := hC0 f hf hsol h3 ξ
    have h2 := ofReal_norm_mul_lintegral_le hh ξ
    have h0 : ENNReal.ofReal (C0 * ‖ξ‖) ≤ ENNReal.ofReal (max C0 0) * ENNReal.ofReal ‖ξ‖ := by
      rw [← ENNReal.ofReal_mul (le_max_right _ _)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    calc ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * (‖f ξ‖ₑ * ‖nonlinSymbol f ξ‖ₑ)
        ≤ ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * (‖f ξ‖ₑ * (ENNReal.ofReal (max C0 0) * ENNReal.ofReal ‖ξ‖ *
            ∫⁻ η, ‖f η‖ₑ * ‖f (ξ - η)‖ₑ)) := by
          gcongr; exact h1.trans (by gcongr)
      _ = ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖f ξ‖ₑ * ENNReal.ofReal (max C0 0) *
            (ENNReal.ofReal ‖ξ‖ * ∫⁻ η, ‖f η‖ₑ * ‖f (ξ - η)‖ₑ) := by ring
      _ ≤ ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖f ξ‖ₑ * ENNReal.ofReal (max C0 0) *
            (2 * ∫⁻ η, ENNReal.ofReal ‖η‖ * ‖f η‖ₑ * ‖f (ξ - η)‖ₑ) := by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring
  have hv2 : ∫⁻ ξ, (ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖f ξ‖ₑ) ^ 2 = homNormSq 2 f := by
    unfold homNormSq
    refine lintegral_congr fun ξ => ?_
    rw [mul_pow, ← ENNReal.ofReal_pow (by positivity), ← pow_mul]
  have hg2 : ∫⁻ η, (ENNReal.ofReal ‖η‖ * ‖f η‖ₑ) ^ 2 = homNormSq 1 f := by
    unfold homNormSq
    refine lintegral_congr fun η => ?_
    rw [mul_pow, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hW := hCA f
  calc ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * (‖f ξ‖ₑ * ‖nonlinSymbol f ξ‖ₑ)
      ≤ ∫⁻ ξ, ENNReal.ofReal (2 * max C0 0) * ((ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖f ξ‖ₑ) *
          ∫⁻ η, (ENNReal.ofReal ‖η‖ * ‖f η‖ₑ) * ‖f (ξ - η)‖ₑ) := lintegral_mono hpt
    _ = ENNReal.ofReal (2 * max C0 0) * ∫⁻ ξ, (ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖f ξ‖ₑ) *
          ∫⁻ η, (ENNReal.ofReal ‖η‖ * ‖f η‖ₑ) * ‖f (ξ - η)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * max C0 0) * (homNormSq 2 f ^ (1 / 2 : ℝ) * homNormSq 1 f ^ (1 / 2 : ℝ) *
          freqL1Norm f) := by
        gcongr
        refine (lintegral_mul_conv_le hv hg hh).trans (le_of_eq ?_)
        rw [hv2, hg2]; rfl
    _ ≤ ENNReal.ofReal (2 * max C0 0) * (homNormSq 2 f ^ (1 / 2 : ℝ) * homNormSq 1 f ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (max CA 0) * homNormSq 1 f ^ (1 / 4 : ℝ) * homNormSq 2 f ^ (1 / 4 : ℝ))) := by
        gcongr
        refine hW.trans ?_
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (2 * max C0 0) * ENNReal.ofReal (max CA 0) *
          (homNormSq 1 f ^ (1 / 2 : ℝ) * homNormSq 1 f ^ (1 / 4 : ℝ)) *
          (homNormSq 2 f ^ (1 / 2 : ℝ) * homNormSq 2 f ^ (1 / 4 : ℝ)) := by ring
    _ = _ := by
        rw [rpow_half_mul_quarter, rpow_half_mul_quarter, ← ENNReal.ofReal_mul (by positivity)]

end Breakdown.SmoothFlow
