import Breakdown.Uniqueness.RegPersistAuxDefs

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private lemma ennreal_sq_rpow_half (z : ℝ≥0∞) : (z ^ 2) ^ (1 / 2 : ℝ) = z := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private lemma ennreal_rpow_half_sq (z : ℝ≥0∞) : (z ^ (1 / 2 : ℝ)) ^ 2 = z := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private lemma conv_sq_le_pointwise {g h : Space → ℝ≥0∞} (hg : AEMeasurable g volume)
    (hh : AEMeasurable h volume) (ξ : Space) :
    (∫⁻ η, h η * g (ξ - η)) ^ 2 ≤ (∫⁻ η, h η ^ 2 * g (ξ - η)) * ∫⁻ z, g z := by
  have hgs : AEMeasurable (fun η => g (ξ - η)) volume :=
    hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume ξ)
  have key := ENNReal.lintegral_mul_norm_pow_le (μ := volume) ((hh.pow_const 2).mul hgs) hgs
    (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have heq : ∀ η, (h η ^ 2 * g (ξ - η)) ^ (1 / 2 : ℝ) * g (ξ - η) ^ (1 / 2 : ℝ) =
      h η * g (ξ - η) := by
    intro η
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_assoc, ← sq,
      ← mul_pow, ennreal_sq_rpow_half]
  simp only [Pi.mul_apply, heq] at key
  rw [lintegral_sub_left_eq_self g ξ] at key
  calc (∫⁻ η, h η * g (ξ - η)) ^ 2
      ≤ ((∫⁻ η, h η ^ 2 * g (ξ - η)) ^ (1 / 2 : ℝ) * (∫⁻ z, g z) ^ (1 / 2 : ℝ)) ^ 2 := by
        exact pow_le_pow_left₀ zero_le key 2
    _ = _ := by rw [mul_pow, ennreal_rpow_half_sq, ennreal_rpow_half_sq]

private lemma aemeasurable_conv_kernel {g h : Space → ℝ≥0∞} (hg : AEMeasurable g volume)
    (hh : AEMeasurable h volume) :
    AEMeasurable (fun z : Space × Space => h z.2 * g (z.1 - z.2)) (volume.prod volume) :=
  hh.comp_snd.mul (hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume))

private lemma lintegral_conv_right {g h : Space → ℝ≥0∞} (hg : AEMeasurable g volume)
    (hh : AEMeasurable h volume) :
    ∫⁻ ξ, ∫⁻ η, h η * g (ξ - η) = (∫⁻ η, h η) * ∫⁻ z, g z := by
  rw [lintegral_lintegral_swap (aemeasurable_conv_kernel hg hh)]
  have hin : ∀ η, ∫⁻ ξ, h η * g (ξ - η) = h η * ∫⁻ z, g z := by
    intro η
    have hm : AEMeasurable (fun ξ => g (ξ - η)) volume :=
      hg.comp_quasiMeasurePreserving (measurePreserving_sub_right volume η).quasiMeasurePreserving
    rw [lintegral_const_mul'' _ hm, lintegral_sub_right_eq_self g η]
  simp only [hin]
  rw [lintegral_mul_const'' _ hh]

private lemma weighted_conv_base {g v : Space → ℝ≥0∞} (hg : AEMeasurable g volume)
    (hv : Measurable v) {K : ℝ≥0∞} (hK : ∀ ξ η, v ξ ≤ K * (v η + v (ξ - η))) :
    ∫⁻ ξ, v ξ ^ 2 * (∫⁻ η, g η * g (ξ - η)) ^ 2 ≤
      4 * K ^ 2 * (∫⁻ ξ, v ξ ^ 2 * g ξ ^ 2) * (∫⁻ z, g z) ^ 2 := by
  have hvg : AEMeasurable (fun η => v η * g η) volume := hv.aemeasurable.mul hg
  have hpt : ∀ ξ, v ξ * ∫⁻ η, g η * g (ξ - η) ≤ 2 * K * ∫⁻ η, (v η * g η) * g (ξ - η) := by
    intro ξ
    have hgs : AEMeasurable (fun η => g (ξ - η)) volume :=
      hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume ξ)
    have hvs : AEMeasurable (fun η => v (ξ - η)) volume :=
      hv.aemeasurable.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume ξ)
    have hswap : ∫⁻ η, g η * (v (ξ - η) * g (ξ - η)) = ∫⁻ η, (v η * g η) * g (ξ - η) := by
      rw [← lintegral_sub_left_eq_self (fun η => (v η * g η) * g (ξ - η)) ξ]
      congr 1
      ext η
      simp only [sub_sub_cancel]
      ring
    calc v ξ * ∫⁻ η, g η * g (ξ - η) = ∫⁻ η, v ξ * (g η * g (ξ - η)) :=
          (lintegral_const_mul'' _ (hg.mul hgs)).symm
      _ ≤ ∫⁻ η, K * ((v η * g η) * g (ξ - η)) + K * (g η * (v (ξ - η) * g (ξ - η))) := by
          apply lintegral_mono
          intro η
          calc v ξ * (g η * g (ξ - η)) ≤ K * (v η + v (ξ - η)) * (g η * g (ξ - η)) :=
                mul_le_mul_left (hK ξ η) _
            _ = _ := by ring
      _ = K * (∫⁻ η, (v η * g η) * g (ξ - η)) + K * ∫⁻ η, g η * (v (ξ - η) * g (ξ - η)) := by
          have hm1 : AEMeasurable (fun η => K * ((v η * g η) * g (ξ - η))) volume :=
            (hvg.mul hgs).const_mul K
          have hm2 : AEMeasurable (fun η => (v η * g η) * g (ξ - η)) volume := hvg.mul hgs
          have hm3 : AEMeasurable (fun η => g η * (v (ξ - η) * g (ξ - η))) volume :=
            hg.mul (hvs.mul hgs)
          rw [lintegral_add_left' hm1, lintegral_const_mul'' _ hm2, lintegral_const_mul'' _ hm3]
      _ = 2 * K * ∫⁻ η, (v η * g η) * g (ξ - η) := by
          rw [hswap]
          ring
  have hF : AEMeasurable (fun ξ => ∫⁻ η, (v η * g η) ^ 2 * g (ξ - η)) volume :=
    (aemeasurable_conv_kernel hg (hvg.pow_const 2)).lintegral_prod_right'
  calc ∫⁻ ξ, v ξ ^ 2 * (∫⁻ η, g η * g (ξ - η)) ^ 2
      = ∫⁻ ξ, (v ξ * ∫⁻ η, g η * g (ξ - η)) ^ 2 := by simp only [mul_pow]
    _ ≤ ∫⁻ ξ, ((2 * K) ^ 2 * ∫⁻ z, g z) * ∫⁻ η, (v η * g η) ^ 2 * g (ξ - η) := by
        apply lintegral_mono
        intro ξ
        calc (v ξ * ∫⁻ η, g η * g (ξ - η)) ^ 2
            ≤ (2 * K * ∫⁻ η, (v η * g η) * g (ξ - η)) ^ 2 := pow_le_pow_left₀ zero_le (hpt ξ) 2
          _ = (2 * K) ^ 2 * (∫⁻ η, (v η * g η) * g (ξ - η)) ^ 2 := by rw [mul_pow]
          _ ≤ (2 * K) ^ 2 * ((∫⁻ η, (v η * g η) ^ 2 * g (ξ - η)) * ∫⁻ z, g z) := by
              gcongr
              exact conv_sq_le_pointwise hg hvg ξ
          _ = _ := by ring
    _ = ((2 * K) ^ 2 * ∫⁻ z, g z) * ∫⁻ ξ, ∫⁻ η, (v η * g η) ^ 2 * g (ξ - η) :=
        lintegral_const_mul'' _ hF
    _ = 4 * K ^ 2 * (∫⁻ ξ, v ξ ^ 2 * g ξ ^ 2) * (∫⁻ z, g z) ^ 2 := by
        rw [lintegral_conv_right hg (hvg.pow_const 2)]
        simp only [mul_pow]
        ring

private lemma weight_rpow_le {r : ℝ} (hr : 0 ≤ r) (ξ η : Space) :
    (1 + ‖ξ‖ ^ 2) ^ r ≤ 4 ^ r * ((1 + ‖η‖ ^ 2) ^ r + (1 + ‖ξ - η‖ ^ 2) ^ r) := by
  have htri : ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by simpa using norm_add_le η (ξ - η)
  have hsq : ‖ξ‖ ^ 2 ≤ (‖η‖ + ‖ξ - η‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have h2 : 1 + ‖ξ‖ ^ 2 ≤ 2 * (1 + ‖η‖ ^ 2) + 2 * (1 + ‖ξ - η‖ ^ 2) := by
    nlinarith [sq_nonneg (‖η‖ - ‖ξ - η‖)]
  have hA : 0 ≤ 1 + ‖η‖ ^ 2 := by positivity
  have hB : 0 ≤ 1 + ‖ξ - η‖ ^ 2 := by positivity
  have h4 : (0 : ℝ) ≤ 4 ^ r := rpow_nonneg (by norm_num) r
  rcases le_total (1 + ‖η‖ ^ 2) (1 + ‖ξ - η‖ ^ 2) with h | h
  · calc (1 + ‖ξ‖ ^ 2) ^ r ≤ (4 * (1 + ‖ξ - η‖ ^ 2)) ^ r :=
          rpow_le_rpow (by positivity) (by linarith) hr
      _ = 4 ^ r * (1 + ‖ξ - η‖ ^ 2) ^ r := mul_rpow (by norm_num) hB
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (rpow_nonneg hA r)) h4
  · calc (1 + ‖ξ‖ ^ 2) ^ r ≤ (4 * (1 + ‖η‖ ^ 2)) ^ r :=
          rpow_le_rpow (by positivity) (by linarith) hr
      _ = 4 ^ r * (1 + ‖η‖ ^ 2) ^ r := mul_rpow (by norm_num) hA
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (rpow_nonneg hB r)) h4

private lemma weight_root_le {r : ℝ} (hr : 0 ≤ r) (ξ η : Space) :
    ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (4 ^ r) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ r) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal ((1 + ‖ξ - η‖ ^ 2) ^ r) ^ (1 / 2 : ℝ)) := by
  have hle : ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) ≤
      ENNReal.ofReal (4 ^ r) *
        (ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ r) + ENNReal.ofReal ((1 + ‖ξ - η‖ ^ 2) ^ r)) := by
    rw [← ENNReal.ofReal_add (rpow_nonneg (by positivity) r) (rpow_nonneg (by positivity) r),
      ← ENNReal.ofReal_mul (rpow_nonneg (by norm_num) r)]
    exact ENNReal.ofReal_le_ofReal (weight_rpow_le hr ξ η)
  calc ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (4 ^ r) *
          (ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ r) + ENNReal.ofReal ((1 + ‖ξ - η‖ ^ 2) ^ r))) ^
            (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ENNReal.ofReal (4 ^ r) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal ((1 + ‖η‖ ^ 2) ^ r) + ENNReal.ofReal ((1 + ‖ξ - η‖ ^ 2) ^ r)) ^
            (1 / 2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ _ := by
        gcongr
        exact ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)

theorem lintegral_weight_conv_sq_le {r : ℝ} (hr : 0 ≤ r) : ∃ C : ℝ, ∀ f : Space → CSpace,
    AEStronglyMeasurable f volume →
      ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * (∫⁻ η, ‖f η‖ₑ * ‖f (ξ - η)‖ₑ) ^ 2 ≤
        ENNReal.ofReal C * fracNormSq r f * freqL1Norm f ^ 2 := by
  refine ⟨4 * 4 ^ r, fun f hf => ?_⟩
  have hvm : Measurable fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) ^ (1 / 2 : ℝ) :=
    (((measurable_const.add (measurable_norm.pow_const 2)).pow_const r).ennreal_ofReal).pow_const _
  have hbase := weighted_conv_base (g := fun ξ => ‖f ξ‖ₑ) hf.enorm hvm (weight_root_le hr)
  simp only [ennreal_rpow_half_sq] at hbase
  have hC : ENNReal.ofReal (4 * 4 ^ r) = 4 * ENNReal.ofReal (4 ^ r) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [hC]
  exact hbase

end Breakdown.SmoothFlow
