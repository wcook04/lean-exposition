import Breakdown.Uniqueness.RegCurveAuxMeasure

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def freqDot (ξ : Space) (z : CSpace) : ℂ := ∑ j, ((ξ j : ℝ) : ℂ) * z j

def pressurePairTerm (ξ : Space) (z w : CSpace) : ℂ :=
  (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (freqDot ξ z * freqDot ξ w)

def pressureBilinSymbol (f g : Space → CSpace) (ξ : Space) : ℂ :=
  -∫ η, pressurePairTerm ξ (f η) (g (ξ - η))

namespace PressureSingle.Internal

theorem freqDot_add (ξ : Space) (z z' : CSpace) : freqDot ξ (z + z') = freqDot ξ z + freqDot ξ z' := by
  simp [freqDot, mul_add, Finset.sum_add_distrib]

theorem freqDot_smul (ξ : Space) (r : ℝ) (z : CSpace) : freqDot ξ (r • z) = (r : ℂ) * freqDot ξ z := by
  simp only [freqDot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.smul_apply, Complex.real_smul]
  ring

theorem pairTerm_add_left (ξ : Space) (z z' w : CSpace) :
    pressurePairTerm ξ (z + z') w = pressurePairTerm ξ z w + pressurePairTerm ξ z' w := by
  simp only [pressurePairTerm, freqDot_add]
  ring

theorem pairTerm_add_right (ξ : Space) (z w w' : CSpace) :
    pressurePairTerm ξ z (w + w') = pressurePairTerm ξ z w + pressurePairTerm ξ z w' := by
  simp only [pressurePairTerm, freqDot_add]
  ring

theorem pairTerm_smul_left (ξ : Space) (r : ℝ) (z w : CSpace) :
    pressurePairTerm ξ (r • z) w = (r : ℂ) * pressurePairTerm ξ z w := by
  simp only [pressurePairTerm, freqDot_smul]
  ring

theorem pairTerm_smul_right (ξ : Space) (r : ℝ) (z w : CSpace) :
    pressurePairTerm ξ z (r • w) = (r : ℂ) * pressurePairTerm ξ z w := by
  simp only [pressurePairTerm, freqDot_smul]
  ring

theorem continuous_pairTerm (ξ : Space) :
    Continuous (Function.uncurry (pressurePairTerm ξ)) := by
  unfold Function.uncurry pressurePairTerm freqDot
  fun_prop

theorem norm_freqDot_le (ξ : Space) (z : CSpace) : ‖freqDot ξ z‖ ≤ 3 * (‖ξ‖ * ‖z‖) := by
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ j ∈ (Finset.univ : Finset (Fin 3)), ‖((ξ j : ℝ) : ℂ) * z j‖ ≤ ‖ξ‖ * ‖z‖ := by
    intro j _
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul (PiLp.norm_apply_le ξ j) (PiLp.norm_apply_le z j) (norm_nonneg _) (norm_nonneg _)
  refine (Finset.sum_le_sum h).trans ?_
  simp

theorem norm_pairTerm_le (ξ : Space) (z w : CSpace) :
    ‖pressurePairTerm ξ z w‖ ≤ 9 * (‖z‖ * ‖w‖) := by
  have hc : 0 ≤ (‖ξ‖ ^ 2)⁻¹ := by positivity
  have h1 : (‖ξ‖ ^ 2)⁻¹ * ‖ξ‖ ^ 2 ≤ 1 := by
    rcases eq_or_ne (‖ξ‖ ^ 2) 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  unfold pressurePairTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  calc (‖ξ‖ ^ 2)⁻¹ * (‖freqDot ξ z‖ * ‖freqDot ξ w‖)
      ≤ (‖ξ‖ ^ 2)⁻¹ * ((3 * (‖ξ‖ * ‖z‖)) * (3 * (‖ξ‖ * ‖w‖))) := by
        gcongr
        · exact norm_freqDot_le ξ z
        · exact norm_freqDot_le ξ w
    _ = 9 * ((‖ξ‖ ^ 2)⁻¹ * ‖ξ‖ ^ 2) * (‖z‖ * ‖w‖) := by ring
    _ ≤ 9 * 1 * (‖z‖ * ‖w‖) := by gcongr
    _ = 9 * (‖z‖ * ‖w‖) := by ring

theorem enorm_pairTerm_le (ξ : Space) (z w : CSpace) :
    ‖pressurePairTerm ξ z w‖ₑ ≤ 9 * (‖z‖ₑ * ‖w‖ₑ) := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _), show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (norm_pairTerm_le ξ z w)

theorem enorm_pressureBilinSymbol_le (f g : Space → CSpace) (ξ : Space) :
    ‖pressureBilinSymbol f g ξ‖ₑ ≤ 9 * ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ := by
  unfold pressureBilinSymbol
  rw [enorm_neg]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ (by simp)]
  exact lintegral_mono fun η => enorm_pairTerm_le ξ (f η) (g (ξ - η))

theorem measurable_conv {a b : Space → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ξ => ∫⁻ η, a η * b (ξ - η)) :=
  Measurable.lintegral_prod_right' (f := fun p : Space × Space => a p.2 * b (p.1 - p.2))
    ((ha.comp measurable_snd).mul (hb.comp (measurable_fst.sub measurable_snd)))

theorem lintegral_conv_measurable {a b : Space → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ ξ, ∫⁻ η, a η * b (ξ - η) = (∫⁻ η, a η) * ∫⁻ η, b η := by
  rw [lintegral_lintegral_swap (f := fun ξ η => a η * b (ξ - η))
    ((ha.comp measurable_snd).mul (hb.comp (measurable_fst.sub measurable_snd))).aemeasurable]
  have e : ∀ η, ∫⁻ ξ, a η * b (ξ - η) = a η * ∫⁻ ξ, b ξ := by
    intro η
    rw [lintegral_const_mul (a η) (f := fun ξ => b (ξ - η)) (hb.comp (measurable_id.sub_const η))]
    congr 1
    exact lintegral_sub_right_eq_self b η
  simp_rw [e]
  exact lintegral_mul_const _ ha

theorem conv_congr_mk {a b : Space → ℝ≥0∞} (ha : AEMeasurable a) (hb : AEMeasurable b) (ξ : Space) :
    ∫⁻ η, a η * b (ξ - η) = ∫⁻ η, ha.mk a η * hb.mk b (ξ - η) := by
  refine lintegral_congr_ae ?_
  have h2 : ∀ᵐ η ∂(volume : Measure Space), b (ξ - η) = hb.mk b (ξ - η) :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume ξ).ae hb.ae_eq_mk
  filter_upwards [ha.ae_eq_mk, h2] with η h1 h2
  rw [h1, h2]

theorem aemeasurable_conv {a b : Space → ℝ≥0∞} (ha : AEMeasurable a) (hb : AEMeasurable b) :
    Measurable (fun ξ => ∫⁻ η, a η * b (ξ - η)) := by
  have : (fun ξ => ∫⁻ η, a η * b (ξ - η)) = fun ξ => ∫⁻ η, ha.mk a η * hb.mk b (ξ - η) :=
    funext (conv_congr_mk ha hb)
  rw [this]
  exact measurable_conv ha.measurable_mk hb.measurable_mk

theorem lintegral_conv {a b : Space → ℝ≥0∞} (ha : AEMeasurable a) (hb : AEMeasurable b) :
    ∫⁻ ξ, ∫⁻ η, a η * b (ξ - η) = (∫⁻ η, a η) * ∫⁻ η, b η := by
  simp_rw [conv_congr_mk ha hb]
  rw [lintegral_conv_measurable ha.measurable_mk hb.measurable_mk, lintegral_congr_ae ha.ae_eq_mk,
    lintegral_congr_ae hb.ae_eq_mk]

theorem weight_le_mul (k : ℕ) (ξ η : Space) :
    ENNReal.ofReal ((1 + ‖ξ‖) ^ k) ≤
      ENNReal.ofReal ((1 + ‖η‖) ^ k) * ENNReal.ofReal ((1 + ‖ξ - η‖) ^ k) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ k)
  have h := norm_add_le η (ξ - η)
  rw [add_sub_cancel] at h
  nlinarith [norm_nonneg η, norm_nonneg (ξ - η)]

theorem measurable_weight (k : ℕ) : Measurable (fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖) ^ k)) :=
  (ENNReal.continuous_ofReal.comp (by fun_prop : Continuous fun ξ : Space => (1 + ‖ξ‖) ^ k)).measurable

theorem lintegral_weight_conv_le (k : ℕ) {a b : Space → ℝ≥0∞} (ha : AEMeasurable a) (hb : AEMeasurable b) :
    ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ∫⁻ η, a η * b (ξ - η) ≤
      (∫⁻ η, ENNReal.ofReal ((1 + ‖η‖) ^ k) * a η) * ∫⁻ η, ENNReal.ofReal ((1 + ‖η‖) ^ k) * b η := by
  rw [← lintegral_conv (a := fun η => ENNReal.ofReal ((1 + ‖η‖) ^ k) * a η)
    (b := fun η => ENNReal.ofReal ((1 + ‖η‖) ^ k) * b η)
    ((measurable_weight k).aemeasurable.mul ha) ((measurable_weight k).aemeasurable.mul hb)]
  refine lintegral_mono fun ξ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun η => ?_
  calc ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * (a η * b (ξ - η))
      ≤ (ENNReal.ofReal ((1 + ‖η‖) ^ k) * ENNReal.ofReal ((1 + ‖ξ - η‖) ^ k)) * (a η * b (ξ - η)) := by
        gcongr
        exact weight_le_mul k ξ η
    _ = ENNReal.ofReal ((1 + ‖η‖) ^ k) * a η * (ENNReal.ofReal ((1 + ‖ξ - η‖) ^ k) * b (ξ - η)) := by ring

theorem volume_ac (k : ℕ) : (volume : Measure Space) ≪ weightedVolume k :=
  withDensity_absolutelyContinuous' (measurable_weight k).aemeasurable
    (Eventually.of_forall fun ξ => (ENNReal.ofReal_pos.mpr (by positivity)).ne')

theorem weighted_ac (k : ℕ) : weightedVolume k ≪ (volume : Measure Space) :=
  withDensity_absolutelyContinuous _ _

theorem lintegral_weighted {k : ℕ} {g : Space → ℝ≥0∞} (hg : AEMeasurable g) :
    ∫⁻ ξ, g ξ ∂weightedVolume k = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * g ξ :=
  lintegral_withDensity_eq_lintegral_mul₀ (measurable_weight k).aemeasurable hg

theorem one_le_weight (k : ℕ) (ξ : Space) : 1 ≤ ENNReal.ofReal ((1 + ‖ξ‖) ^ k) := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith [norm_nonneg ξ]))

theorem aesm_of_memLp {k : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightedVolume k)) :
    AEStronglyMeasurable f volume :=
  hf.1.mono_ac (volume_ac k)

theorem eLpNorm_eq {k : ℕ} {f : Space → CSpace} (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 1 (weightedVolume k) = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖f ξ‖ₑ := by
  rw [eLpNorm_one_eq_lintegral_enorm, lintegral_weighted hf.enorm]

theorem lintegral_enorm_lt_top {k : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightedVolume k)) :
    ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖f ξ‖ₑ < ⊤ := by
  rw [← eLpNorm_eq (aesm_of_memLp hf)]
  exact hf.2

theorem lintegral_enorm_lt_top' {k : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightedVolume k)) :
    ∫⁻ ξ, ‖f ξ‖ₑ < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) (lintegral_enorm_lt_top hf)
  calc ‖f ξ‖ₑ = 1 * ‖f ξ‖ₑ := (one_mul _).symm
    _ ≤ _ := by gcongr; exact one_le_weight k ξ

theorem aesm_shift {g : Space → CSpace} (hg : AEStronglyMeasurable g volume) (ξ : Space) :
    AEStronglyMeasurable (fun η => g (ξ - η)) volume :=
  hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant volume ξ)

theorem integrable_pairTerm {f g : Space → CSpace} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) {ξ : Space} (hξ : ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ < ⊤) :
    Integrable (fun η => pressurePairTerm ξ (f η) (g (ξ - η))) := by
  have hm : AEStronglyMeasurable (fun η => pressurePairTerm ξ (f η) (g (ξ - η))) volume :=
    (continuous_pairTerm ξ).comp_aestronglyMeasurable₂ hf (aesm_shift hg ξ)
  refine ⟨hm, ?_⟩
  show ∫⁻ η, ‖pressurePairTerm ξ (f η) (g (ξ - η))‖ₑ < ⊤
  refine lt_of_le_of_lt (lintegral_mono fun η => enorm_pairTerm_le ξ (f η) (g (ξ - η))) ?_
  rw [lintegral_const_mul' _ _ (by simp)]
  exact ENNReal.mul_lt_top (by simp) hξ

theorem ae_conv_lt_top {k : ℕ} {f g : Space → CSpace} (hf : MemLp f 1 (weightedVolume k))
    (hg : MemLp g 1 (weightedVolume k)) :
    ∀ᵐ ξ ∂(volume : Measure Space), ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ < ⊤ := by
  have ha := (aesm_of_memLp hf).enorm
  have hb := (aesm_of_memLp hg).enorm
  refine ae_lt_top' (aemeasurable_conv ha hb).aemeasurable ?_
  rw [lintegral_conv ha hb]
  exact ENNReal.mul_ne_top (lintegral_enorm_lt_top' hf).ne (lintegral_enorm_lt_top' hg).ne

end PressureSingle.Internal

end Breakdown.SmoothFlow
