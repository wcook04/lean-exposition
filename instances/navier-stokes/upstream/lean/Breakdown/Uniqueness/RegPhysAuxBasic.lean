import Breakdown.Uniqueness.RegCurve

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def sspSymbol (f : Space → CSpace) (ξ : Space) : CSpace :=
  -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • f ξ

def gradPressureSymbol (f : Space → CSpace) (ξ : Space) : CSpace :=
  (2 * (π : ℂ) * Complex.I * pressureSymbol f ξ) • freqVec ξ

theorem timeDerivSymbol_add_advectionSymbol (f : Space → CSpace) (ξ : Space) :
    timeDerivSymbol f ξ + advectionSymbol f ξ = sspSymbol f ξ - gradPressureSymbol f ξ := by
  have key : ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ((ξ i : ℝ) : ℂ) * advectionSymbol f ξ i) • freqVec ξ =
      -((2 * (π : ℂ) * Complex.I * pressureSymbol f ξ) • freqVec ξ) := by
    by_cases h : ξ = 0
    · subst h
      simp [freqVec]
    · have hn : (‖ξ‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
      rw [← neg_smul]
      congr 1
      unfold pressureSymbol
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hn' : (((‖ξ‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hn
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      push_cast at hn' ⊢
      field_simp
  simp only [timeDerivSymbol, nonlinSymbol, divFreeC, sspSymbol, gradPressureSymbol]
  rw [key]
  abel

theorem integrable_char_smul {f : Space → CSpace} (hf : Integrable f) (x : Space) :
    Integrable (fun v : Space => 𝐞 (inner ℝ v x) • f v) := by
  refine hf.norm.mono' ?_ (Eventually.of_forall fun v => ?_)
  · exact ((Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const)).aestronglyMeasurable).smul hf.1
  · exact (Circle.norm_smul _ _).le

theorem physField_add {f g : Space → CSpace} (hf : Integrable f) (hg : Integrable g) (x : Space) :
    physField (fun ξ => f ξ + g ξ) x = physField f x + physField g x := by
  simp only [physField, Real.fourierInv_eq, smul_add]
  rw [integral_add (integrable_char_smul hf x) (integrable_char_smul hg x), map_add]

theorem physField_sub {f g : Space → CSpace} (hf : Integrable f) (hg : Integrable g) (x : Space) :
    physField (fun ξ => f ξ - g ξ) x = physField f x - physField g x := by
  simp only [physField, Real.fourierInv_eq, smul_sub]
  rw [integral_sub (integrable_char_smul hf x) (integrable_char_smul hg x), map_sub]

theorem aemeasurable_weight (k : ℕ) :
    AEMeasurable (fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖) ^ k)) volume := by
  fun_prop

theorem volume_ac_weight (k : ℕ) : (volume : Measure Space) ≪ weightL1Measure k := by
  refine withDensity_absolutelyContinuous' (aemeasurable_weight k) (Eventually.of_forall fun ξ => ?_)
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

theorem weight_ac_volume (k : ℕ) : weightL1Measure k ≪ (volume : Measure Space) :=
  withDensity_absolutelyContinuous _ _

theorem lintegral_weight (k : ℕ) {g : Space → ℝ≥0∞} (hg : AEMeasurable g volume) :
    ∫⁻ ξ, g ξ ∂(weightL1Measure k) = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * g ξ := by
  rw [weightL1Measure, lintegral_withDensity_eq_lintegral_mul₀ (aemeasurable_weight k) hg]
  rfl

theorem memLp_weight_iff {f : Space → CSpace} {k : ℕ} (hf : AEStronglyMeasurable f volume) :
    MemLp f 1 (weightL1Measure k) ↔ ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖f ξ‖ₑ < ⊤ := by
  rw [MemLp, eLpNorm_one_eq_lintegral_enorm, lintegral_weight k hf.enorm]
  exact and_iff_right (hf.mono_ac (weight_ac_volume k))

theorem memLp_weight_of_curve {T : ℝ} {F : ℝ → Space → CSpace} (hF : ∀ m, IsHsCurve m F 0 T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (k : ℕ) : MemLp (F t) 1 (weightL1Measure k) := by
  obtain ⟨hm, hs⟩ := (hF (k + 2)).1 t ht
  obtain ⟨C, hC⟩ := weightedFreqL1_le k
  rw [memLp_weight_iff hm]
  refine lt_of_le_of_lt (hC (F t)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hs.ne

theorem integrable_of_memLp_weight {f : Space → CSpace} {k : ℕ} (hf : MemLp f 1 (weightL1Measure k)) :
    Integrable f := by
  have hm : AEStronglyMeasurable f volume := hf.1.mono_ac (volume_ac_weight k)
  refine ⟨hm, ?_⟩
  have h2 := (memLp_weight_iff hm).1 hf
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) h2
  refine le_mul_of_one_le_left bot_le ?_
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  exact one_le_pow₀ (by linarith [norm_nonneg ξ])

end Breakdown.SmoothFlow
