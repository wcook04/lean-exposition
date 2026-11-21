import Breakdown.CertTorus.BilinSymbol
import Breakdown.Uniqueness.RegPhysAuxPressure
import Breakdown.Uniqueness.RegPhysAuxDeriv
import Breakdown.Uniqueness.RegEmbedAux

open MeasureTheory Set Real Filter
open scoped ENNReal FourierTransform

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.PressureGradYoung

theorem sq_lintegral_mul_le (a c : Space → ℝ≥0∞) (ha : AEMeasurable a) (hc : AEMeasurable c) :
    (∫⁻ η, a η * c η) ^ 2 ≤ (∫⁻ η, a η) * ∫⁻ η, a η * c η ^ 2 := by
  have hg : AEMeasurable (fun η => a η * c η ^ 2) := ha.mul (hc.pow_const 2)
  have h : ∫⁻ η, a η ^ (1 / 2 : ℝ) * (a η * c η ^ 2) ^ (1 / 2 : ℝ) ≤
      (∫⁻ η, a η) ^ (1 / 2 : ℝ) * (∫⁻ η, a η * c η ^ 2) ^ (1 / 2 : ℝ) :=
    ENNReal.lintegral_mul_norm_pow_le ha hg (by norm_num) (by norm_num) (by norm_num)
  have k1 : ∀ z : ℝ≥0∞, (z ^ 2) ^ (1 / 2 : ℝ) = z := by
    intro z
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have k2 : ∀ z : ℝ≥0∞, (z ^ (1 / 2 : ℝ)) ^ 2 = z := by
    intro z
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have e : ∀ η, a η ^ (1 / 2 : ℝ) * (a η * c η ^ 2) ^ (1 / 2 : ℝ) = a η * c η := by
    intro η
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc,
      ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← sq, k1, k1]
  simp_rw [e] at h
  calc (∫⁻ η, a η * c η) ^ 2
      ≤ ((∫⁻ η, a η) ^ (1 / 2 : ℝ) * (∫⁻ η, a η * c η ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ η, a η) * ∫⁻ η, a η * c η ^ 2 := by rw [mul_pow, k2, k2]

theorem lintegral_conv_sq_le (a b : Space → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ ξ, (∫⁻ η, a η * b (ξ - η)) ^ 2 ≤ (∫⁻ η, a η) ^ 2 * ∫⁻ ζ, b ζ ^ 2 := by
  have hm : Measurable (Function.uncurry fun ξ η : Space => a η * b (ξ - η) ^ 2) :=
    (ha.comp measurable_snd).mul ((hb.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  calc ∫⁻ ξ, (∫⁻ η, a η * b (ξ - η)) ^ 2
      ≤ ∫⁻ ξ, (∫⁻ η, a η) * ∫⁻ η, a η * b (ξ - η) ^ 2 :=
        lintegral_mono fun ξ => sq_lintegral_mul_le a _ ha.aemeasurable
          (hb.comp (measurable_const.sub measurable_id)).aemeasurable
    _ = (∫⁻ η, a η) * ∫⁻ ξ, ∫⁻ η, a η * b (ξ - η) ^ 2 :=
        lintegral_const_mul _ hm.lintegral_prod_right'
    _ = (∫⁻ η, a η) * ∫⁻ η, ∫⁻ ξ, a η * b (ξ - η) ^ 2 := by
        rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = (∫⁻ η, a η) * ∫⁻ η, a η * ∫⁻ ζ, b ζ ^ 2 := by
        congr 1
        refine lintegral_congr fun η => ?_
        have hs : Measurable fun ξ : Space => b (ξ - η) ^ 2 :=
          (hb.comp (measurable_id.sub measurable_const)).pow_const 2
        rw [lintegral_const_mul _ hs]
        rw [lintegral_sub_right_eq_self (fun ζ => b ζ ^ 2) η]
    _ = (∫⁻ η, a η) ^ 2 * ∫⁻ ζ, b ζ ^ 2 := by
        rw [lintegral_mul_const _ ha]
        ring

theorem norm_le_sum_coord (z : CSpace) : ‖z‖ ≤ ∑ i, ‖z i‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg (z 0), norm_nonneg (z 1), norm_nonneg (z 2)]

theorem norm_fderiv_le_gradientAt (p : Space → ℝ) (y : Space) :
    ‖fderiv ℝ p y‖ ≤ 3 * ‖gradientAt p y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = ∑ i, v i • unitVector i := by
    ext j
    rw [SmoothFlow.Internal.sum_smul_unitVector_apply]
  have hg : ∀ i, fderiv ℝ p y (unitVector i) = gradientAt p y i := by
    intro i
    unfold gradientAt
    rw [SmoothFlow.Internal.sum_smul_unitVector_apply]
  rw [hv, map_sum]
  calc ‖∑ i, fderiv ℝ p y (v i • unitVector i)‖
      ≤ ∑ i, ‖fderiv ℝ p y (v i • unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖gradientAt p y‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [map_smul, hg, norm_smul, mul_comm]
        exact mul_le_mul (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _) (norm_nonneg _)
          (norm_nonneg _)
    _ = 3 * ‖gradientAt p y‖ * ‖∑ i, v i • unitVector i‖ := by
        rw [← hv]
        simp
        ring


theorem enorm_le_sum_coord (z : CSpace) : ‖z‖ₑ ≤ ∑ i, ‖z i‖ₑ := by
  simp_rw [← ofReal_norm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_le_sum_coord z)

theorem advectionSymbol_apply (f : Space → CSpace) (ξ : Space) (i : Fin 3) :
    advectionSymbol f ξ i = ∑ j, ∫ η, f η j *
      (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i) := rfl

theorem norm_conv_term_le (f g : Space → CSpace) (ξ η : Space) (i j : Fin 3)
    (h : 2 * π * ‖ξ - η‖ * ‖f (ξ - η)‖ ≤ ‖g (ξ - η)‖) :
    ‖f η j * (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i)‖ ≤
      ‖f η‖ * ‖g (ξ - η)‖ := by
  have h1 : ‖f η j‖ ≤ ‖f η‖ := PiLp.norm_apply_le _ _
  have h2 : ‖f (ξ - η) i‖ ≤ ‖f (ξ - η)‖ := PiLp.norm_apply_le _ _
  have h3 : |(ξ - η) j| ≤ ‖ξ - η‖ := by
    have := PiLp.norm_apply_le (ξ - η) j
    rwa [Real.norm_eq_abs] at this
  have e : ‖2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i‖ =
      2 * π * |(ξ - η) j| * ‖f (ξ - η) i‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos pi_pos]
    norm_num
  rw [norm_mul, e]
  calc ‖f η j‖ * (2 * π * |(ξ - η) j| * ‖f (ξ - η) i‖)
      ≤ ‖f η‖ * (2 * π * ‖ξ - η‖ * ‖f (ξ - η)‖) := by
        have := pi_pos
        gcongr
    _ ≤ ‖f η‖ * ‖g (ξ - η)‖ := mul_le_mul_of_nonneg_left h (norm_nonneg _)

theorem enorm_advectionSymbol_le (f g : Space → CSpace)
    (hfg : ∀ᵐ ζ ∂(volume : Measure Space), 2 * π * ‖ζ‖ * ‖f ζ‖ ≤ ‖g ζ‖) (ξ : Space) :
    ‖advectionSymbol f ξ‖ₑ ≤ 9 * ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ := by
  have hae : ∀ᵐ η ∂(volume : Measure Space), 2 * π * ‖ξ - η‖ * ‖f (ξ - η)‖ ≤ ‖g (ξ - η)‖ :=
    (Measure.measurePreserving_sub_left volume ξ).quasiMeasurePreserving.ae hfg
  have hi : ∀ i j : Fin 3, ‖∫ η, f η j *
      (2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i)‖ₑ ≤
        ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ := by
    intro i j
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
    filter_upwards [hae] with η hη
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_conv_term_le f g ξ η i j hη)
  calc ‖advectionSymbol f ξ‖ₑ ≤ ∑ i, ‖advectionSymbol f ξ i‖ₑ := enorm_le_sum_coord _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [advectionSymbol_apply]
        exact (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hi i j)
    _ = 9 * ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc]
        norm_num

theorem lintegral_enorm_sq_lt_top {g : Space → CSpace} (hg : MemLp g 2 volume) :
    ∫⁻ ζ, ‖g ζ‖ₑ ^ 2 < ⊤ := by
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).1 hg.2
  simpa using h

theorem memLp_two_advectionSymbol (f g : Space → CSpace) (hf : Integrable f)
    (hg : MemLp g 2 volume)
    (hfg : ∀ᵐ ζ ∂(volume : Measure Space), 2 * π * ‖ζ‖ * ‖f ζ‖ ≤ ‖g ζ‖)
    (hA : AEStronglyMeasurable (advectionSymbol f) volume) :
    MemLp (advectionSymbol f) 2 volume := by
  refine ⟨hA, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  set a : Space → ℝ≥0∞ := fun η => ‖hf.aestronglyMeasurable.mk f η‖ₑ with ha_def
  set b : Space → ℝ≥0∞ := fun ζ => ‖hg.1.mk g ζ‖ₑ with hb_def
  have ha : Measurable a := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable.enorm
  have hb : Measurable b := hg.1.stronglyMeasurable_mk.measurable.enorm
  have hconv : ∀ ξ, ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ = ∫⁻ η, a η * b (ξ - η) := by
    intro ξ
    refine lintegral_congr_ae ?_
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk,
      (Measure.measurePreserving_sub_left volume ξ).quasiMeasurePreserving.ae hg.1.ae_eq_mk] with η h1 h2
    rw [ha_def, hb_def]
    dsimp only
    rw [h1, h2]
  have hle : ∀ ξ, ‖advectionSymbol f ξ‖ₑ ^ 2 ≤ 81 * (∫⁻ η, a η * b (ξ - η)) ^ 2 := by
    intro ξ
    calc ‖advectionSymbol f ξ‖ₑ ^ 2 ≤ (9 * ∫⁻ η, a η * b (ξ - η)) ^ 2 := by
          rw [← hconv]
          gcongr
          exact enorm_advectionSymbol_le f g hfg ξ
      _ = 81 * (∫⁻ η, a η * b (ξ - η)) ^ 2 := by
          rw [mul_pow]
          norm_num
  have hia : ∫⁻ η, a η < ⊤ := by
    refine (lintegral_congr_ae ?_).trans_lt hf.hasFiniteIntegral
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with η h
    rw [ha_def]
    dsimp only
    rw [h]
  have hib : ∫⁻ ζ, b ζ ^ 2 < ⊤ := by
    refine (lintegral_congr_ae ?_).trans_lt (lintegral_enorm_sq_lt_top hg)
    filter_upwards [hg.1.ae_eq_mk] with η h
    rw [hb_def]
    dsimp only
    rw [h]
  calc ∫⁻ ξ, ‖advectionSymbol f ξ‖ₑ ^ 2 ≤ ∫⁻ ξ, 81 * (∫⁻ η, a η * b (ξ - η)) ^ 2 :=
        lintegral_mono hle
    _ = 81 * ∫⁻ ξ, (∫⁻ η, a η * b (ξ - η)) ^ 2 := lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 81 * ((∫⁻ η, a η) ^ 2 * ∫⁻ ζ, b ζ ^ 2) := by
        gcongr
        exact lintegral_conv_sq_le a b ha hb
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top (ENNReal.pow_lt_top hia) hib)

theorem norm_grad_pressureSymbol_le (f : Space → CSpace) (ξ : Space) :
    ‖(2 * (π : ℂ) * Complex.I * pressureSymbol f ξ) • freqVec ξ‖ ≤ ‖advectionSymbol f ξ‖ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [SmoothFlow.Internal.RegIdentifyDivFree.freqVec_zero]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hs : ‖∑ i, ((ξ i : ℝ) : ℂ) * advectionSymbol f ξ i‖ ≤ ‖ξ‖ * ‖advectionSymbol f ξ‖ := by
    rw [← SmoothFlow.Internal.RegIdentifyDivFree.inner_freqVec_eq]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [SmoothFlow.Internal.RegIdentifyDivFree.norm_freqVec_eq]
  have h1 : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    simp [pi_ne_zero, Complex.I_ne_zero]
  have h2 : (((‖ξ‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (‖ξ‖ ^ 2 : ℝ) ≠ 0)
  have e : 2 * (π : ℂ) * Complex.I * pressureSymbol f ξ =
      -(∑ i, ((ξ i : ℝ) : ℂ) * advectionSymbol f ξ i) / (((‖ξ‖ ^ 2 : ℝ)) : ℂ) := by
    unfold pressureSymbol
    field_simp
  rw [norm_smul, e, norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    SmoothFlow.Internal.RegIdentifyDivFree.norm_freqVec_eq]
  calc ‖∑ i, ((ξ i : ℝ) : ℂ) * advectionSymbol f ξ i‖ / ‖ξ‖ ^ 2 * ‖ξ‖
      ≤ ‖ξ‖ * ‖advectionSymbol f ξ‖ / ‖ξ‖ ^ 2 * ‖ξ‖ := by gcongr
    _ = ‖advectionSymbol f ξ‖ := by field_simp

end Internal.PressureGradYoung

open Internal.PressureGradYoung Internal.BilinSymbolOfVelocity in
theorem pressureGradL2OfWiener_holds : PressureGradL2OfWiener := by
  intro hW x hx
  have hf : ∀ k, MemLp (velSymbol x) 1 (weightL1Measure k) := memLp_weight_velSymbol hW hx
  have hsol := isSolenoidal_velSymbol x
  have hfi : Integrable (velSymbol x) := integrable_of_memLp_weight (hf 0)
  have hg : MemLp (symX x) 2 volume := Lp.memLp (x : L2C)
  have hfg : ∀ᵐ ζ ∂(volume : Measure Space),
      2 * π * ‖ζ‖ * ‖velSymbol x ζ‖ ≤ ‖symX x ζ‖ := by
    filter_upwards [smul_velSymbol_ae x] with ζ h
    rw [← h, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hAm : AEStronglyMeasurable (advectionSymbol (velSymbol x)) volume :=
    (integrable_of_memLp_weight (memLp_advectionSymbol hf 0)).1
  have hA2 := memLp_two_advectionSymbol (velSymbol x) (symX x) hfi hg hfg hAm
  have hp0 := memLp_pressureSymbol_single hf hsol 0
  have hp1 := memLp_pressureSymbol_single hf hsol 1
  have hpi : Integrable (pressureSymbol (velSymbol x)) := by
    have := (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).integrable_comp
      (integrable_of_memLp_weight hp0)
    simpa using this
  have hfm : AEStronglyMeasurable (fun ξ : Space => freqVec ξ) volume :=
    complexifyVec.continuous.aestronglyMeasurable
  have hpv : Integrable (fun ξ => pressureSymbol (velSymbol x) ξ • freqVec ξ) := by
    have h1 := SmoothFlow.Internal.integrable_pow_mul_of_weight hp1 (le_refl 1)
    refine h1.mono' (hpi.1.smul hfm) (Eventually.of_forall fun ξ => ?_)
    rw [norm_smul, norm_smul, SmoothFlow.Internal.RegIdentifyDivFree.norm_freqVec_eq,
      PiLp.norm_single, norm_one, mul_one, pow_one, mul_comm]
  have hVi : Integrable (fun ξ => (2 * (π : ℂ) * Complex.I * pressureSymbol (velSymbol x) ξ) •
      freqVec ξ) :=
    (hpv.smul (2 * (π : ℂ) * Complex.I)).congr
      (Eventually.of_forall fun ξ => by simp only [Pi.smul_apply, smul_smul])
  have hV2 : MemLp (fun ξ => (2 * (π : ℂ) * Complex.I * pressureSymbol (velSymbol x) ξ) •
      freqVec ξ) 2 volume :=
    hA2.of_le_mul (c := 1) hVi.1 (Eventually.of_forall fun ξ => by
      rw [one_mul]
      exact norm_grad_pressureSymbol_le _ ξ)
  have hphys := SmoothFlow.Internal.RegEmbed.memLp_realVec_freqTrInv hVi hV2
  refine hphys.of_le_mul (c := 3) (measurable_fderiv ℝ _).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hgr := gradientAt_physScalar hpi hpv y
  refine (norm_fderiv_le_gradientAt _ y).trans ?_
  rw [hgr]
  rfl

end Breakdown.FarField
