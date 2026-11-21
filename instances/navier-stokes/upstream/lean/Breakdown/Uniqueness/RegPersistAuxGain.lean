import Breakdown.Uniqueness.RegPersistAux
import Breakdown.Uniqueness.RegPersistAuxNonlin
import Breakdown.Uniqueness.RegPersistAuxProductBound
import Breakdown.Uniqueness.RegPersistAuxMeas
import Breakdown.Uniqueness.RegPersistAuxHeat

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem lintegral_mul_sq_le_of_aemeasurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * ∫⁻ x, g x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ x, f x * g x ∂μ) ^ 2
      ≤ ((∫⁻ x, f x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ x, g x ^ 2 ∂μ) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ = (∫⁻ x, f x ^ 2 ∂μ) * ∫⁻ x, g x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast ((∫⁻ x, g x ^ 2 ∂μ) ^ (1 / (2 : ℝ))),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

private theorem lintegral_Ioo_sub_rpow_le {a t : ℝ} (hat : a ≤ t) :
    ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 4) : ℝ)) ≤
      ENNReal.ofReal (4 * (t - a) ^ (1 / 4 : ℝ)) := by
  have hr : (-1 : ℝ) < -(3 / 4) := by norm_num
  have hii : IntervalIntegrable (fun s => (t - s) ^ (-(3 / 4) : ℝ)) volume a t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' hr (a := t - a) (b := 0)).comp_sub_left t
    simpa using h
  have hint : IntegrableOn (fun s => (t - s) ^ (-(3 / 4) : ℝ)) (Ioc a t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hat).1 hii
  have hval : ∫ s in a..t, (t - s) ^ (-(3 / 4) : ℝ) = 4 * (t - a) ^ (1 / 4 : ℝ) := by
    have h := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ (-(3 / 4) : ℝ))
      (a := a) (b := t) t
    rw [h, sub_self, integral_rpow (Or.inl hr)]
    have e : (-(3 / 4 : ℝ)) + 1 = 1 / 4 := by norm_num
    rw [e, Real.zero_rpow (by norm_num)]
    ring
  calc ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 4) : ℝ))
      ≤ ∫⁻ s in Ioc a t, ENNReal.ofReal ((t - s) ^ (-(3 / 4) : ℝ)) :=
        lintegral_mono_set Ioo_subset_Ioc_self
    _ = ENNReal.ofReal (∫ s in Ioc a t, (t - s) ^ (-(3 / 4) : ℝ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs =>
          Real.rpow_nonneg (by linarith [hs.2]) _
    _ = ENNReal.ofReal (4 * (t - a) ^ (1 / 4 : ℝ)) := by
        rw [← intervalIntegral.integral_of_le hat, hval]

theorem fracNormSq_varConst_gain {F : ℝ → Space → CSpace} {a b : ℝ} (h3 : IsHsCurve 3 F a b)
    (hd : IsVarConstSymbol F a b) (hs : ∀ t ∈ Icc a b, IsSolenoidalSymbol (F t)) {r : ℝ} (hr : 0 ≤ r)
    {B : ℝ} (hB : ∀ s ∈ Icc a b, fracNormSq r (F s) ≤ ENNReal.ofReal B) :
    ∃ B' : ℝ, ∀ t ∈ Icc a b, fracNormSq (r + 1 / 2) (F t - heatPart a (F a) t) ≤ ENNReal.ofReal B' := by
  obtain ⟨CN, hCN⟩ := enorm_nonlinSymbol_le
  obtain ⟨CY, hCY⟩ := lintegral_weight_conv_sq_le hr
  obtain ⟨CH, hCH⟩ := heatSymbol_gain_le (b - a)
  obtain ⟨CW, hCW⟩ := freqL1Norm_le_hsNormSq
  obtain ⟨B3, hB3⟩ := hsNormSq_bdd_of_curve h3
  set C0 : ℝ := max CN 0 with hC0def
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hW : ∀ s ∈ Icc a b, freqL1Norm (F s) ^ 2 ≤ ENNReal.ofReal CW ^ 2 * ENNReal.ofReal B3 := by
    intro s hsm
    have h23 : hsNormSq 2 (F s) ≤ hsNormSq 3 (F s) := by
      rw [← fracNormSq_natCast, ← fracNormSq_natCast]
      exact fracNormSq_mono (by norm_num) _
    calc freqL1Norm (F s) ^ 2 ≤ (ENNReal.ofReal CW * hsNormSq 2 (F s) ^ (1 / 2 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (hCW _) 2
      _ = ENNReal.ofReal CW ^ 2 * hsNormSq 2 (F s) := by
          rw [mul_pow, ← ENNReal.rpow_natCast (hsNormSq 2 (F s) ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul]
          norm_num
      _ ≤ ENNReal.ofReal CW ^ 2 * ENNReal.ofReal B3 := by
          gcongr
          exact h23.trans (hB3 s hsm)
  have hreal : ∀ τ : ℝ, 0 < τ → τ ≤ b - a → ∀ ξ : Space,
      (1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) * (τ ^ (3 / 8 : ℝ) * heatSymbol τ ξ * (C0 * ‖ξ‖)) ^ 2 ≤
        C0 ^ 2 * CH * τ ^ (-(3 / 4) : ℝ) * (1 + ‖ξ‖ ^ 2) ^ r := by
    intro τ hτ hτb ξ
    have h1 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    have hsplit : (1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) = (1 + ‖ξ‖ ^ 2) ^ r * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_add h1 _ _
    have hsq : (τ ^ (3 / 8 : ℝ)) ^ 2 = τ ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
      norm_num
    have hexp : τ ^ (-(3 / 4) : ℝ) = τ ^ (3 / 4 : ℝ) * τ ^ (-(3 / 2) : ℝ) := by
      rw [← Real.rpow_add hτ]
      norm_num
    have hnn : 0 ≤ C0 ^ 2 * (1 + ‖ξ‖ ^ 2) ^ r * τ ^ (3 / 4 : ℝ) := by positivity
    calc (1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) * (τ ^ (3 / 8 : ℝ) * heatSymbol τ ξ * (C0 * ‖ξ‖)) ^ 2
        = (C0 ^ 2 * (1 + ‖ξ‖ ^ 2) ^ r * τ ^ (3 / 4 : ℝ)) *
            (‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) * heatSymbol τ ξ ^ 2) := by
          rw [hsplit]
          simp only [mul_pow]
          rw [hsq]
          ring
      _ ≤ (C0 ^ 2 * (1 + ‖ξ‖ ^ 2) ^ r * τ ^ (3 / 4 : ℝ)) * (CH * τ ^ (-(3 / 2) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hCH τ hτ hτb ξ) hnn
      _ = C0 ^ 2 * CH * τ ^ (-(3 / 4) : ℝ) * (1 + ‖ξ‖ ^ 2) ^ r := by
          rw [hexp]
          ring
  have hpt1 : ∀ s ∈ Icc a b, ∀ τ : ℝ, 0 < τ → τ ≤ b - a → ∀ ξ : Space,
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
          (ENNReal.ofReal (τ ^ (3 / 8 : ℝ)) * ENNReal.ofReal (heatSymbol τ ξ) *
            ‖nonlinSymbol (F s) ξ‖ₑ) ^ 2 ≤
        ENNReal.ofReal (C0 ^ 2 * CH * τ ^ (-(3 / 4) : ℝ)) *
          (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * (∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ) ^ 2) := by
    intro s hsm τ hτ hτb ξ
    have hN : ‖nonlinSymbol (F s) ξ‖ₑ ≤
        ENNReal.ofReal (C0 * ‖ξ‖) * ∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ :=
      (hCN (F s) (h3.1 s hsm).1 (hs s hsm) (h3.1 s hsm).2 ξ).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) _)
    have hh0 : 0 ≤ heatSymbol τ ξ := Real.exp_nonneg _
    have hw0 : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) := by positivity
    have hA0 : 0 ≤ τ ^ (3 / 8 : ℝ) := Real.rpow_nonneg hτ.le _
    have hY2 : 0 ≤ τ ^ (3 / 8 : ℝ) * heatSymbol τ ξ := mul_nonneg hA0 hh0
    have hY : 0 ≤ τ ^ (3 / 8 : ℝ) * heatSymbol τ ξ * (C0 * ‖ξ‖) :=
      mul_nonneg hY2 (mul_nonneg hC0 (norm_nonneg _))
    have e : ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) *
          (τ ^ (3 / 8 : ℝ) * heatSymbol τ ξ * (C0 * ‖ξ‖)) ^ 2) =
        ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
          (ENNReal.ofReal (τ ^ (3 / 8 : ℝ)) * ENNReal.ofReal (heatSymbol τ ξ) *
            ENNReal.ofReal (C0 * ‖ξ‖)) ^ 2 := by
      rw [ENNReal.ofReal_mul hw0, ENNReal.ofReal_pow hY, ENNReal.ofReal_mul hY2, ENNReal.ofReal_mul hA0]
    calc _ ≤ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
          (ENNReal.ofReal (τ ^ (3 / 8 : ℝ)) * ENNReal.ofReal (heatSymbol τ ξ) *
            (ENNReal.ofReal (C0 * ‖ξ‖) * ∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ)) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) *
            (τ ^ (3 / 8 : ℝ) * heatSymbol τ ξ * (C0 * ‖ξ‖)) ^ 2) *
            (∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ) ^ 2 := by
          rw [e]
          ring
      _ ≤ ENNReal.ofReal (C0 ^ 2 * CH * τ ^ (-(3 / 4) : ℝ) * (1 + ‖ξ‖ ^ 2) ^ r) *
            (∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ) ^ 2 := by
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hreal τ hτ hτb ξ)) _
      _ = _ := by
          rw [ENNReal.ofReal_mul' (by positivity)]
          ring
  set KK : ℝ≥0∞ := ENNReal.ofReal (C0 ^ 2 * CH) *
    (ENNReal.ofReal CY * ENNReal.ofReal B * (ENNReal.ofReal CW ^ 2 * ENNReal.ofReal B3)) with hKK
  have hKKne : KK ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top))
  have hper : ∀ s ∈ Icc a b, ∀ τ : ℝ, 0 < τ → τ ≤ b - a →
      ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
          (ENNReal.ofReal (τ ^ (3 / 8 : ℝ)) * ENNReal.ofReal (heatSymbol τ ξ) *
            ‖nonlinSymbol (F s) ξ‖ₑ) ^ 2 ≤
        KK * ENNReal.ofReal (τ ^ (-(3 / 4) : ℝ)) := by
    intro s hsm τ hτ hτb
    calc _ ≤ ∫⁻ ξ, ENNReal.ofReal (C0 ^ 2 * CH * τ ^ (-(3 / 4) : ℝ)) *
          (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * (∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ) ^ 2) :=
          lintegral_mono fun ξ => hpt1 s hsm τ hτ hτb ξ
      _ = ENNReal.ofReal (C0 ^ 2 * CH * τ ^ (-(3 / 4) : ℝ)) *
          ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * (∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ) ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C0 ^ 2 * CH * τ ^ (-(3 / 4) : ℝ)) *
          (ENNReal.ofReal CY * ENNReal.ofReal B * (ENNReal.ofReal CW ^ 2 * ENNReal.ofReal B3)) := by
          gcongr
          refine (hCY (F s) (h3.1 s hsm).1).trans ?_
          gcongr
          · exact hB s hsm
          · exact hW s hsm
      _ = KK * ENNReal.ofReal (τ ^ (-(3 / 4) : ℝ)) := by
          rw [hKK, ENNReal.ofReal_mul' (Real.rpow_nonneg hτ.le _)]
          ring
  have hM := aemeasurable_enorm_nonlinSymbol h3 hs
  obtain ⟨N', hN'm, hae⟩ := hM
  have hA : ∀ᵐ s ∂(volume.restrict (Icc a b)), ∀ᵐ ξ ∂(volume : Measure Space),
      ‖nonlinSymbol (F s) ξ‖ₑ = N' (s, ξ) :=
    Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => ‖nonlinSymbol (F z.1) z.2‖ₑ = N' z) hae
  have hAs : ∀ᵐ ξ ∂(volume : Measure Space), ∀ᵐ s ∂(volume.restrict (Icc a b)),
      ‖nonlinSymbol (F s) ξ‖ₑ = N' (s, ξ) := by
    have h := (Measure.measurePreserving_swap (μ := (volume : Measure Space))
      (ν := volume.restrict (Icc a b))).quasiMeasurePreserving.ae
      (p := fun z : ℝ × Space => ‖nonlinSymbol (F z.1) z.2‖ₑ = N' z) hae
    exact Measure.ae_ae_of_ae_prod
      (p := fun z : Space × ℝ => ‖nonlinSymbol (F z.2) z.1‖ₑ = N' (z.2, z.1)) h
  have hhc : Continuous fun p : ℝ × Space => heatSymbol p.1 p.2 := by
    unfold heatSymbol
    fun_prop
  set KB : ℝ≥0∞ := ENNReal.ofReal (4 * (b - a) ^ (1 / 4 : ℝ)) with hKB
  refine ⟨(KB * (KK * KB)).toReal, fun t ht => ?_⟩
  obtain ⟨hat, htb⟩ := ht
  have hsub : Ioo a t ⊆ Icc a b := Ioo_subset_Icc_self.trans (Icc_subset_Icc_right htb)
  have hK2 : ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 4) : ℝ)) ≤ KB :=
    (lintegral_Ioo_sub_rpow_le hat).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
        (by norm_num)))
  have hK1 : ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) ^ 2 ≤ KB := by
    refine le_trans (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioo).mono fun s hsm => ?_)) hK2
    have h0 : 0 ≤ t - s := by linarith [hsm.2]
    rw [← ENNReal.ofReal_pow (Real.rpow_nonneg h0 _), ← Real.rpow_natCast, ← Real.rpow_mul h0]
    norm_num
  have hK1ne : ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK1
  have hm1 : Measurable fun s : ℝ => ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) :=
    ((measurable_const.sub measurable_id).pow_const _).ennreal_ofReal
  have hm2 : ∀ ξ : Space, Measurable fun s : ℝ => ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) *
      ENNReal.ofReal (heatSymbol (t - s) ξ) * N' (s, ξ) := fun ξ =>
    ((((measurable_const.sub measurable_id).pow_const _).ennreal_ofReal).mul
      (hhc.measurable.comp ((measurable_const.sub measurable_id).prodMk measurable_const)).ennreal_ofReal).mul
      (hN'm.comp (measurable_id.prodMk measurable_const))
  have hmF : Measurable fun p : Space × ℝ => ENNReal.ofReal ((1 + ‖p.1‖ ^ 2) ^ (r + 1 / 2)) *
      (ENNReal.ofReal ((t - p.2) ^ (3 / 8 : ℝ)) * ENNReal.ofReal (heatSymbol (t - p.2) p.1) *
        N' (p.2, p.1)) ^ 2 :=
    (((measurable_const.add (measurable_fst.norm.pow_const 2)).pow_const _).ennreal_ofReal).mul
      (((((measurable_const.sub measurable_snd).pow_const _).ennreal_ofReal.mul
        (hhc.measurable.comp ((measurable_const.sub measurable_snd).prodMk measurable_fst)).ennreal_ofReal).mul
        (hN'm.comp measurable_swap)).pow_const 2)
  have hpt : ∀ᵐ ξ ∂(volume : Measure Space), ‖(F t - heatPart a (F a) t) ξ‖ₑ ≤
      ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) *
        (ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) * ENNReal.ofReal (heatSymbol (t - s) ξ) * N' (s, ξ)) := by
    filter_upwards [hAs] with ξ hξ
    have hrep : (F t - heatPart a (F a) t) ξ =
        ∫ s in Ioo a t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ := by
      rw [Pi.sub_apply, hd t ⟨hat, htb⟩ ξ, heatPart, add_sub_cancel_left,
        intervalIntegral.integral_of_le hat, integral_Ioc_eq_integral_Ioo]
    rw [hrep]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr_ae ?_))
    have hξ' : ∀ᵐ s ∂(volume.restrict (Ioo a t)), ‖nonlinSymbol (F s) ξ‖ₑ = N' (s, ξ) :=
      ae_restrict_of_ae_restrict_of_subset hsub hξ
    filter_upwards [hξ', ae_restrict_mem measurableSet_Ioo] with s hse hsm
    have hpos : 0 < t - s := by linarith [hsm.2]
    have h1 : ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) * ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _), ← Real.rpow_add hpos]
      norm_num
    have h2 : ‖((heatSymbol (t - s) ξ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (heatSymbol (t - s) ξ) := by
      have hh : 0 ≤ heatSymbol (t - s) ξ := Real.exp_nonneg _
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hh]
    rw [enorm_smul, hse, h2, ← mul_assoc, ← mul_assoc, h1, one_mul]
  have hCst : ∀ ξ : Space, (∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) *
        (ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) * ENNReal.ofReal (heatSymbol (t - s) ξ) * N' (s, ξ))) ^ 2 ≤
      (∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) ^ 2) *
        ∫⁻ s in Ioo a t, (ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) *
          ENNReal.ofReal (heatSymbol (t - s) ξ) * N' (s, ξ)) ^ 2 := fun ξ =>
    lintegral_mul_sq_le_of_aemeasurable hm1.aemeasurable (hm2 ξ).aemeasurable
  have hstep : ∫⁻ s in Ioo a t, ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
        (ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) * ENNReal.ofReal (heatSymbol (t - s) ξ) * N' (s, ξ)) ^ 2 ≤
      ∫⁻ s in Ioo a t, KK * ENNReal.ofReal ((t - s) ^ (-(3 / 4) : ℝ)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hA, ae_restrict_mem measurableSet_Ioo]
      with s hsA hsm
    calc _ = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
          (ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) * ENNReal.ofReal (heatSymbol (t - s) ξ) *
            ‖nonlinSymbol (F s) ξ‖ₑ) ^ 2 :=
          lintegral_congr_ae (hsA.mono fun ξ h => by simp only [h])
      _ ≤ _ := hper s (hsub hsm) (t - s) (by linarith [hsm.2]) (by linarith [hsm.1])
  have hmain : fracNormSq (r + 1 / 2) (F t - heatPart a (F a) t) ≤ KB * (KK * KB) := by
    calc fracNormSq (r + 1 / 2) (F t - heatPart a (F a) t)
        ≤ ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
            ((∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) ^ 2) *
              ∫⁻ s in Ioo a t, (ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) *
                ENNReal.ofReal (heatSymbol (t - s) ξ) * N' (s, ξ)) ^ 2) := by
          unfold fracNormSq
          refine lintegral_mono_ae (hpt.mono fun ξ hξ => ?_)
          exact mul_le_mul_right ((pow_le_pow_left₀ (by positivity) hξ 2).trans (hCst ξ)) _
      _ = (∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) ^ 2) *
            ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
              ∫⁻ s in Ioo a t, (ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) *
                ENNReal.ofReal (heatSymbol (t - s) ξ) * N' (s, ξ)) ^ 2 := by
          rw [← lintegral_const_mul' _ _ hK1ne]
          exact lintegral_congr fun ξ => mul_left_comm _ _ _
      _ = (∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) ^ 2) *
            ∫⁻ ξ, ∫⁻ s in Ioo a t, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
              (ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) *
                ENNReal.ofReal (heatSymbol (t - s) ξ) * N' (s, ξ)) ^ 2 := by
          congr 1
          exact lintegral_congr fun ξ => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = (∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(3 / 8) : ℝ)) ^ 2) *
            ∫⁻ s in Ioo a t, ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
              (ENNReal.ofReal ((t - s) ^ (3 / 8 : ℝ)) *
                ENNReal.ofReal (heatSymbol (t - s) ξ) * N' (s, ξ)) ^ 2 := by
          rw [lintegral_lintegral_swap hmF.aemeasurable]
      _ ≤ KB * ∫⁻ s in Ioo a t, KK * ENNReal.ofReal ((t - s) ^ (-(3 / 4) : ℝ)) :=
          mul_le_mul' hK1 hstep
      _ ≤ KB * (KK * KB) := by
          rw [lintegral_const_mul' _ _ hKKne]
          gcongr
  have hne : KB * (KK * KB) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hKKne ENNReal.ofReal_ne_top)
  rw [ENNReal.ofReal_toReal hne]
  exact hmain

end Breakdown.SmoothFlow
