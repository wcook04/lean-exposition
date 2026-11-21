import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegPersistAux
import Breakdown.Uniqueness.RegPersistAuxNonlin
import Breakdown.Uniqueness.RegPersistAuxProductBound
import Breakdown.Uniqueness.RegPersistAuxMeas

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

private theorem lintegral_Ioo_sub_rpow_le_of_lt {p : ℝ} (hp : p < 1) {a t : ℝ} (hat : a ≤ t) :
    ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-p)) ≤
      ENNReal.ofReal ((t - a) ^ (1 - p) / (1 - p)) := by
  have hr : (-1 : ℝ) < -p := by linarith
  have hii : IntervalIntegrable (fun s => (t - s) ^ (-p)) volume a t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' hr (a := t - a) (b := 0)).comp_sub_left t
    simpa using h
  have hint : IntegrableOn (fun s => (t - s) ^ (-p)) (Ioc a t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hat).1 hii
  have hval : ∫ s in a..t, (t - s) ^ (-p) = (t - a) ^ (1 - p) / (1 - p) := by
    have h := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ (-p))
      (a := a) (b := t) t
    rw [h, sub_self, integral_rpow (Or.inl hr)]
    have e : -p + 1 = 1 - p := by ring
    rw [e, Real.zero_rpow (by linarith), sub_zero]
  calc ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-p))
      ≤ ∫⁻ s in Ioc a t, ENNReal.ofReal ((t - s) ^ (-p)) :=
        lintegral_mono_set Ioo_subset_Ioc_self
    _ = ENNReal.ofReal (∫ s in Ioc a t, (t - s) ^ (-p)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs =>
          Real.rpow_nonneg (by linarith [hs.2]) _
    _ = ENNReal.ofReal ((t - a) ^ (1 - p) / (1 - p)) := by
        rw [← intervalIntegral.integral_of_le hat, hval]

theorem powerMildGain_of (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) (h1 : PowerHeatGainStatement α)
    (_h2 : PowerHeatPartStatement α) : PowerMildGainStatement α := by
  intro F a b h3 hd hs r hr B hB
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 3 / (8 * α) := ⟨_, rfl⟩
  have hα0 : 0 < α := by linarith
  have he0 : 0 < e := by rw [he]; exact div_pos (by norm_num) (by linarith)
  have hmul : e * (8 * α) = 3 := by rw [he]; field_simp
  have h2e : 2 * e < 1 := by nlinarith [mul_pos (sub_pos.2 hα) he0]
  have h4e : 4 * e = 3 / (2 * α) := by rw [he]; field_simp; ring
  obtain ⟨CN, hCN⟩ := enorm_nonlinSymbol_le
  obtain ⟨CY, hCY⟩ := lintegral_weight_conv_sq_le hr
  obtain ⟨CH, hCH⟩ := h1 (b - a)
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
      (1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) * (τ ^ e * powerHeatSymbol α τ ξ * (C0 * ‖ξ‖)) ^ 2 ≤
        C0 ^ 2 * CH * τ ^ (-(2 * e)) * (1 + ‖ξ‖ ^ 2) ^ r := by
    intro τ hτ hτb ξ
    have h1 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    have hsplit : (1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) = (1 + ‖ξ‖ ^ 2) ^ r * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_add h1 _ _
    have hsq : (τ ^ e) ^ 2 = τ ^ (2 * e) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
      congr 1
      push_cast
      ring
    have hexp : τ ^ (-(2 * e)) = τ ^ (2 * e) * τ ^ (-(3 / (2 * α))) := by
      rw [← Real.rpow_add hτ]
      congr 1
      linarith
    have hnn : 0 ≤ C0 ^ 2 * (1 + ‖ξ‖ ^ 2) ^ r * τ ^ (2 * e) := by positivity
    calc (1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) * (τ ^ e * powerHeatSymbol α τ ξ * (C0 * ‖ξ‖)) ^ 2
        = (C0 ^ 2 * (1 + ‖ξ‖ ^ 2) ^ r * τ ^ (2 * e)) *
            (‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) * powerHeatSymbol α τ ξ ^ 2) := by
          rw [hsplit]
          simp only [mul_pow]
          rw [hsq]
          ring
      _ ≤ (C0 ^ 2 * (1 + ‖ξ‖ ^ 2) ^ r * τ ^ (2 * e)) * (CH * τ ^ (-(3 / (2 * α)))) :=
          mul_le_mul_of_nonneg_left (hCH τ hτ hτb ξ) hnn
      _ = C0 ^ 2 * CH * τ ^ (-(2 * e)) * (1 + ‖ξ‖ ^ 2) ^ r := by
          rw [hexp]
          ring
  have hpt1 : ∀ s ∈ Icc a b, ∀ τ : ℝ, 0 < τ → τ ≤ b - a → ∀ ξ : Space,
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
          (ENNReal.ofReal (τ ^ e) * ENNReal.ofReal (powerHeatSymbol α τ ξ) *
            ‖nonlinSymbol (F s) ξ‖ₑ) ^ 2 ≤
        ENNReal.ofReal (C0 ^ 2 * CH * τ ^ (-(2 * e))) *
          (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * (∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ) ^ 2) := by
    intro s hsm τ hτ hτb ξ
    have hN : ‖nonlinSymbol (F s) ξ‖ₑ ≤
        ENNReal.ofReal (C0 * ‖ξ‖) * ∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ :=
      (hCN (F s) (h3.1 s hsm).1 (hs s hsm) (h3.1 s hsm).2 ξ).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) _)
    have hh0 : 0 ≤ powerHeatSymbol α τ ξ := Real.exp_nonneg _
    have hw0 : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) := by positivity
    have hA0 : 0 ≤ τ ^ e := Real.rpow_nonneg hτ.le _
    have hY2 : 0 ≤ τ ^ e * powerHeatSymbol α τ ξ := mul_nonneg hA0 hh0
    have hY : 0 ≤ τ ^ e * powerHeatSymbol α τ ξ * (C0 * ‖ξ‖) :=
      mul_nonneg hY2 (mul_nonneg hC0 (norm_nonneg _))
    have hE : ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) *
          (τ ^ e * powerHeatSymbol α τ ξ * (C0 * ‖ξ‖)) ^ 2) =
        ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
          (ENNReal.ofReal (τ ^ e) * ENNReal.ofReal (powerHeatSymbol α τ ξ) *
            ENNReal.ofReal (C0 * ‖ξ‖)) ^ 2 := by
      rw [ENNReal.ofReal_mul hw0, ENNReal.ofReal_pow hY, ENNReal.ofReal_mul hY2, ENNReal.ofReal_mul hA0]
    calc _ ≤ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
          (ENNReal.ofReal (τ ^ e) * ENNReal.ofReal (powerHeatSymbol α τ ξ) *
            (ENNReal.ofReal (C0 * ‖ξ‖) * ∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ)) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2) *
            (τ ^ e * powerHeatSymbol α τ ξ * (C0 * ‖ξ‖)) ^ 2) *
            (∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ) ^ 2 := by
          rw [hE]
          ring
      _ ≤ ENNReal.ofReal (C0 ^ 2 * CH * τ ^ (-(2 * e)) * (1 + ‖ξ‖ ^ 2) ^ r) *
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
          (ENNReal.ofReal (τ ^ e) * ENNReal.ofReal (powerHeatSymbol α τ ξ) *
            ‖nonlinSymbol (F s) ξ‖ₑ) ^ 2 ≤
        KK * ENNReal.ofReal (τ ^ (-(2 * e))) := by
    intro s hsm τ hτ hτb
    calc _ ≤ ∫⁻ ξ, ENNReal.ofReal (C0 ^ 2 * CH * τ ^ (-(2 * e))) *
          (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * (∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ) ^ 2) :=
          lintegral_mono fun ξ => hpt1 s hsm τ hτ hτb ξ
      _ = ENNReal.ofReal (C0 ^ 2 * CH * τ ^ (-(2 * e))) *
          ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ r) * (∫⁻ η, ‖F s η‖ₑ * ‖F s (ξ - η)‖ₑ) ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C0 ^ 2 * CH * τ ^ (-(2 * e))) *
          (ENNReal.ofReal CY * ENNReal.ofReal B * (ENNReal.ofReal CW ^ 2 * ENNReal.ofReal B3)) := by
          gcongr
          refine (hCY (F s) (h3.1 s hsm).1).trans ?_
          gcongr
          · exact hB s hsm
          · exact hW s hsm
      _ = KK * ENNReal.ofReal (τ ^ (-(2 * e))) := by
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
  have hhc : Continuous fun p : ℝ × Space => powerHeatSymbol α p.1 p.2 := by
    have hc : Continuous fun x : ℝ => x ^ (2 * α) := Real.continuous_rpow_const (by linarith)
    unfold powerHeatSymbol
    exact Real.continuous_exp.comp
      ((continuous_fst.mul (hc.comp (continuous_const.mul continuous_snd.norm))).neg)
  set KB : ℝ≥0∞ := ENNReal.ofReal ((b - a) ^ (1 - 2 * e) / (1 - 2 * e)) with hKB
  refine ⟨(KB * (KK * KB)).toReal, fun t ht => ?_⟩
  obtain ⟨hat, htb⟩ := ht
  have hsub : Ioo a t ⊆ Icc a b := Ioo_subset_Icc_self.trans (Icc_subset_Icc_right htb)
  have hK2 : ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-(2 * e))) ≤ KB :=
    (lintegral_Ioo_sub_rpow_le_of_lt (by linarith) hat).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
        (by linarith)))
  have hK1 : ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-e)) ^ 2 ≤ KB := by
    refine le_trans (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioo).mono fun s hsm => ?_)) hK2
    have h0 : 0 ≤ t - s := by linarith [hsm.2]
    rw [← ENNReal.ofReal_pow (Real.rpow_nonneg h0 _), ← Real.rpow_natCast, ← Real.rpow_mul h0]
    apply le_of_eq
    congr 2
    push_cast
    ring
  have hK1ne : ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-e)) ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK1
  have hm1 : Measurable fun s : ℝ => ENNReal.ofReal ((t - s) ^ (-e)) :=
    ((measurable_const.sub measurable_id).pow_const _).ennreal_ofReal
  have hm2 : ∀ ξ : Space, Measurable fun s : ℝ => ENNReal.ofReal ((t - s) ^ e) *
      ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * N' (s, ξ) := fun ξ =>
    ((((measurable_const.sub measurable_id).pow_const _).ennreal_ofReal).mul
      (hhc.measurable.comp ((measurable_const.sub measurable_id).prodMk measurable_const)).ennreal_ofReal).mul
      (hN'm.comp (measurable_id.prodMk measurable_const))
  have hmF : Measurable fun p : Space × ℝ => ENNReal.ofReal ((1 + ‖p.1‖ ^ 2) ^ (r + 1 / 2)) *
      (ENNReal.ofReal ((t - p.2) ^ e) * ENNReal.ofReal (powerHeatSymbol α (t - p.2) p.1) *
        N' (p.2, p.1)) ^ 2 :=
    (((measurable_const.add (measurable_fst.norm.pow_const 2)).pow_const _).ennreal_ofReal).mul
      (((((measurable_const.sub measurable_snd).pow_const _).ennreal_ofReal.mul
        (hhc.measurable.comp ((measurable_const.sub measurable_snd).prodMk measurable_fst)).ennreal_ofReal).mul
        (hN'm.comp measurable_swap)).pow_const 2)
  have hpt : ∀ᵐ ξ ∂(volume : Measure Space), ‖(F t - powerHeatPart α a (F a) t) ξ‖ₑ ≤
      ∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-e)) *
        (ENNReal.ofReal ((t - s) ^ e) * ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * N' (s, ξ)) := by
    filter_upwards [hAs] with ξ hξ
    have hrep : (F t - powerHeatPart α a (F a) t) ξ =
        ∫ s in Ioo a t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ := by
      rw [Pi.sub_apply, hd t ⟨hat, htb⟩ ξ, powerHeatPart, add_sub_cancel_left,
        intervalIntegral.integral_of_le hat, integral_Ioc_eq_integral_Ioo]
    rw [hrep]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr_ae ?_))
    have hξ' : ∀ᵐ s ∂(volume.restrict (Ioo a t)), ‖nonlinSymbol (F s) ξ‖ₑ = N' (s, ξ) :=
      ae_restrict_of_ae_restrict_of_subset hsub hξ
    filter_upwards [hξ', ae_restrict_mem measurableSet_Ioo] with s hse hsm
    have hpos : 0 < t - s := by linarith [hsm.2]
    have h1 : ENNReal.ofReal ((t - s) ^ (-e)) * ENNReal.ofReal ((t - s) ^ e) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _), ← Real.rpow_add hpos, neg_add_cancel,
        Real.rpow_zero, ENNReal.ofReal_one]
    have h2 : ‖((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) := by
      have hh : 0 ≤ powerHeatSymbol α (t - s) ξ := Real.exp_nonneg _
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hh]
    rw [enorm_smul, hse, h2, ← mul_assoc, ← mul_assoc, h1, one_mul]
  have hCst : ∀ ξ : Space, (∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-e)) *
        (ENNReal.ofReal ((t - s) ^ e) * ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * N' (s, ξ))) ^ 2 ≤
      (∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-e)) ^ 2) *
        ∫⁻ s in Ioo a t, (ENNReal.ofReal ((t - s) ^ e) *
          ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * N' (s, ξ)) ^ 2 := fun ξ =>
    lintegral_mul_sq_le_of_aemeasurable hm1.aemeasurable (hm2 ξ).aemeasurable
  have hstep : ∫⁻ s in Ioo a t, ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
        (ENNReal.ofReal ((t - s) ^ e) * ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * N' (s, ξ)) ^ 2 ≤
      ∫⁻ s in Ioo a t, KK * ENNReal.ofReal ((t - s) ^ (-(2 * e))) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hA, ae_restrict_mem measurableSet_Ioo]
      with s hsA hsm
    calc _ = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
          (ENNReal.ofReal ((t - s) ^ e) * ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) *
            ‖nonlinSymbol (F s) ξ‖ₑ) ^ 2 :=
          lintegral_congr_ae (hsA.mono fun ξ h => by simp only [h])
      _ ≤ _ := hper s (hsub hsm) (t - s) (by linarith [hsm.2]) (by linarith [hsm.1])
  have hmain : fracNormSq (r + 1 / 2) (F t - powerHeatPart α a (F a) t) ≤ KB * (KK * KB) := by
    calc fracNormSq (r + 1 / 2) (F t - powerHeatPart α a (F a) t)
        ≤ ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
            ((∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-e)) ^ 2) *
              ∫⁻ s in Ioo a t, (ENNReal.ofReal ((t - s) ^ e) *
                ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * N' (s, ξ)) ^ 2) := by
          unfold fracNormSq
          refine lintegral_mono_ae (hpt.mono fun ξ hξ => ?_)
          exact mul_le_mul_right ((pow_le_pow_left₀ (by positivity) hξ 2).trans (hCst ξ)) _
      _ = (∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-e)) ^ 2) *
            ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
              ∫⁻ s in Ioo a t, (ENNReal.ofReal ((t - s) ^ e) *
                ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * N' (s, ξ)) ^ 2 := by
          rw [← lintegral_const_mul' _ _ hK1ne]
          exact lintegral_congr fun ξ => mul_left_comm _ _ _
      _ = (∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-e)) ^ 2) *
            ∫⁻ ξ, ∫⁻ s in Ioo a t, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
              (ENNReal.ofReal ((t - s) ^ e) *
                ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * N' (s, ξ)) ^ 2 := by
          congr 1
          exact lintegral_congr fun ξ => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = (∫⁻ s in Ioo a t, ENNReal.ofReal ((t - s) ^ (-e)) ^ 2) *
            ∫⁻ s in Ioo a t, ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (r + 1 / 2)) *
              (ENNReal.ofReal ((t - s) ^ e) *
                ENNReal.ofReal (powerHeatSymbol α (t - s) ξ) * N' (s, ξ)) ^ 2 := by
          rw [lintegral_lintegral_swap hmF.aemeasurable]
      _ ≤ KB * ∫⁻ s in Ioo a t, KK * ENNReal.ofReal ((t - s) ^ (-(2 * e))) :=
          mul_le_mul' hK1 hstep
      _ ≤ KB * (KK * KB) := by
          rw [lintegral_const_mul' _ _ hKKne]
          gcongr
  have hne : KB * (KK * KB) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hKKne ENNReal.ofReal_ne_top)
  rw [ENNReal.ofReal_toReal hne]
  exact hmain

end Breakdown.SmoothFlow
