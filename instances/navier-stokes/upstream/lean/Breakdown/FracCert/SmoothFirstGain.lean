import Breakdown.FracCert.StatementsSmooth
import Breakdown.Frac.RExports
import Breakdown.Frac.TorusHeatCompareInverse

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.FracCert.SmoothFirstGain.Internal

open Breakdown.Freq Breakdown.SmoothFlow

def gainWeight (α : ℝ) (ξ : Space) : ℝ := ‖ξ‖ ^ (2 * α - 1)

def gainNormSq (α : ℝ) (f : Space → CSpace) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (gainWeight α ξ) * ‖f ξ‖ₑ ^ 2

theorem lintegral_enorm_sq (f : L2C) :
    ∫⁻ ξ, ‖(f : Space → CSpace) ξ‖ₑ ^ 2 = ENNReal.ofReal (‖f‖ ^ 2) := by
  have hE : eLpNorm (f : Space → CSpace) 2 volume ≠ ⊤ := Lp.eLpNorm_ne_top f
  rw [Lp.norm_def, ← ENNReal.toReal_pow, ENNReal.ofReal_toReal (ENNReal.pow_ne_top hE),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem fracHomSq_le (α : ℝ) (x : X) :
    fracHomSq (α + 1 / 2) x ≤ ENNReal.ofReal ((2 * π)⁻¹ ^ 2) * gainNormSq α (x : L2C) := by
  rw [fracHomSq, gainNormSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ξ => ?_
  rw [symbolX, enorm_smul]
  rcases eq_or_lt_of_le (norm_nonneg ξ) with h0 | hpos
  · rw [← h0]
    simp
  · have hc : 0 ≤ (2 * π * ‖ξ‖)⁻¹ := by positivity
    rw [Real.enorm_eq_ofReal hc]
    refine le_of_eq ?_
    conv_lhs => rw [mul_pow, ← ENNReal.ofReal_pow hc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    conv_rhs => rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    have e1 : ‖ξ‖ ^ (2 * (α + 1 / 2)) = ‖ξ‖ ^ (2 * α - 1) * ‖ξ‖ ^ 2 := by
      rw [show 2 * (α + 1 / 2) = (2 * α - 1) + 2 by ring, Real.rpow_add hpos, Real.rpow_two]
    rw [e1, gainWeight]
    have hpi : 0 < π := Real.pi_pos
    field_simp

theorem heat_weight_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    gainWeight α ξ * fracHeatFactor α τ ξ ^ 2 ≤ τ ^ (-((2 * α - 1) / (2 * α))) := by
  set a := 2 * π * ‖ξ‖ with ha
  have ha0 : 0 ≤ a := by positivity
  set p := (2 * α - 1) / (2 * α) with hp
  have hp0 : 0 < p := by rw [hp]; apply div_pos <;> linarith
  have hp1 : p ≤ 1 := by rw [hp, div_le_one (by linarith)]; linarith
  have h1 : ‖ξ‖ ^ (2 * α - 1) ≤ a ^ (2 * α - 1) := by
    apply Real.rpow_le_rpow (norm_nonneg _) _ (by linarith)
    rw [ha]
    have : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
    nlinarith [norm_nonneg ξ]
  set q := τ * a ^ (2 * α) with hq
  have hq0 : 0 ≤ q := by positivity
  have h2 : a ^ (2 * α - 1) = τ ^ (-p) * q ^ p := by
    rw [hq, Real.mul_rpow hτ.le (Real.rpow_nonneg ha0 _), ← Real.rpow_mul ha0, ← mul_assoc,
      ← Real.rpow_add hτ, neg_add_cancel, Real.rpow_zero, one_mul]
    congr 1
    rw [hp]
    field_simp
  have h3 : q ^ p ≤ 1 + q := by
    rcases le_total q 1 with hq1 | hq1
    · have := Real.rpow_le_one hq0 hq1 hp0.le
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le hq1 hp1
      rw [Real.rpow_one] at this
      linarith
  have h4 : fracHeatFactor α τ ξ = Real.exp (-q) := by
    rw [fracHeatFactor, max_eq_left hτ.le]
  have h5 : q ^ p * Real.exp (-q) ^ 2 ≤ 1 := by
    have e1 : 1 + q ≤ Real.exp q := by linarith [Real.add_one_le_exp q]
    have e2 : Real.exp (-q) ^ 2 ≤ Real.exp (-q) * Real.exp (-q) := le_of_eq (sq _)
    have e3 : Real.exp (-q) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc q ^ p * Real.exp (-q) ^ 2 ≤ Real.exp q * (Real.exp (-q) * 1) := by
          apply mul_le_mul (h3.trans e1) _ (by positivity) (Real.exp_pos _).le
          rw [sq]
          exact mul_le_mul_of_nonneg_left e3 (Real.exp_pos _).le
      _ = 1 := by rw [mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have htp : 0 ≤ τ ^ (-p) := Real.rpow_nonneg hτ.le _
  rw [gainWeight, h4]
  calc ‖ξ‖ ^ (2 * α - 1) * Real.exp (-q) ^ 2 ≤ a ^ (2 * α - 1) * Real.exp (-q) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = τ ^ (-p) * (q ^ p * Real.exp (-q) ^ 2) := by rw [h2]; ring
    _ ≤ τ ^ (-p) * 1 := mul_le_mul_of_nonneg_left h5 htp
    _ = τ ^ (-p) := mul_one _

theorem heat_gain {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (y : X) :
    gainNormSq α ((fracHeatX α τ y : X) : L2C) ≤
      ENNReal.ofReal (τ ^ (-((2 * α - 1) / (2 * α)))) * ENNReal.ofReal (‖y‖ ^ 2) := by
  have hc : ((fracHeatX α τ y : X) : L2C) = fracHeatL2 α τ (y : L2C) :=
    (fracHeatSemigroup α).2.2.2.2.2 τ y
  have hae := Breakdown.Periodic.FracHeatCompareInverse.Internal.fracHeat_ae
    (by linarith : (0 : ℝ) < α) τ (y : L2C)
  have hn : ‖y‖ = ‖(y : L2C)‖ := rfl
  rw [hn, ← lintegral_enorm_sq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, gainNormSq, hc]
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with ξ hξ
  have hf0 : 0 ≤ fracHeatFactor α τ ξ := (Real.exp_pos _).le
  rw [hξ, enorm_smul, Real.enorm_eq_ofReal hf0, mul_pow, ← ENNReal.ofReal_pow hf0, ← mul_assoc,
    ← ENNReal.ofReal_mul (by rw [gainWeight]; positivity)]
  gcongr
  exact heat_weight_le hα hτ ξ

theorem gainWeight_continuous {α : ℝ} (hα : 1 < α) : Continuous (gainWeight α) :=
  continuous_norm.rpow_const fun _ => Or.inr (by linarith)

def cutMul (α : ℝ) (N : ℕ) (ξ : Space) : CSpace →L[ℝ] CSpace :=
  Real.sqrt (min (gainWeight α ξ) N) • ContinuousLinearMap.id ℝ CSpace

def cutOp (α : ℝ) (N : ℕ) : L2C →L[ℝ] L2C := fieldOp id (cutMul α N)

theorem cutOp_ae {α : ℝ} (hα : 1 < α) (N : ℕ) (f : L2C) :
    ∀ᵐ ξ ∂volume, (cutOp α N f : Space → CSpace) ξ =
      Real.sqrt (min (gainWeight α ξ) N) • (f : Space → CSpace) ξ := by
  have hm : AEStronglyMeasurable (cutMul α N) volume :=
    ((((gainWeight_continuous hα).min continuous_const).sqrt).smul continuous_const).aestronglyMeasurable
  have hb : ∀ ξ, ‖cutMul α N ξ‖ ≤ Real.sqrt N := by
    intro ξ
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (min (gainWeight α ξ) N) * ‖ContinuousLinearMap.id ℝ CSpace‖
        ≤ Real.sqrt N * 1 :=
          mul_le_mul (Real.sqrt_le_sqrt (min_le_right _ _)) ContinuousLinearMap.norm_id_le
            (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt N := mul_one _
  have h := fieldOp_ae (ContinuousLinearEquiv.refl ℝ Space) (A := id) rfl hm hb f
  filter_upwards [h] with ξ hξ
  rw [cutOp, hξ]
  rfl

theorem cutOp_sq {α : ℝ} (hα : 1 < α) (N : ℕ) (f : L2C) :
    ENNReal.ofReal (‖cutOp α N f‖ ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal (min (gainWeight α ξ) N) * ‖(f : Space → CSpace) ξ‖ₑ ^ 2 := by
  rw [← lintegral_enorm_sq]
  refine lintegral_congr_ae ?_
  filter_upwards [cutOp_ae hα N f] with ξ hξ
  have hm : 0 ≤ min (gainWeight α ξ) N :=
    le_min (by rw [gainWeight]; positivity) (Nat.cast_nonneg _)
  rw [hξ, enorm_smul, Real.enorm_eq_ofReal (Real.sqrt_nonneg _), mul_pow,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hm]

theorem cutOp_le {α : ℝ} (hα : 1 < α) (N : ℕ) (f : L2C) :
    ENNReal.ofReal (‖cutOp α N f‖ ^ 2) ≤ gainNormSq α f := by
  rw [cutOp_sq hα, gainNormSq]
  refine lintegral_mono fun ξ => ?_
  gcongr
  exact min_le_left _ _

theorem gainNormSq_le_iSup {α : ℝ} (hα : 1 < α) (f : L2C) :
    gainNormSq α f ≤ ⨆ N : ℕ, ENNReal.ofReal (‖cutOp α N f‖ ^ 2) := by
  simp_rw [cutOp_sq hα]
  rw [← lintegral_iSup']
  · refine lintegral_mono fun ξ => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (gainWeight α ξ)
    refine le_iSup_of_le N ?_
    rw [min_eq_left hN]
  · intro N
    exact (ENNReal.measurable_ofReal.comp
      ((gainWeight_continuous hα).min continuous_const).measurable).aemeasurable.mul
      ((Lp.aestronglyMeasurable f).enorm.pow_const 2)
  · refine Filter.Eventually.of_forall fun ξ => ?_
    intro m n hmn
    simp only
    gcongr

theorem cutOp_norm_le {α : ℝ} (hα : 1 < α) (N : ℕ) {f : L2C} {B : ℝ} (hB : 0 ≤ B)
    (h : gainNormSq α f ≤ ENNReal.ofReal B) : ‖cutOp α N f‖ ≤ Real.sqrt B := by
  have h1 := (cutOp_le hα N f).trans h
  rw [ENNReal.ofReal_le_ofReal_iff hB] at h1
  exact (le_abs_self _).trans (Real.abs_le_sqrt h1)

theorem bilin_gain {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ, 0 < τ → ∀ u v : X, ‖fracBilinX α τ u v‖ ≤ C * τ ^ (-(3 / (4 * α))) * ‖u‖ * ‖v‖)
    (u : X) {M : ℝ} (hu : ‖u‖ ≤ M) :
    gainNormSq α ((fracBilinX α τ u u : X) : L2C) ≤
      ENNReal.ofReal ((τ / 2) ^ (-((2 * α - 1) / (2 * α))) *
        (C * (τ / 2) ^ (-(3 / (4 * α))) * M * M) ^ 2) := by
  have h2 : (0 : ℝ) < τ / 2 := by linarith
  have hsh := fracBilinShift α (fracBilin_holds α hα).1 (fracHeatSemigroup α) (τ / 2) (τ / 2)
    h2.le h2 u u
  rw [add_halves] at hsh
  rw [← hsh]
  refine (heat_gain hα h2 _).trans ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg h2.le _)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg h2.le _))
  have hk := hC (τ / 2) h2 u u
  have hu0 := norm_nonneg u
  have hk2 : C * (τ / 2) ^ (-(3 / (4 * α))) * ‖u‖ * ‖u‖ ≤ C * (τ / 2) ^ (-(3 / (4 * α))) * M * M := by
    have hC1 : 0 ≤ C * (τ / 2) ^ (-(3 / (4 * α))) := mul_nonneg hC0 (Real.rpow_nonneg h2.le _)
    have := mul_le_mul hu hu hu0 (hu0.trans hu)
    rw [mul_assoc, mul_assoc (C * _)]
    exact mul_le_mul_of_nonneg_left this hC1
  exact pow_le_pow_left₀ (norm_nonneg _) (hk.trans hk2) 2

theorem half_rpow_neg {τ e : ℝ} (hτ : 0 ≤ τ) : (τ / 2) ^ (-e) = 2 ^ e * τ ^ (-e) := by
  rw [Real.div_rpow hτ zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul, mul_comm]

theorem bilin_cut {α : ℝ} (hα : 1 < α) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ, 0 < τ → ∀ u v : X, ‖fracBilinX α τ u v‖ ≤ C * τ ^ (-(3 / (4 * α))) * ‖u‖ * ‖v‖)
    (N : ℕ) {τ : ℝ} (hpos : 0 < τ) (u : X) {M : ℝ} (hM : 0 ≤ M) (hu : ‖u‖ ≤ M) :
    ‖cutOp α N ((fracBilinX α τ u u : X) : L2C)‖ ≤
      C * M * M * 2 ^ ((α + 1) / (2 * α)) * τ ^ (-((α + 1) / (2 * α))) := by
  have hτ : 0 ≤ τ := hpos.le
  · have h2 : (0 : ℝ) < τ / 2 := by linarith
    have hb := bilin_gain hα hpos hC0 hC u hu
    have hB0 : 0 ≤ (τ / 2) ^ (-((2 * α - 1) / (2 * α))) *
        (C * (τ / 2) ^ (-(3 / (4 * α))) * M * M) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg h2.le _) (sq_nonneg _)
    refine (cutOp_norm_le hα N hB0 hb).trans (le_of_eq ?_)
    have hb0 : 0 ≤ C * (τ / 2) ^ (-(3 / (4 * α))) * M * M :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg h2.le _)) hM) hM
    rw [Real.sqrt_mul (Real.rpow_nonneg h2.le _), Real.sqrt_sq hb0, Real.sqrt_eq_rpow,
      ← Real.rpow_mul h2.le]
    have hexp : (τ / 2) ^ (-((2 * α - 1) / (2 * α)) * (1 / 2)) * (τ / 2) ^ (-(3 / (4 * α))) =
        (τ / 2) ^ (-((α + 1) / (2 * α))) := by
      rw [← Real.rpow_add h2]
      congr 1
      have hα0 : α ≠ 0 := by linarith
      field_simp
      ring
    calc (τ / 2) ^ (-((2 * α - 1) / (2 * α)) * (1 / 2)) * (C * (τ / 2) ^ (-(3 / (4 * α))) * M * M)
        = C * M * M * ((τ / 2) ^ (-((2 * α - 1) / (2 * α)) * (1 / 2)) * (τ / 2) ^ (-(3 / (4 * α)))) := by
          ring
      _ = C * M * M * (2 ^ ((α + 1) / (2 * α)) * τ ^ (-((α + 1) / (2 * α)))) := by
          rw [hexp, half_rpow_neg hτ]
      _ = _ := by ring

theorem sub_rpow_integral {s e : ℝ} (he : e < 1) :
    IntervalIntegrable (fun r => (s - r) ^ (-e)) volume 0 s ∧
      ∫ r in (0 : ℝ)..s, (s - r) ^ (-e) = s ^ (1 - e) / (1 - e) := by
  have h1 : -1 < -e := by linarith
  constructor
  · have := (intervalIntegral.intervalIntegrable_rpow' (a := s) (b := 0) h1).comp_sub_left s
    simpa using this
  · rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ (-e)) s, sub_self, sub_zero,
      integral_rpow (Or.inl h1), Real.zero_rpow (by linarith), sub_zero]
    congr 1 <;> ring_nf

theorem cut_bound {α : ℝ} (hα : 1 < α) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ, 0 < τ → ∀ u v : X, ‖fracBilinX α τ u v‖ ≤ C * τ ^ (-(3 / (4 * α))) * ‖u‖ * ‖v‖)
    (u : ℝ → X) {σ s t M : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (hst : s ≤ t) (hMnn : 0 ≤ M)
    (hM : ∀ r ∈ Icc 0 t, ‖u r‖ ≤ M)
    (hint : IntervalIntegrable (fun r => fracBilinX α (s - r) (u r) (u r)) volume 0 s)
    (heq : u s = fracHeatX α s (u 0) + ∫ r in (0 : ℝ)..s, fracBilinX α (s - r) (u r) (u r))
    (N : ℕ) :
    ‖cutOp α N (u s : L2C)‖ ≤ Real.sqrt (σ ^ (-((2 * α - 1) / (2 * α))) * ‖u 0‖ ^ 2) +
      C * M * M * 2 ^ ((α + 1) / (2 * α)) * (t ^ (1 - (α + 1) / (2 * α)) / (1 - (α + 1) / (2 * α))) := by
  have hs0 : 0 < s := hσ.trans_le hσs
  have he1 : (α + 1) / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hp0 : 0 ≤ (2 * α - 1) / (2 * α) := by apply div_nonneg <;> linarith
  have hD : 0 ≤ C * M * M * 2 ^ ((α + 1) / (2 * α)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 hMnn) hMnn) (Real.rpow_nonneg zero_le_two _)
  rw [heq, Submodule.coe_add, map_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have hB : 0 ≤ s ^ (-((2 * α - 1) / (2 * α))) * ‖u 0‖ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hs0.le _) (sq_nonneg _)
    have h1 := cutOp_norm_le hα N hB
      (by rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _)]; exact heat_gain hα hs0 (u 0))
    refine h1.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
    exact Real.rpow_le_rpow_of_nonpos hσ hσs (by linarith)
  · have hcomm := ((cutOp α N).comp (Sig.subtypeL)).intervalIntegral_comp_comm hint
    have hcoe : ((∫ r in (0 : ℝ)..s, fracBilinX α (s - r) (u r) (u r) : X) : L2C) =
        (Sig.subtypeL) (∫ r in (0 : ℝ)..s, fracBilinX α (s - r) (u r) (u r)) := rfl
    rw [hcoe, ← ContinuousLinearMap.comp_apply, ← hcomm]
    obtain ⟨hI, hval⟩ := sub_rpow_integral he1
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ s := by
      rw [ae_iff]
      simp
    refine (intervalIntegral.norm_integral_le_of_norm_le hs0.le
      (g := fun r => C * M * M * 2 ^ ((α + 1) / (2 * α)) * (s - r) ^ (-((α + 1) / (2 * α))))
      ?_ (hI.const_mul (C * M * M * 2 ^ ((α + 1) / (2 * α))))).trans ?_
    · filter_upwards [hne] with r hrs hr
      exact bilin_cut hα hC0 hC N (by rcases hr with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 hrs))
        (u r) hMnn (hM r ⟨hr.1.le, hr.2.trans hst⟩)
    · rw [intervalIntegral.integral_const_mul, hval]
      refine mul_le_mul_of_nonneg_left ?_ hD
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hs0.le hst (by linarith)) (by linarith)

end Breakdown.FracCert.SmoothFirstGain.Internal

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow SmoothFirstGain.Internal

theorem mildFirstGain : MildFirstGainStatement := by
  intro α hα hα2 F hF u t ht hmild σ hσ
  obtain ⟨C, hC0, hC⟩ := (fracBilin_holds α hα).2
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hmild.1
  have hM : ∀ r ∈ Icc 0 t, ‖u r‖ ≤ max M0 0 := fun r hr => (hM0 r hr).trans (le_max_left _ _)
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Real.sqrt (σ ^ (-((2 * α - 1) / (2 * α))) * ‖u 0‖ ^ 2) +
      C * max M0 0 * max M0 0 * 2 ^ ((α + 1) / (2 * α)) *
        (t ^ (1 - (α + 1) / (2 * α)) / (1 - (α + 1) / (2 * α))) := ⟨_, rfl⟩
  refine ⟨(2 * π)⁻¹ ^ 2 * R ^ 2, fun s hs => ?_⟩
  have hs0 : 0 < s := hσ.1.trans_le hs.1
  obtain ⟨hint, heq⟩ := hmild.2 s ⟨hs0.le, hs.2⟩
  obtain ⟨hG, hK⟩ := hF
  have hint' := hint
  rw [hK] at hint'
  have heq' := heq
  simp only [hG, hK, sub_zero] at heq'
  have key : ∀ N : ℕ, ‖cutOp α N (u s : L2C)‖ ≤ R := fun N => hR ▸
    cut_bound hα hC0 hC u hσ.1 hs.1 hs.2 (le_max_right _ _) hM hint' heq' N
  calc fracHomSq (α + 1 / 2) (u s) ≤ ENNReal.ofReal ((2 * π)⁻¹ ^ 2) * gainNormSq α (u s : L2C) :=
        fracHomSq_le α (u s)
    _ ≤ ENNReal.ofReal ((2 * π)⁻¹ ^ 2) * ENNReal.ofReal (R ^ 2) := by
        gcongr
        exact (gainNormSq_le_iSup hα _).trans (iSup_le fun N => ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (key N) 2))
    _ = ENNReal.ofReal ((2 * π)⁻¹ ^ 2 * R ^ 2) := (ENNReal.ofReal_mul (by positivity)).symm

end Breakdown.FracCert
