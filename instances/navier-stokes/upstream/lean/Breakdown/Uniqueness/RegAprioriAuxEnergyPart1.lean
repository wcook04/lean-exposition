import Breakdown.Uniqueness.RegCurveAuxPointwise
import Breakdown.Uniqueness.RegAprioriAuxCont

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem hsWeight_le_of_le {k m : ℕ} (h : k ≤ m) (ξ : Space) : hsWeight k ξ ≤ hsWeight m ξ :=
  pow_le_pow_right₀ (by nlinarith [sq_nonneg ‖ξ‖]) h

theorem hsNormSq_le_hsNormSq_of_le {k m : ℕ} (h : k ≤ m) (f : Space → CSpace) :
    hsNormSq k f ≤ hsNormSq m f :=
  lintegral_mono fun ξ => by gcongr; exact hsWeight_le_of_le h ξ

theorem homNormSq_le_hsNormSq {k m : ℕ} (h : k ≤ m) (f : Space → CSpace) :
    homNormSq k f ≤ hsNormSq m f :=
  lintegral_mono fun ξ => by
    gcongr
    calc ‖ξ‖ ^ (2 * k) = (‖ξ‖ ^ 2) ^ k := pow_mul _ _ _
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ k := by gcongr; linarith
      _ ≤ hsWeight m ξ := hsWeight_le_of_le h ξ

theorem isHsCurve_of_le {k m : ℕ} (h : k ≤ m) {F : ℝ → Space → CSpace} {a b : ℝ}
    (hF : IsHsCurve m F a b) : IsHsCurve k F a b :=
  ⟨fun t ht => ⟨(hF.1 t ht).1, lt_of_le_of_lt (hsNormSq_le_hsNormSq_of_le h _) (hF.1 t ht).2⟩,
    fun t₀ ht₀ => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hF.2 t₀ ht₀)
      (fun _ => bot_le) (fun _ => hsNormSq_le_hsNormSq_of_le h _)⟩

private theorem continuous_divFreeC (ξ : Space) : Continuous (divFreeC ξ) := by
  unfold divFreeC
  fun_prop

theorem continuousOn_nonlinSymbol_of_hsCurve {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : IsHsCurve 1 F 0 T) (ξ : Space) :
    ContinuousOn (fun s => nonlinSymbol (F s) ξ) (Icc 0 T) :=
  ((continuous_divFreeC ξ).comp_continuousOn (continuousOn_advectionSymbol_apply hF ξ)).neg

theorem setLIntegral_homNormSq_two_lt_top {m : ℕ} (hm : 2 ≤ m) {T : ℝ} {F : ℝ → Space → CSpace}
    (hF : IsHsCurve m F 0 T) : ∫⁻ s in Icc 0 T, homNormSq 2 (F s) < ⊤ := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.bddAbove_image (continuousOn_hsNormSq_toReal hF))
  have hle : ∀ s ∈ Icc 0 T, homNormSq 2 (F s) ≤ ENNReal.ofReal B := fun s hs => by
    calc homNormSq 2 (F s) ≤ hsNormSq m (F s) := homNormSq_le_hsNormSq hm _
      _ = ENNReal.ofReal (hsNormSq m (F s)).toReal := (ENNReal.ofReal_toReal (hF.1 s hs).2.ne).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hB ⟨s, hs, rfl⟩)
  calc ∫⁻ s in Icc 0 T, homNormSq 2 (F s) ≤ ∫⁻ s in Icc 0 T, ENNReal.ofReal B :=
        setLIntegral_mono' measurableSet_Icc hle
    _ = ENNReal.ofReal B * volume (Icc 0 T) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

theorem ofReal_mul_rpow_three_quarters_le {a : ℝ} (ha : 0 ≤ a) (y : ℝ≥0∞) :
    ENNReal.ofReal a * y ^ (3 / 4 : ℝ) ≤
      ENNReal.ofReal (4 * π ^ 2) * y + ENNReal.ofReal (a * (a / (4 * π ^ 2)) ^ 3) := by
  have hpi : 0 < 4 * π ^ 2 := by positivity
  rcases eq_or_ne y ⊤ with rfl | hy
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hpi).ne']
    simp
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 ≤ r ∧ y = ENNReal.ofReal r :=
    ⟨y.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hy).symm⟩
  have hb0 : 0 ≤ a / (4 * π ^ 2) := div_nonneg ha hpi.le
  rw [ENNReal.ofReal_rpow_of_nonneg hr (by norm_num), ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_mul hpi.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hq0 : 0 ≤ r ^ (1 / 4 : ℝ) := Real.rpow_nonneg hr _
  have hr3 : r ^ (3 / 4 : ℝ) = (r ^ (1 / 4 : ℝ)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
  have hr4 : r = (r ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
  have hab : a = 4 * π ^ 2 * (a / (4 * π ^ 2)) := by field_simp
  rw [hr3]
  conv_rhs => rw [hr4]
  rcases le_total (r ^ (1 / 4 : ℝ)) (a / (4 * π ^ 2)) with h | h
  · have h3 : (r ^ (1 / 4 : ℝ)) ^ 3 ≤ (a / (4 * π ^ 2)) ^ 3 := pow_le_pow_left₀ hq0 h 3
    have := mul_le_mul_of_nonneg_left h3 ha
    have := mul_nonneg hpi.le (pow_nonneg hq0 4)
    linarith
  · have key : a * (r ^ (1 / 4 : ℝ)) ^ 3 ≤ 4 * π ^ 2 * (r ^ (1 / 4 : ℝ)) ^ 4 := by
      calc a * (r ^ (1 / 4 : ℝ)) ^ 3 = 4 * π ^ 2 * ((a / (4 * π ^ 2)) * (r ^ (1 / 4 : ℝ)) ^ 3) := by
            field_simp
        _ ≤ 4 * π ^ 2 * (r ^ (1 / 4 : ℝ) * (r ^ (1 / 4 : ℝ)) ^ 3) := by gcongr
        _ = 4 * π ^ 2 * (r ^ (1 / 4 : ℝ)) ^ 4 := by ring
    have := mul_nonneg ha (pow_nonneg hb0 3)
    linarith

theorem setLIntegral_ofReal_eq_intervalIntegral {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 T)) (hg0 : ∀ s, 0 ≤ g s) :
    ∫⁻ s in Icc 0 T, ENNReal.ofReal (g s) = ENNReal.ofReal (∫ s in (0 : ℝ)..T, g s) := by
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal (hg.integrableOn_Icc) (ae_of_all _ hg0)]

theorem energy_inequality_apply {T : ℝ} (hT : 0 < T) {F : ℝ → Space → CSpace}
    (hF : IsHsCurve 1 F 0 T) (hd : IsVarConstSymbol F 0 T) (ξ : Space) :
    ENNReal.ofReal (8 * π ^ 2) * ∫⁻ s in Icc 0 T, ENNReal.ofReal (‖ξ‖ ^ (2 * 2)) * ‖F s ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖F 0 ξ‖ₑ ^ 2 +
        2 * ∫⁻ s in Icc 0 T, ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) := by
  have hN := continuousOn_nonlinSymbol_of_hsCurve hF ξ
  have hder : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun τ => F τ ξ)
      (-(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • F t ξ + nonlinSymbol (F t) ξ) (Icc 0 T) t :=
    fun t ht => hasDerivWithinAt_apply_of_varConst hT hd hN ht
  have hu : ContinuousOn (fun τ => F τ ξ) (Icc 0 T) := fun t ht => (hder t ht).continuousWithinAt
  have hsm : ∀ t, (-(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • F t ξ) =
      (-(4 * π ^ 2 * ‖ξ‖ ^ 2) : ℝ) • F t ξ := fun t => by
    rw [← Complex.coe_smul]; push_cast; ring_nf
  have hin : ∀ t, inner ℝ (F t ξ) (-(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • F t ξ + nonlinSymbol (F t) ξ) =
      -(4 * π ^ 2 * ‖ξ‖ ^ 2) * ‖F t ξ‖ ^ 2 + inner ℝ (F t ξ) (nonlinSymbol (F t) ξ) := fun t => by
    rw [inner_add_right, hsm, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hφ : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun τ => ‖F τ ξ‖ ^ 2)
      (2 * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * ‖F t ξ‖ ^ 2 + inner ℝ (F t ξ) (nonlinSymbol (F t) ξ)))
      (Icc 0 T) t := fun t ht => by
    rw [← hin]; exact (hder t ht).norm_sq
  have hi : ContinuousOn (fun t => inner ℝ (F t ξ) (nonlinSymbol (F t) ξ)) (Icc 0 T) := hu.inner hN
  have hn2 : ContinuousOn (fun t => ‖F t ξ‖ ^ 2) (Icc 0 T) := hu.norm.pow 2
  have hnn : ContinuousOn (fun t => ‖F t ξ‖ * ‖nonlinSymbol (F t) ξ‖) (Icc 0 T) := hu.norm.mul hN.norm
  have hgc : ContinuousOn (fun t => 2 * (-(4 * π ^ 2 * ‖ξ‖ ^ 2) * ‖F t ξ‖ ^ 2 +
      inner ℝ (F t ξ) (nonlinSymbol (F t) ξ))) (Icc 0 T) :=
    continuousOn_const.mul ((continuousOn_const.mul hn2).add hi)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT.le hn2
    (fun t ht => ((hφ t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt) (hgc.intervalIntegrable_of_Icc hT.le)
  have i1 := hn2.intervalIntegrable_of_Icc (μ := volume) hT.le
  have i2 := hi.intervalIntegrable_of_Icc (μ := volume) hT.le
  have i3 := hnn.intervalIntegrable_of_Icc (μ := volume) hT.le
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (i1.const_mul _) i2,
    intervalIntegral.integral_const_mul] at hFTC
  have hQR : ∫ t in (0 : ℝ)..T, inner ℝ (F t ξ) (nonlinSymbol (F t) ξ) ≤
      ∫ t in (0 : ℝ)..T, ‖F t ξ‖ * ‖nonlinSymbol (F t) ξ‖ :=
    intervalIntegral.integral_mono_on hT.le i2 i3 fun t _ => real_inner_le_norm _ _
  have hP0 : 0 ≤ ∫ t in (0 : ℝ)..T, ‖F t ξ‖ ^ 2 :=
    intervalIntegral.integral_nonneg hT.le fun t _ => by positivity
  have hT2 : 0 ≤ ‖F T ξ‖ ^ 2 := by positivity
  have hreal : 8 * π ^ 2 * (‖ξ‖ ^ (2 * 2) * ∫ t in (0 : ℝ)..T, ‖F t ξ‖ ^ 2) ≤
      ‖ξ‖ ^ (2 * 1) * ‖F 0 ξ‖ ^ 2 +
        2 * (‖ξ‖ ^ (2 * 1) * ∫ t in (0 : ℝ)..T, ‖F t ξ‖ * ‖nonlinSymbol (F t) ξ‖) := by
    have hx : 0 ≤ ‖ξ‖ ^ 2 := by positivity
    have key : 8 * π ^ 2 * ‖ξ‖ ^ 2 * ∫ t in (0 : ℝ)..T, ‖F t ξ‖ ^ 2 ≤
        ‖F 0 ξ‖ ^ 2 + 2 * ∫ t in (0 : ℝ)..T, ‖F t ξ‖ * ‖nonlinSymbol (F t) ξ‖ := by
      nlinarith
    have := mul_le_mul_of_nonneg_left key hx
    norm_num
    nlinarith
  have e1 : ∀ s, ENNReal.ofReal (‖ξ‖ ^ (2 * 2)) * ‖F s ξ‖ₑ ^ 2 =
      ENNReal.ofReal (‖ξ‖ ^ (2 * 2) * ‖F s ξ‖ ^ 2) := fun s => by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg (F s ξ)) 2, ofReal_norm]
  have e2 : ∀ s, ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ) =
      ENNReal.ofReal (‖ξ‖ ^ (2 * 1) * (‖F s ξ‖ * ‖nonlinSymbol (F s) ξ‖)) := fun s => by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
      ofReal_norm]
  have e0 : ENNReal.ofReal (‖ξ‖ ^ (2 * 1)) * ‖F 0 ξ‖ₑ ^ 2 =
      ENNReal.ofReal (‖ξ‖ ^ (2 * 1) * ‖F 0 ξ‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg (F 0 ξ)) 2, ofReal_norm]
  simp only [e1, e2, e0]
  rw [setLIntegral_ofReal_eq_intervalIntegral (g := fun s => ‖ξ‖ ^ (2 * 2) * ‖F s ξ‖ ^ 2) hT.le
      (continuousOn_const.mul hn2) (fun s => by positivity),
    setLIntegral_ofReal_eq_intervalIntegral
      (g := fun s => ‖ξ‖ ^ (2 * 1) * (‖F s ξ‖ * ‖nonlinSymbol (F s) ξ‖)) hT.le (continuousOn_const.mul hnn) (fun s => by positivity),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← ENNReal.ofReal_mul (by positivity)]
  have h2 : ∀ x : ℝ, (2 : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) := fun x => by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [h2, ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by norm_num) (mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg hT.le fun t _ => by positivity)))]
  exact ENNReal.ofReal_le_ofReal hreal

end Breakdown.SmoothFlow
