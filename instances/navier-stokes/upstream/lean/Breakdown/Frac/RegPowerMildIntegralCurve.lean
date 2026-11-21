import Breakdown.Frac.StSpaceReg

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem rpow_two_eq' (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

private theorem power_rate_nonneg (α : ℝ) (ξ : Space) : 0 ≤ (2 * π * ‖ξ‖) ^ (2 * α) :=
  Real.rpow_nonneg (by positivity) _

private theorem powerHeat_mul (α t s : ℝ) (ξ : Space) :
    powerHeatSymbol α (t - s) ξ = powerHeatSymbol α t ξ * powerHeatSymbol α (-s) ξ := by
  unfold powerHeatSymbol
  rw [← Real.exp_add]
  congr 1
  ring

private theorem powerHeat_anti (α : ℝ) {τ τ' : ℝ} (h : τ ≤ τ') (ξ : Space) :
    powerHeatSymbol α τ' ξ ≤ powerHeatSymbol α τ ξ := by
  unfold powerHeatSymbol
  rw [Real.exp_le_exp]
  have := mul_le_mul_of_nonneg_right h (power_rate_nonneg α ξ)
  linarith

private theorem powerHeat_continuous_time (α : ℝ) (ξ : Space) :
    Continuous (fun t : ℝ => ((powerHeatSymbol α t ξ : ℝ) : ℂ)) := by
  unfold powerHeatSymbol
  fun_prop

private theorem powerHeat_continuous_neg (α : ℝ) (ξ : Space) :
    Continuous (fun s : ℝ => ((powerHeatSymbol α (-s) ξ : ℝ) : ℂ)) := by
  unfold powerHeatSymbol
  fun_prop

private theorem powerHeat_continuous_sub (α t : ℝ) (ξ : Space) :
    Continuous (fun s : ℝ => ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ)) := by
  unfold powerHeatSymbol
  fun_prop

private theorem powerHeat_continuous_joint {α : ℝ} (hα : 0 ≤ α) (t : ℝ) :
    Continuous (fun p : Space × ℝ => ((powerHeatSymbol α (t - p.2) p.1 : ℝ) : ℂ)) := by
  have hb : Continuous (fun p : Space × ℝ => 2 * π * ‖p.1‖) := by fun_prop
  have hr : Continuous (fun p : Space × ℝ => (2 * π * ‖p.1‖) ^ (2 * α)) :=
    hb.rpow_const (fun _ => Or.inr (by linarith))
  have hl : Continuous (fun p : Space × ℝ => -((t - p.2) * (2 * π * ‖p.1‖) ^ (2 * α))) :=
    ((continuous_const.sub continuous_snd).mul hr).neg
  exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp hl)

private theorem weight_chunks {α C : ℝ}
    (hC : ∀ a t : ℝ, a ≤ t → t ≤ a + 1 → ∀ ξ : Space,
      ∫⁻ s in Ioc a t, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) * powerHeatSymbol α (t - s) ξ ^ 2) ≤
        ENNReal.ofReal C) (ξ : Space) :
    ∀ k : ℕ, ∀ a t : ℝ, a ≤ t → t ≤ a + (k + 1) →
      ∫⁻ s in Ioc a t, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) * powerHeatSymbol α (t - s) ξ ^ 2) ≤
        ((k : ℝ≥0∞) + 1) * ENNReal.ofReal C := by
  intro k
  induction k with
  | zero =>
    intro a t hat hta
    simpa using hC a t hat (by simpa using hta) ξ
  | succ k ih =>
    intro a t hat hta
    by_cases h1 : t ≤ a + 1
    · refine (hC a t hat h1 ξ).trans ?_
      calc ENNReal.ofReal C = 1 * ENNReal.ofReal C := (one_mul _).symm
        _ ≤ _ := by
          gcongr
          exact le_add_self
    · replace h1 := not_le.1 h1
      have hsplit : Ioc a t = Ioc a (a + 1) ∪ Ioc (a + 1) t :=
        (Ioc_union_Ioc_eq_Ioc (by linarith) h1.le).symm
      rw [hsplit]
      refine (lintegral_union_le _ _ _).trans ?_
      have hA : ∫⁻ s in Ioc a (a + 1),
          ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) * powerHeatSymbol α (t - s) ξ ^ 2) ≤ ENNReal.ofReal C := by
        refine le_trans (lintegral_mono fun s => ?_) (hC a (a + 1) (by linarith) le_rfl ξ)
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
        have h0 : 0 ≤ powerHeatSymbol α (t - s) ξ := (Real.exp_pos _).le
        exact pow_le_pow_left₀ h0 (powerHeat_anti α (by linarith) ξ) 2
      have hB := ih (a + 1) t h1.le (by push_cast at hta; linarith)
      calc _ ≤ ENNReal.ofReal C + ((k : ℝ≥0∞) + 1) * ENNReal.ofReal C := add_le_add hA hB
        _ = _ := by push_cast; ring

private theorem weight_uniform {α C : ℝ}
    (hC : ∀ a t : ℝ, a ≤ t → t ≤ a + 1 → ∀ ξ : Space,
      ∫⁻ s in Ioc a t, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) * powerHeatSymbol α (t - s) ξ ^ 2) ≤
        ENNReal.ofReal C) {a b t : ℝ} (ht : t ∈ Icc a b) (ξ : Space) :
    ENNReal.ofReal (1 + ‖ξ‖ ^ 2) * ∫⁻ s in Ioc a t, ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2 ≤
      ((⌈b - a⌉₊ : ℝ≥0∞) + 1) * ENNReal.ofReal C := by
  have hpt : ∀ s, ENNReal.ofReal (1 + ‖ξ‖ ^ 2) * ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2 =
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) * powerHeatSymbol α (t - s) ξ ^ 2) := by
    intro s
    have h0 : 0 ≤ powerHeatSymbol α (t - s) ξ := (Real.exp_pos _).le
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0, ← ENNReal.ofReal_pow h0,
      ← ENNReal.ofReal_mul (by positivity)]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [hpt]
  refine weight_chunks hC ξ ⌈b - a⌉₊ a t ht.1 ?_
  have := Nat.le_ceil (b - a)
  linarith [ht.2]

private theorem enorm_memoryIntegral_sq_le {α a t : ℝ} (hat : a ≤ t) (N : ℝ → Space → CSpace)
    (ξ : Space) (hm : AEMeasurable (fun s => ‖N s ξ‖ₑ) (volume.restrict (Ioc a t))) :
    ‖powerMildIntegral α a N t ξ‖ₑ ^ 2 ≤
      (∫⁻ s in Ioc a t, ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2) *
        ∫⁻ s in Ioc a t, ‖N s ξ‖ₑ ^ 2 := by
  have h1 : ‖powerMildIntegral α a N t ξ‖ₑ ≤
      ∫⁻ s in Ioc a t, ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ * ‖N s ξ‖ₑ := by
    unfold powerMildIntegral
    rw [intervalIntegral.integral_of_le hat]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1
    funext s
    rw [enorm_smul]
  have hh : AEMeasurable (fun s => ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ)
      (volume.restrict (Ioc a t)) :=
    (powerHeat_continuous_sub α t ξ).measurable.enorm.aemeasurable
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc a t))
    Real.HolderConjugate.two_two hh hm
  simp only [Pi.mul_apply, rpow_two_eq'] at h2
  calc ‖powerMildIntegral α a N t ξ‖ₑ ^ 2
      ≤ (∫⁻ s in Ioc a t, ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ * ‖N s ξ‖ₑ) ^ 2 :=
        pow_le_pow_left₀ bot_le h1 2
    _ ≤ ((∫⁻ s in Ioc a t, ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ s in Ioc a t, ‖N s ξ‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ bot_le h2 2
    _ = _ := by
      have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      rw [mul_pow, hsq, hsq]

private theorem hsWeight_succ' (n : ℕ) (ξ : Space) :
    ENNReal.ofReal (hsWeight (n + 1) ξ) =
      ENNReal.ofReal (hsWeight n ξ) * ENNReal.ofReal (1 + ‖ξ‖ ^ 2) := by
  unfold hsWeight
  rw [pow_succ, ENNReal.ofReal_mul (by positivity)]

private theorem memoryIntegral_weight_le {α a b t : ℝ} {W : ℝ≥0∞} (ht : t ∈ Icc a b)
    (hW : ∀ ξ : Space, ENNReal.ofReal (1 + ‖ξ‖ ^ 2) *
      ∫⁻ s in Ioc a t, ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2 ≤ W)
    (n : ℕ) (N : ℝ → Space → CSpace)
    (ξ : Space) (hm : AEMeasurable (fun s => ‖N s ξ‖ₑ) (volume.restrict (Icc a b))) :
    ENNReal.ofReal (hsWeight (n + 1) ξ) * ‖powerMildIntegral α a N t ξ‖ₑ ^ 2 ≤
      W * (ENNReal.ofReal (hsWeight n ξ) * ∫⁻ s in Icc a b, ‖N s ξ‖ₑ ^ 2) := by
  have hsub : Ioc a t ⊆ Icc a b := fun x hx => ⟨hx.1.le, hx.2.trans ht.2⟩
  have h2 := enorm_memoryIntegral_sq_le (α := α) ht.1 N ξ (hm.mono_set hsub)
  have h5 : ∫⁻ s in Ioc a t, ‖N s ξ‖ₑ ^ 2 ≤ ∫⁻ s in Icc a b, ‖N s ξ‖ₑ ^ 2 := lintegral_mono_set hsub
  rw [hsWeight_succ', mul_assoc]
  calc ENNReal.ofReal (hsWeight n ξ) *
        (ENNReal.ofReal (1 + ‖ξ‖ ^ 2) * ‖powerMildIntegral α a N t ξ‖ₑ ^ 2)
      ≤ ENNReal.ofReal (hsWeight n ξ) * (ENNReal.ofReal (1 + ‖ξ‖ ^ 2) *
          ((∫⁻ s in Ioc a t, ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2) *
            ∫⁻ s in Ioc a t, ‖N s ξ‖ₑ ^ 2)) := by
        gcongr
    _ = ENNReal.ofReal (hsWeight n ξ) * ((ENNReal.ofReal (1 + ‖ξ‖ ^ 2) *
          ∫⁻ s in Ioc a t, ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2) *
            ∫⁻ s in Ioc a t, ‖N s ξ‖ₑ ^ 2) := by
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (hsWeight n ξ) * (W * ∫⁻ s in Icc a b, ‖N s ξ‖ₑ ^ 2) := by
        gcongr
        exact hW ξ
    _ = _ := by rw [mul_left_comm]

private theorem enorm_sub_sq_le' (x y : CSpace) : ‖x - y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have e : ∀ z : CSpace, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, e]
  have key : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x - y), norm_sub_le x y]
  calc ENNReal.ofReal (‖x - y‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal key
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

private theorem one_le_hsWeight' (n : ℕ) (ξ : Space) : 1 ≤ ENNReal.ofReal (hsWeight n ξ) := by
  rw [ENNReal.one_le_ofReal]
  unfold hsWeight
  exact one_le_pow₀ (by nlinarith [sq_nonneg ‖ξ‖])

private theorem measurable_hsWeight' (n : ℕ) :
    Measurable (fun ξ : Space => ENNReal.ofReal (hsWeight n ξ)) := by
  have : Continuous (fun ξ : Space => hsWeight n ξ) := by
    unfold hsWeight
    fun_prop
  exact ENNReal.measurable_ofReal.comp this.measurable

theorem powerMildIntegralCurve (α : ℝ) (hα : 1 < α) (_h1 : PowerHeatBasicStatement α)
    (h2 : PowerHeatWeightStatement α) : PowerMildIntegralCurveStatement α := by
  intro n a b N K hN hK
  obtain ⟨C, hC⟩ := h2
  set W : ℝ≥0∞ := ((⌈b - a⌉₊ : ℝ≥0∞) + 1) * ENNReal.ofReal C with hWdef
  have hWtop : W ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩)
      ENNReal.ofReal_ne_top
  have hW : ∀ t ∈ Icc a b, ∀ ξ : Space, ENNReal.ofReal (1 + ‖ξ‖ ^ 2) *
      ∫⁻ s in Ioc a t, ‖(((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ))‖ₑ ^ 2 ≤ W :=
    fun t ht ξ => weight_uniform hC ht ξ
  have hα0 : 0 ≤ α := by linarith
  set J : Space → ℝ≥0∞ := fun ξ => ∫⁻ s in Icc a b, ‖N s ξ‖ₑ ^ 2 with hJ
  have hmξ : ∀ᵐ ξ ∂(volume : Measure Space),
      AEStronglyMeasurable (fun s => N s ξ) (volume.restrict (Icc a b)) := hN.prodMk_left
  have hJm : AEMeasurable J volume := (hN.enorm.pow_const 2).lintegral_prod_right'
  have hwJm : AEMeasurable (fun ξ => ENNReal.ofReal (hsWeight n ξ) * J ξ) volume :=
    (measurable_hsWeight' n).aemeasurable.mul hJm
  have hfin : ∫⁻ ξ, ENNReal.ofReal (hsWeight n ξ) * J ξ ≠ ⊤ := by
    have e1 : ∫⁻ ξ, ENNReal.ofReal (hsWeight n ξ) * J ξ =
        ∫⁻ ξ, ∫⁻ s in Icc a b, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 := by
      refine lintegral_congr fun ξ => ?_
      rw [hJ, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hprod : AEMeasurable (Function.uncurry fun (ξ : Space) (s : ℝ) =>
        ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2)
        ((volume : Measure Space).prod (volume.restrict (Icc a b))) :=
      ((measurable_hsWeight' n).comp measurable_fst).aemeasurable.mul (hN.enorm.pow_const 2)
    rw [e1, lintegral_lintegral_swap hprod]
    have e2 : ∫⁻ s in Icc a b, ∫⁻ ξ, ENNReal.ofReal (hsWeight n ξ) * ‖N s ξ‖ₑ ^ 2 ≤
        ∫⁻ s in Icc a b, ENNReal.ofReal K :=
      lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hK))
    refine ne_top_of_le_ne_top ?_ e2
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hbound : ∀ t ∈ Icc a b, ∀ᵐ ξ ∂(volume : Measure Space),
      ENNReal.ofReal (hsWeight (n + 1) ξ) * ‖powerMildIntegral α a N t ξ‖ₑ ^ 2 ≤
        W * (ENNReal.ofReal (hsWeight n ξ) * J ξ) := by
    intro t ht
    filter_upwards [hmξ] with ξ hξ
    exact memoryIntegral_weight_le ht (hW t ht) n N ξ hξ.enorm
  have hmeas : ∀ t ∈ Icc a b, AEStronglyMeasurable (powerMildIntegral α a N t) volume := by
    intro t ht
    have hsub : Ioc a t ⊆ Icc a b := fun x hx => ⟨hx.1.le, hx.2.trans ht.2⟩
    have e : (volume : Measure Space).prod (volume.restrict (Ioc a t)) =
        ((volume : Measure Space).prod (volume.restrict (Icc a b))).restrict (univ ×ˢ Ioc a t) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.2 hsub]
    have hN' : AEStronglyMeasurable (fun p : Space × ℝ => N p.2 p.1)
        ((volume : Measure Space).prod (volume.restrict (Ioc a t))) := by
      rw [e]
      exact hN.restrict
    have h := ((powerHeat_continuous_joint hα0 t).aestronglyMeasurable.smul hN').integral_prod_right'
    have e2 : powerMildIntegral α a N t = fun ξ => ∫ s in Ioc a t,
        ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • N s ξ := by
      funext ξ
      unfold powerMildIntegral
      rw [intervalIntegral.integral_of_le ht.1]
    rw [e2]
    exact h
  refine ⟨fun t ht => ⟨hmeas t ht, ?_⟩, fun t₀ ht₀ => ?_⟩
  · unfold hsNormSq
    refine lt_of_le_of_lt (lintegral_mono_ae (hbound t ht)) ?_
    rw [lintegral_const_mul' _ _ hWtop]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hWtop) (lt_top_iff_ne_top.2 hfin)
  · have hab : a ≤ b := ht₀.1.trans ht₀.2
    have hlim : ∀ᵐ ξ ∂(volume : Measure Space), Tendsto (fun t => ENNReal.ofReal (hsWeight (n + 1) ξ) *
        ‖(powerMildIntegral α a N t - powerMildIntegral α a N t₀) ξ‖ₑ ^ 2)
        (𝓝[Icc a b] t₀) (𝓝 0) := by
      filter_upwards [hmξ, ae_lt_top' hwJm hfin] with ξ hξ hfξ
      have hJξ : J ξ < ⊤ := by
        refine lt_of_le_of_lt ?_ hfξ
        calc J ξ = 1 * J ξ := (one_mul _).symm
          _ ≤ ENNReal.ofReal (hsWeight n ξ) * J ξ := by gcongr; exact one_le_hsWeight' n ξ
      have hL2 : MemLp (fun s => N s ξ) 2 (volume.restrict (Icc a b)) := by
        refine ⟨hξ, ?_⟩
        rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
        simpa [rpow_two_eq'] using hJξ
      have hint : IntegrableOn (fun s => N s ξ) (Icc a b) := hL2.integrable one_le_two
      have hint2 : IntegrableOn (fun s => ((powerHeatSymbol α (-s) ξ : ℝ) : ℂ) • N s ξ) (uIcc a b) := by
        rw [uIcc_of_le hab]
        exact hint.continuousOn_smul (powerHeat_continuous_neg α ξ).continuousOn isCompact_Icc
      have hP := intervalIntegral.continuousOn_primitive_interval hint2
      rw [uIcc_of_le hab] at hP
      have hfac : ∀ t, powerMildIntegral α a N t ξ = ((powerHeatSymbol α t ξ : ℝ) : ℂ) •
          ∫ s in a..t, ((powerHeatSymbol α (-s) ξ : ℝ) : ℂ) • N s ξ := by
        intro t
        unfold powerMildIntegral
        rw [← intervalIntegral.integral_smul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        rw [powerHeat_mul, Complex.ofReal_mul, mul_smul]
      have hcw : ContinuousWithinAt (fun t => powerMildIntegral α a N t ξ) (Icc a b) t₀ := by
        simp only [hfac]
        exact (powerHeat_continuous_time α ξ).continuousWithinAt.smul (hP t₀ ht₀)
      have h0 : Tendsto (fun t => powerMildIntegral α a N t ξ - powerMildIntegral α a N t₀ ξ)
          (𝓝[Icc a b] t₀) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 hcw
      have h1' : Tendsto (fun t => ‖powerMildIntegral α a N t ξ - powerMildIntegral α a N t₀ ξ‖ₑ)
          (𝓝[Icc a b] t₀) (𝓝 0) := by
        have h := (continuous_enorm.tendsto (0 : CSpace)).comp h0
        rw [enorm_zero] at h
        exact h
      have h2' := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (hsWeight (n + 1) ξ))
        (ENNReal.Tendsto.pow (n := 2) h1') (Or.inr ENNReal.ofReal_ne_top)
      simpa using h2'
    have hmain := tendsto_lintegral_filter_of_dominated_convergence'
      (fun ξ => 4 * (W * (ENNReal.ofReal (hsWeight n ξ) * J ξ)))
      (F := fun t ξ => ENNReal.ofReal (hsWeight (n + 1) ξ) *
        ‖(powerMildIntegral α a N t - powerMildIntegral α a N t₀) ξ‖ₑ ^ 2)
      (f := fun _ => 0) ?_ ?_ ?_ hlim
    · simpa [hsNormSq] using hmain
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (measurable_hsWeight' (n + 1)).aemeasurable.mul
        (((hmeas t ht).sub (hmeas t₀ ht₀)).enorm.pow_const 2)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [hbound t ht, hbound t₀ ht₀] with ξ hb1 hb2
      calc ENNReal.ofReal (hsWeight (n + 1) ξ) *
            ‖(powerMildIntegral α a N t - powerMildIntegral α a N t₀) ξ‖ₑ ^ 2
          ≤ ENNReal.ofReal (hsWeight (n + 1) ξ) * (2 * ‖powerMildIntegral α a N t ξ‖ₑ ^ 2 +
              2 * ‖powerMildIntegral α a N t₀ ξ‖ₑ ^ 2) := by
            gcongr
            exact enorm_sub_sq_le' _ _
        _ = 2 * (ENNReal.ofReal (hsWeight (n + 1) ξ) * ‖powerMildIntegral α a N t ξ‖ₑ ^ 2) +
              2 * (ENNReal.ofReal (hsWeight (n + 1) ξ) * ‖powerMildIntegral α a N t₀ ξ‖ₑ ^ 2) := by
            rw [mul_add, mul_left_comm, mul_left_comm (ENNReal.ofReal _) 2]
        _ ≤ 2 * (W * (ENNReal.ofReal (hsWeight n ξ) * J ξ)) +
              2 * (W * (ENNReal.ofReal (hsWeight n ξ) * J ξ)) := by
            gcongr
        _ = _ := by
            rw [← add_mul]
            norm_num
    · rw [lintegral_const_mul' 4 _ (by norm_num), lintegral_const_mul' _ _ hWtop]
      exact ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top hWtop hfin)

end Breakdown.SmoothFlow
