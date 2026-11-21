import Breakdown.Uniqueness.RegToolkit

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private def lintSq (u : Space → ℂ) : ℝ≥0∞ := ∫⁻ η, ‖u η‖ₑ ^ 2

private lemma lintegral_enorm_mul_le (u v : Space → ℂ) (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) :
    ∫⁻ η, ‖u η * v η‖ₑ ≤ lintSq u ^ (1 / 2 : ℝ) * lintSq v ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hu.enorm hv.enorm
  calc ∫⁻ η, ‖u η * v η‖ₑ = ∫⁻ η, ((fun a => ‖u a‖ₑ) * fun a => ‖v a‖ₑ) η := by
        simp [enorm_mul]
    _ ≤ _ := h
    _ = _ := by simp only [lintSq, ENNReal.rpow_two]

private lemma enorm_integral_mul_le (u v : Space → ℂ) (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) :
    ‖∫ η, u η * v η‖ₑ ≤ lintSq u ^ (1 / 2 : ℝ) * lintSq v ^ (1 / 2 : ℝ) :=
  (enorm_integral_le_lintegral_enorm _).trans (lintegral_enorm_mul_le u v hu hv)

private lemma integrable_mul_of_lintSq {u v : Space → ℂ} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (hu2 : lintSq u ≠ ⊤) (hv2 : lintSq v ≠ ⊤) :
    Integrable (fun η => u η * v η) volume := by
  refine ⟨hu.mul hv, ?_⟩
  refine lt_of_le_of_lt (lintegral_enorm_mul_le u v hu hv) ?_
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hu2)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hv2)

private lemma tendsto_rpow_half {ι : Type*} {l : Filter ι} {d : ι → ℝ≥0∞}
    (hd : Tendsto d l (𝓝 0)) : Tendsto (fun s => d s ^ (1 / 2 : ℝ)) l (𝓝 0) := by
  have h := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hd
  simpa [ENNReal.zero_rpow_of_pos, Function.comp_def] using h

private lemma tendsto_integral_mul {ι : Type*} {l : Filter ι} {u v : ι → Space → ℂ}
    {u₀ v₀ : Space → ℂ} (hu₀ : AEStronglyMeasurable u₀ volume)
    (hv₀ : AEStronglyMeasurable v₀ volume)
    (hmeas : ∀ᶠ s in l, AEStronglyMeasurable (u s) volume ∧ AEStronglyMeasurable (v s) volume)
    (hu₀2 : lintSq u₀ ≠ ⊤) (hv₀2 : lintSq v₀ ≠ ⊤)
    (hu : Tendsto (fun s => lintSq (u s - u₀)) l (𝓝 0))
    (hv : Tendsto (fun s => lintSq (v s - v₀)) l (𝓝 0)) :
    Tendsto (fun s => ∫ η, u s η * v s η) l (𝓝 (∫ η, u₀ η * v₀ η)) := by
  have hA : lintSq u₀ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hu₀2
  have hB : lintSq v₀ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hv₀2
  have hu' := tendsto_rpow_half hu
  have hv' := tendsto_rpow_half hv
  have hg : Tendsto (fun s => lintSq (u s - u₀) ^ (1 / 2 : ℝ) * lintSq v₀ ^ (1 / 2 : ℝ) +
      lintSq u₀ ^ (1 / 2 : ℝ) * lintSq (v s - v₀) ^ (1 / 2 : ℝ) +
      lintSq (u s - u₀) ^ (1 / 2 : ℝ) * lintSq (v s - v₀) ^ (1 / 2 : ℝ)) l (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul_const hu' (Or.inr hB)
    have h2 := ENNReal.Tendsto.const_mul hv' (Or.inr hA)
    have h3 := ENNReal.Tendsto.mul hu' (Or.inr ENNReal.zero_ne_top) hv' (Or.inr ENNReal.zero_ne_top)
    simpa using (h1.add h2).add h3
  rw [tendsto_iff_edist_tendsto_0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Eventually.of_forall fun _ => zero_le) ?_
  have hfin : ∀ᶠ s in l, lintSq (u s - u₀) < ⊤ ∧ lintSq (v s - v₀) < ⊤ :=
    (hu.eventually_lt_const ENNReal.zero_lt_top).and (hv.eventually_lt_const ENNReal.zero_lt_top)
  filter_upwards [hmeas, hfin] with s hs hsf
  have hdum : AEStronglyMeasurable (u s - u₀) volume := hs.1.sub hu₀
  have hdvm : AEStronglyMeasurable (v s - v₀) volume := hs.2.sub hv₀
  have e : (fun η => u s η * v s η) = fun η => u₀ η * v₀ η +
      ((u s - u₀) η * v₀ η + u₀ η * (v s - v₀) η + (u s - u₀) η * (v s - v₀) η) := by
    funext η; simp only [Pi.sub_apply]; ring
  have i1 := integrable_mul_of_lintSq hu₀ hv₀ hu₀2 hv₀2
  have i2 := integrable_mul_of_lintSq hdum hv₀ hsf.1.ne hv₀2
  have i3 := integrable_mul_of_lintSq hu₀ hdvm hu₀2 hsf.2.ne
  have i4 := integrable_mul_of_lintSq hdum hdvm hsf.1.ne hsf.2.ne
  have i23 : Integrable (fun η => (u s - u₀) η * v₀ η + u₀ η * (v s - v₀) η) volume := i2.add i3
  have i234 : Integrable (fun η => (u s - u₀) η * v₀ η + u₀ η * (v s - v₀) η +
      (u s - u₀) η * (v s - v₀) η) volume := i23.add i4
  rw [e, integral_add i1 i234, integral_add i23 i4, integral_add i2 i3,
    edist_eq_enorm_sub, add_sub_cancel_left]
  refine (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact enorm_integral_mul_le _ _ hdum hv₀
  · exact enorm_integral_mul_le _ _ hu₀ hdvm
  · exact enorm_integral_mul_le _ _ hdum hdvm

private lemma one_le_hsWeight_one (ξ : Space) : (1 : ℝ) ≤ hsWeight 1 ξ := by
  simp only [hsWeight, pow_one]
  exact le_add_of_nonneg_right (by positivity)

private lemma lintSq_apply_le (f : Space → CSpace) (j : Fin 3) :
    lintSq (fun η => f η j) ≤ hsNormSq 1 f := by
  refine lintegral_mono fun η => ?_
  have h1 : ‖f η j‖ₑ ≤ ‖f η‖ₑ := PiLp.enorm_apply_le _ _
  have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hsWeight 1 η) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (one_le_hsWeight_one η)
  calc ‖f η j‖ₑ ^ 2 ≤ ‖f η‖ₑ ^ 2 := by gcongr
    _ = 1 * ‖f η‖ₑ ^ 2 := (one_mul _).symm
    _ ≤ _ := by gcongr

private lemma enorm_freq_mul_sq_le (f : Space → CSpace) (i j : Fin 3) (x : Space) :
    ‖2 * (π : ℂ) * Complex.I * ((x j : ℝ) : ℂ) * f x i‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * π ^ 2) * (ENNReal.ofReal (hsWeight 1 x) * ‖f x‖ₑ ^ 2) := by
  have hw : 0 ≤ hsWeight 1 x := le_trans zero_le_one (one_le_hsWeight_one x)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hx : ‖x j‖ ≤ ‖x‖ := PiLp.norm_apply_le x j
  have hf : ‖f x i‖ ≤ ‖f x‖ := PiLp.norm_apply_le _ i
  have e : ‖2 * (π : ℂ) * Complex.I * ((x j : ℝ) : ℂ) * f x i‖ = 2 * π * ‖x j‖ * ‖f x i‖ := by
    simp [abs_of_pos Real.pi_pos]
  rw [e]
  simp only [hsWeight, pow_one]
  have hxj : ‖x j‖ ^ 2 ≤ 1 + ‖x‖ ^ 2 := by nlinarith [norm_nonneg (x j)]
  have hfi : ‖f x i‖ ^ 2 ≤ ‖f x‖ ^ 2 := by gcongr
  calc (2 * π * ‖x j‖ * ‖f x i‖) ^ 2 = 4 * π ^ 2 * (‖x j‖ ^ 2 * ‖f x i‖ ^ 2) := by ring
    _ ≤ 4 * π ^ 2 * ((1 + ‖x‖ ^ 2) * ‖f x‖ ^ 2) := by gcongr

private lemma lintSq_shift_le (f : Space → CSpace) (ξ : Space) (i j : Fin 3) :
    lintSq (fun η => 2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i) ≤
      ENNReal.ofReal (4 * π ^ 2) * hsNormSq 1 f := by
  calc lintSq (fun η => 2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i)
        = ∫⁻ η, (fun x : Space => ‖2 * (π : ℂ) * Complex.I * ((x j : ℝ) : ℂ) * f x i‖ₑ ^ 2)
          (ξ - η) := rfl
    _ = ∫⁻ x, ‖2 * (π : ℂ) * Complex.I * ((x j : ℝ) : ℂ) * f x i‖ₑ ^ 2 :=
        lintegral_sub_left_eq_self (μ := (volume : Measure Space))
          (fun x : Space => ‖2 * (π : ℂ) * Complex.I * ((x j : ℝ) : ℂ) * f x i‖ₑ ^ 2) ξ
    _ ≤ ∫⁻ x, ENNReal.ofReal (4 * π ^ 2) * (ENNReal.ofReal (hsWeight 1 x) * ‖f x‖ₑ ^ 2) :=
        lintegral_mono fun x => enorm_freq_mul_sq_le f i j x
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private lemma aesm_apply {f : Space → CSpace} (hf : AEStronglyMeasurable f volume) (j : Fin 3) :
    AEStronglyMeasurable (fun η => f η j) volume :=
  (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j).comp_aestronglyMeasurable hf

private lemma aesm_shift {f : Space → CSpace} (hf : AEStronglyMeasurable f volume) (ξ : Space)
    (i j : Fin 3) : AEStronglyMeasurable
      (fun η => 2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * f (ξ - η) i) volume := by
  have h1 : AEStronglyMeasurable (fun η => f (ξ - η)) volume :=
    hf.comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure Space) ξ)
  have h2 : AEStronglyMeasurable (fun η => f (ξ - η) i) volume :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) i).comp_aestronglyMeasurable h1
  have h3 : Continuous (fun η : Space => 2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ)) := by
    fun_prop
  exact h3.aestronglyMeasurable.mul h2

private lemma hsWeight_mono {m n : ℕ} (hmn : n ≤ m) (ξ : Space) : hsWeight n ξ ≤ hsWeight m ξ :=
  pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hmn

private lemma hsNormSq_mono {m n : ℕ} (hmn : n ≤ m) (f : Space → CSpace) :
    hsNormSq n f ≤ hsNormSq m f :=
  lintegral_mono fun ξ => by gcongr; exact hsWeight_mono hmn ξ

private lemma continuousOn_convC {F : ℝ → Space → CSpace} {a b : ℝ} (hF : IsHsCurve 1 F a b)
    (ξ : Space) (i j : Fin 3) :
    ContinuousOn (fun s => convC (fun η => F s η j)
      (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * F s η i) ξ) (Icc a b) := by
  unfold IsHsCurve at hF
  intro s₀ hs₀
  obtain ⟨hm₀, hfin₀⟩ := hF.1 s₀ hs₀
  have hd := hF.2 s₀ hs₀
  have hmem : ∀ᶠ s in 𝓝[Icc a b] s₀, s ∈ Icc a b := self_mem_nhdsWithin
  simp only [ContinuousWithinAt, convC]
  refine tendsto_integral_mul (u := fun s η => F s η j)
    (v := fun s η => 2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * F s (ξ - η) i)
    (aesm_apply hm₀ j) (aesm_shift hm₀ ξ i j) ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hmem] with s hs
    exact ⟨aesm_apply (hF.1 s hs).1 j, aesm_shift (hF.1 s hs).1 ξ i j⟩
  · exact (lt_of_le_of_lt (lintSq_apply_le _ j) hfin₀).ne
  · exact (lt_of_le_of_lt (lintSq_shift_le _ ξ i j)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin₀)).ne
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd (fun _ => zero_le)
      fun s => ?_
    have e : ((fun η => F s η j) - fun η => F s₀ η j) = fun η => (F s - F s₀) η j := by
      funext η; simp
    simp only [e]
    exact lintSq_apply_le _ j
  · have hd' := ENNReal.Tendsto.const_mul hd (Or.inr (ENNReal.ofReal_ne_top (r := 4 * π ^ 2)))
    rw [mul_zero] at hd'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd' (fun _ => zero_le)
      fun s => ?_
    have e : ((fun η => 2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * F s (ξ - η) i) -
        fun η => 2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * F s₀ (ξ - η) i) =
        fun η => 2 * (π : ℂ) * Complex.I * (((ξ - η) j : ℝ) : ℂ) * (F s - F s₀) (ξ - η) i := by
      funext η; simp only [Pi.sub_apply, PiLp.sub_apply]; ring
    simp only [e]
    exact lintSq_shift_le _ ξ i j

private lemma continuous_divFreeC (ξ : Space) : Continuous (divFreeC ξ) := by
  unfold divFreeC
  fun_prop

private lemma continuousOn_nonlinSymbol {F : ℝ → Space → CSpace} {a b : ℝ}
    (hF : IsHsCurve 1 F a b) (ξ : Space) :
    ContinuousOn (fun s => nonlinSymbol (F s) ξ) (Icc a b) := by
  have hA : ContinuousOn (fun s => advectionSymbol (F s) ξ) (Icc a b) := by
    have h : ContinuousOn (fun s => fun i => ∑ j, convC (fun η => F s η j)
        (fun η => 2 * (π : ℂ) * Complex.I * ((η j : ℝ) : ℂ) * F s η i) ξ) (Icc a b) :=
      continuousOn_pi.2 fun i => continuousOn_finsetSum _ fun j _ => continuousOn_convC hF ξ i j
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp_continuousOn h
  exact ((continuous_divFreeC ξ).comp_continuousOn hA).neg

private lemma continuous_heatFactor (t : ℝ) (ξ : Space) :
    Continuous (fun s : ℝ => ((heatSymbol (t - s) ξ : ℝ) : ℂ)) := by
  unfold heatSymbol
  fun_prop

private lemma heatSymbol_mul (t b s : ℝ) (ξ : Space) :
    ((heatSymbol (t - b) ξ : ℝ) : ℂ) * ((heatSymbol (b - s) ξ : ℝ) : ℂ) =
      ((heatSymbol (t - s) ξ : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  simp only [heatSymbol, ← Real.exp_add]
  congr 1
  ring

private lemma isHsCurve_mono_aux {m n : ℕ} (hmn : n ≤ m) {F : ℝ → Space → CSpace} {a b : ℝ}
    (hF : IsHsCurve m F a b) : IsHsCurve n F a b := by
  unfold IsHsCurve at hF ⊢
  exact ⟨fun t ht => ⟨(hF.1 t ht).1, lt_of_le_of_lt (hsNormSq_mono hmn _) (hF.1 t ht).2⟩,
    fun t₀ ht₀ => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hF.2 t₀ ht₀)
      (fun _ => zero_le) (fun _ => hsNormSq_mono hmn _)⟩

theorem isHsCurve_concat {m : ℕ} {F G : ℝ → Space → CSpace} {a b c : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) (hF : IsHsCurve m F a b) (hG : IsHsCurve m G b c) (hFG : G b = F b) :
    IsHsCurve m (fun t => if t ≤ b then F t else G t) a c := by
  unfold IsHsCurve at hF hG ⊢
  have hHF : ∀ t ∈ Icc a b, (if t ≤ b then F t else G t) = F t := fun t ht => if_pos ht.2
  have hHG : ∀ t ∈ Icc b c, (if t ≤ b then F t else G t) = G t := by
    intro t ht
    by_cases h : t ≤ b
    · rw [if_pos h, le_antisymm h ht.1, hFG]
    · rw [if_neg h]
  have hsplit : Icc a c = Icc a b ∪ Icc b c := (Icc_union_Icc_eq_Icc hab hbc).symm
  refine ⟨fun t ht => ?_, fun t₀ ht₀ => ?_⟩
  · beta_reduce
    rw [hsplit] at ht
    rcases ht with ht | ht
    · rw [hHF t ht]; exact hF.1 t ht
    · rw [hHG t ht]; exact hG.1 t ht
  · rw [hsplit, nhdsWithin_union]
    refine Tendsto.sup ?_ ?_
    · by_cases h₀ : t₀ ∈ Icc a b
      · refine (hF.2 t₀ h₀).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hHF t ht, hHF t₀ h₀]
      · have h : 𝓝[Icc a b] t₀ = ⊥ :=
          notMem_closure_iff_nhdsWithin_eq_bot.1 (by rwa [closure_Icc])
        rw [h]; exact tendsto_bot
    · by_cases h₀ : t₀ ∈ Icc b c
      · refine (hG.2 t₀ h₀).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hHG t ht, hHG t₀ h₀]
      · have h : 𝓝[Icc b c] t₀ = ⊥ :=
          notMem_closure_iff_nhdsWithin_eq_bot.1 (by rwa [closure_Icc])
        rw [h]; exact tendsto_bot

theorem isVarConstSymbol_concat {F G : ℝ → Space → CSpace} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hF3 : IsHsCurve 3 F a b) (hG3 : IsHsCurve 3 G b c)
    (hF : IsVarConstSymbol F a b) (hG : IsVarConstSymbol G b c) (hFG : G b = F b) :
    IsVarConstSymbol (fun t => if t ≤ b then F t else G t) a c := by
  have hF1 := isHsCurve_mono_aux (by norm_num : 1 ≤ 3) hF3
  have hG1 := isHsCurve_mono_aux (by norm_num : 1 ≤ 3) hG3
  have hHG : ∀ s ∈ Icc b c, (if s ≤ b then F s else G s) = G s := by
    intro s hs
    by_cases h : s ≤ b
    · rw [if_pos h, le_antisymm h hs.1, hFG]
    · rw [if_neg h]
  intro t ht ξ
  simp only [if_pos hab]
  by_cases htb : t ≤ b
  · rw [if_pos htb, hF t ⟨ht.1, htb⟩ ξ]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [if_pos (hs.2.trans htb)]
  · have hbt : b ≤ t := (not_le.1 htb).le
    have hI1 : IntervalIntegrable (fun s => ((heatSymbol (t - s) ξ : ℝ) : ℂ) •
        nonlinSymbol (if s ≤ b then F s else G s) ξ) volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]
      refine (((continuous_heatFactor t ξ).continuousOn).smul
        (continuousOn_nonlinSymbol hF1 ξ)).congr fun s hs => ?_
      simp only [if_pos hs.2]
      rfl
    have hI2 : IntervalIntegrable (fun s => ((heatSymbol (t - s) ξ : ℝ) : ℂ) •
        nonlinSymbol (if s ≤ b then F s else G s) ξ) volume b t := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hbt]
      refine ((((continuous_heatFactor t ξ).continuousOn).smul
        (continuousOn_nonlinSymbol hG1 ξ)).mono (Icc_subset_Icc le_rfl ht.2)).congr
        fun s hs => ?_
      simp only [hHG s ⟨hs.1, hs.2.trans ht.2⟩]
      rfl
    have e1 : ∫ s in a..b, ((heatSymbol (t - s) ξ : ℝ) : ℂ) •
        nonlinSymbol (if s ≤ b then F s else G s) ξ =
        ∫ s in a..b, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hab] at hs
      simp only [if_pos hs.2]
    have e2 : ∫ s in b..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) •
        nonlinSymbol (if s ≤ b then F s else G s) ξ =
        ∫ s in b..t, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (G s) ξ := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hbt] at hs
      simp only [hHG s ⟨hs.1, hs.2.trans ht.2⟩]
    have e3 : ((heatSymbol (t - b) ξ : ℝ) : ℂ) •
        ∫ s in a..b, ((heatSymbol (b - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ =
        ∫ s in a..b, ((heatSymbol (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ := by
      rw [← intervalIntegral.integral_smul]
      congr 1
      funext s
      rw [smul_smul, heatSymbol_mul]
    rw [if_neg htb, hG t ⟨hbt, ht.2⟩ ξ, hFG, hF b ⟨hab, le_rfl⟩ ξ,
      ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, e1, e2, smul_add, smul_smul,
      heatSymbol_mul, e3, add_assoc]

theorem isHsCurve_mono {m n : ℕ} (hmn : n ≤ m) {F : ℝ → Space → CSpace} {a b : ℝ}
    (hF : IsHsCurve m F a b) : IsHsCurve n F a b :=
  isHsCurve_mono_aux hmn hF

theorem isHsCurve_restrict {m : ℕ} {F : ℝ → Space → CSpace} {a b a' b' : ℝ}
    (ha : a ≤ a') (hb : b' ≤ b) (hF : IsHsCurve m F a b) : IsHsCurve m F a' b' := by
  unfold IsHsCurve at hF ⊢
  have hs : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha hb
  exact ⟨fun t ht => hF.1 t (hs ht),
    fun t₀ ht₀ => (hF.2 t₀ (hs ht₀)).mono_left (nhdsWithin_mono _ hs)⟩

theorem isVarConstSymbol_restrict {F : ℝ → Space → CSpace} {a b b' : ℝ} (hb : b' ≤ b)
    (hF : IsVarConstSymbol F a b) : IsVarConstSymbol F a b' :=
  fun t ht ξ => hF t ⟨ht.1, ht.2.trans hb⟩ ξ

end Breakdown.SmoothFlow
