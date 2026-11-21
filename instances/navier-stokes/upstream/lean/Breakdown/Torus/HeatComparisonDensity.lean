import Breakdown.Torus.HeatComparisonStatements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic.SourceDensity.Internal

open Breakdown.Periodic

theorem norm_cexp_sub_le (a b : ℝ) :
    ‖Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I)‖ ≤ |a - b| := by
  have h : Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I) =
      Complex.exp (↑b * Complex.I) * (Complex.exp (Complex.I * ↑(a - b)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem norm_complexifyVec_eq (z : Space) : ‖Freq.complexifyVec z‖ = ‖z‖ := by
  simp [EuclideanSpace.norm_eq, Freq.complexifyVec]

theorem inner_eq_sum (ξ : Space) (c : Coef) :
    (∑ i, ((ξ i : ℝ) : ℂ) * c i) = inner ℂ (Freq.complexifyVec ξ) c := by
  simp [PiLp.inner_apply, Freq.complexifyVec, mul_comm]

theorem l1_bound (A : Freq.L2R) (b' : ℝ)
    (hA : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) :
    Integrable (⇑A) ∧
      ∫ x, ‖A x‖ ≤ (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal *
        (eLpNorm (A : Space → Space) (3 / 2) volume).toReal := by
  set s := Metric.closedBall (0 : Space) |b'| with hsdef
  have hs : ∀ᵐ y ∂volume, y ∉ s → A y = 0 := hA.mono fun _ h hy =>
    h fun hy' => hy (Metric.closedBall_subset_closedBall (le_abs_self b') hy')
  have hind : (⇑A) =ᵐ[volume] s.indicator ⇑A := by
    filter_upwards [hs] with y hy
    by_cases h : y ∈ s
    · simp [h]
    · simp [h, hy h]
  have hmeas : AEStronglyMeasurable (⇑A) volume := Lp.aestronglyMeasurable A
  have hres : ∀ p : ℝ≥0∞, eLpNorm (⇑A) p volume = eLpNorm (⇑A) p (volume.restrict s) := fun p => by
    rw [eLpNorm_congr_ae hind, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  have e2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 3 / 2)
    (by rw [ENNReal.le_div_iff_mul_le (by simp) (by simp)]; norm_num)
    (hmeas.restrict (s := s)) (μ := volume.restrict s)
  have e5 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 3 / 2) (q := 2)
    (ENNReal.div_le_of_le_mul (by norm_num))
    (hmeas.restrict (s := s)) (μ := volume.restrict s)
  rw [Measure.restrict_apply_univ] at e2 e5
  have hx1 : (1 / (1 : ℝ≥0∞).toReal - 1 / (3 / 2 : ℝ≥0∞).toReal) = (1 / 3 : ℝ) := by
    rw [ENNReal.toReal_div]
    norm_num
  have hx2 : (1 / (3 / 2 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 6 : ℝ) := by
    rw [ENNReal.toReal_div]
    norm_num
  rw [hx1] at e2
  rw [hx2] at e5
  have hvol : volume s ≠ ⊤ := measure_closedBall_lt_top.ne
  have hfin3 : volume s ^ (1 / 3 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 3) hvol
  have hfin6 : volume s ^ (1 / 6 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 6) hvol
  have hN : eLpNorm (⇑A) (3 / 2) volume ≠ ⊤ := by
    rw [hres]
    refine (lt_of_le_of_lt e5 (ENNReal.mul_lt_top ?_ hfin6.lt_top)).ne
    exact lt_of_le_of_lt (eLpNorm_mono_measure _ Measure.restrict_le_self)
      (Lp.eLpNorm_ne_top A).lt_top
  have key : eLpNorm (⇑A) 1 volume ≤ eLpNorm (⇑A) (3 / 2) volume * volume s ^ (1 / 3 : ℝ) := by
    rw [hres 1, hres (3 / 2)]
    exact e2
  have hlt : eLpNorm (⇑A) 1 volume < ⊤ :=
    key.trans_lt (ENNReal.mul_lt_top hN.lt_top hfin3.lt_top)
  refine ⟨memLp_one_iff_integrable.mp ⟨hmeas, hlt⟩, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hmeas, ← eLpNorm_one_eq_lintegral_enorm]
  calc (eLpNorm (⇑A) 1 volume).toReal ≤
        (eLpNorm (⇑A) (3 / 2) volume * volume s ^ (1 / 3 : ℝ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hN hfin3) key
    _ = _ := by rw [ENNReal.toReal_mul, mul_comm]

theorem freqTrVec_eq (A : Space → Space) (ξ : Space) :
    freqTrVec A ξ = ∫ x, Complex.exp (↑(-2 * π * inner ℝ x ξ) * Complex.I) • Freq.complexifyVec (A x) := by
  unfold freqTrVec
  rw [Real.fourier_eq']

theorem kern_meas (A : Freq.L2R) (ξ : Space) :
    AEStronglyMeasurable (fun x => Complex.exp (↑(-2 * π * inner ℝ x ξ) * Complex.I) •
      Freq.complexifyVec ((A : Space → Space) x)) volume :=
  (by fun_prop : Continuous fun x : Space =>
      Complex.exp (↑(-2 * π * inner ℝ x ξ) * Complex.I)).aestronglyMeasurable.smul
    (Freq.complexifyVec.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable A))

theorem norm_kern (v : Space) (ξ x : Space) :
    ‖Complex.exp (↑(-2 * π * inner ℝ x ξ) * Complex.I) • Freq.complexifyVec v‖ = ‖v‖ := by
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_complexifyVec_eq]

theorem ae_zero_abs (A : Freq.L2R) (b' : ℝ)
    (hA : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) :
    ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) |b'| → A y = 0 :=
  hA.mono fun _ h hy => h fun hy' => hy (Metric.closedBall_subset_closedBall (le_abs_self b') hy')

theorem freqTrVec_bound (A : Freq.L2R) (b' : ℝ)
    (hA : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) (hAn : (eLpNorm (A : Space → Space) (3 / 2) volume).toReal ≤ 1)
    (ξ : Space) :
    ‖freqTrVec (⇑A) ξ‖ ≤ (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal := by
  rw [freqTrVec_eq]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp_rw [norm_kern]
  exact (l1_bound A b' hA).2.trans (mul_le_of_le_one_right ENNReal.toReal_nonneg hAn)

theorem abs_neg_two_pi_mul (t : ℝ) : |-2 * π * t| = 2 * π * |t| := by
  rw [abs_mul, abs_of_neg (by linarith [pi_pos] : -2 * π < 0)]
  ring

theorem freqTrVec_slope (A : Freq.L2R) (b' : ℝ)
    (hA : ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b' → A y = 0) (hAn : (eLpNorm (A : Space → Space) (3 / 2) volume).toReal ≤ 1)
    (ξ ξ' : Space) :
    ‖freqTrVec (⇑A) ξ - freqTrVec (⇑A) ξ'‖ ≤
      2 * π * |b'| * (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal *
        ‖ξ - ξ'‖ := by
  obtain ⟨hint, hl1⟩ := l1_bound A b' hA
  have i1 := Integrable.mono' hint.norm (kern_meas A ξ) (ae_of_all _ fun x => (norm_kern _ ξ x).le)
  have i2 := Integrable.mono' hint.norm (kern_meas A ξ') (ae_of_all _ fun x => (norm_kern _ ξ' x).le)
  rw [freqTrVec_eq, freqTrVec_eq, ← integral_sub i1 i2]
  have hs := ae_zero_abs A b' hA
  refine (norm_integral_le_of_norm_le (g := fun x => 2 * π * |b'| * ‖ξ - ξ'‖ * ‖A x‖)
    (hint.norm.const_mul _) ?_).trans ?_
  · filter_upwards [hs] with x hx
    by_cases hxs : x ∈ Metric.closedBall (0 : Space) |b'|
    · rw [← sub_smul, norm_smul, norm_complexifyVec_eq]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine (norm_cexp_sub_le _ _).trans ?_
      have h1 : -2 * π * inner ℝ x ξ - -2 * π * inner ℝ x ξ' = -2 * π * inner ℝ x (ξ - ξ') := by
        rw [inner_sub_right]
        ring
      rw [h1, abs_neg_two_pi_mul]
      have h2 := abs_real_inner_le_norm x (ξ - ξ')
      have h3 : ‖x‖ ≤ |b'| := mem_closedBall_zero_iff.mp hxs
      calc 2 * π * |inner ℝ x (ξ - ξ')| ≤ 2 * π * (|b'| * ‖ξ - ξ'‖) := by
            gcongr
            exact h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
        _ = _ := by ring
    · rw [hx hxs]
      simp
  · rw [integral_const_mul]
    calc 2 * π * |b'| * ‖ξ - ξ'‖ * ∫ x, ‖A x‖ ≤
          2 * π * |b'| * ‖ξ - ξ'‖ * (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal := by
          gcongr
          exact hl1.trans (mul_le_of_le_one_right ENNReal.toReal_nonneg hAn)
      _ = _ := by ring

theorem expChar_eq (y ξ : Space) :
    expChar y ξ = Complex.exp (↑(2 * π * inner ℝ ξ y) * Complex.I) := by
  unfold expChar
  congr 1
  push_cast
  ring

theorem norm_expChar (y ξ : Space) : ‖expChar y ξ‖ = 1 := by
  rw [expChar_eq, Complex.norm_exp_ofReal_mul_I]

theorem expChar_slope {b : ℝ} {y : Space} (hy : ‖y‖ ≤ b) (ξ ξ' : Space) :
    ‖expChar y ξ - expChar y ξ'‖ ≤ 2 * π * |b| * ‖ξ - ξ'‖ := by
  rw [expChar_eq, expChar_eq]
  refine (norm_cexp_sub_le _ _).trans ?_
  have h0 : 2 * π * inner ℝ ξ y - 2 * π * inner ℝ ξ' y = 2 * π * inner ℝ (ξ - ξ') y := by
    rw [inner_sub_left]
    ring
  rw [h0, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have h1 := abs_real_inner_le_norm (ξ - ξ') y
  have h2 : ‖y‖ ≤ |b| := hy.trans (le_abs_self b)
  calc 2 * π * |inner ℝ (ξ - ξ') y| ≤ 2 * π * (‖ξ - ξ'‖ * |b|) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    _ = _ := by ring

theorem exp_neg_sub_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.exp (-s) - Real.exp (-t)| ≤ |s - t| := by
  have key : ∀ s t : ℝ, 0 ≤ s → s ≤ t → |Real.exp (-s) - Real.exp (-t)| ≤ |s - t| := by
    intro s t hs hst
    have h1 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
      rw [← Real.exp_add]
      ring_nf
    have h2 := Real.add_one_le_exp (-(t - s))
    have h3 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h4 : 0 < Real.exp (-s) := Real.exp_pos _
    have h5 : Real.exp (-(t - s)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [h1, abs_of_nonneg (by nlinarith), abs_of_nonpos (by linarith)]
    nlinarith
  rcases le_total s t with h | h
  · exact key s t hs h
  · rw [abs_sub_comm, abs_sub_comm s]
    exact key t s ht h

theorem sq_norm_sub_le {R : ℝ} {ξ ξ' : Space} (hξ : ‖ξ‖ ≤ R) (hξ' : ‖ξ'‖ ≤ R) :
    |‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2| ≤ 2 * R * ‖ξ - ξ'‖ := by
  have h0 : ‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2 = (‖ξ‖ - ‖ξ'‖) * (‖ξ‖ + ‖ξ'‖) := by ring
  rw [h0, abs_mul]
  have a1 := abs_norm_sub_norm_le ξ ξ'
  have a2 : |‖ξ‖ + ‖ξ'‖| ≤ 2 * R := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  calc _ ≤ ‖ξ - ξ'‖ * (2 * R) := mul_le_mul a1 a2 (abs_nonneg _) (norm_nonneg _)
    _ = _ := by ring

theorem heatFactor_nonneg (τ : ℝ) (ξ : Space) : 0 ≤ Freq.heatFactor τ ξ :=
  (Real.exp_pos _).le

theorem heatFactor_le_one (τ : ℝ) (ξ : Space) : Freq.heatFactor τ ξ ≤ 1 := by
  unfold Freq.heatFactor
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by have := le_max_right τ 0; positivity))

theorem heatFactor_slope {ε τ R : ℝ} (hε : 0 < ε) (hτ : τ ≤ ε⁻¹) {ξ ξ' : Space}
    (hξ : ‖ξ‖ ≤ R) (hξ' : ‖ξ'‖ ≤ R) :
    ‖Freq.heatFactor τ ξ - Freq.heatFactor τ ξ'‖ ≤ 4 * π ^ 2 * ε⁻¹ * (2 * R) * ‖ξ - ξ'‖ := by
  have hm0 : 0 ≤ max τ 0 := le_max_right _ _
  have hm : max τ 0 ≤ ε⁻¹ := max_le hτ (inv_nonneg.mpr hε.le)
  rw [Real.norm_eq_abs]
  unfold Freq.heatFactor
  refine (exp_neg_sub_le (by positivity) (by positivity)).trans ?_
  have h0 : 4 * π ^ 2 * max τ 0 * ‖ξ‖ ^ 2 - 4 * π ^ 2 * max τ 0 * ‖ξ'‖ ^ 2 =
      4 * π ^ 2 * max τ 0 * (‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2) := by ring
  rw [h0, abs_mul, abs_of_nonneg (by positivity)]
  have hd := sq_norm_sub_le hξ hξ'
  calc 4 * π ^ 2 * max τ 0 * |‖ξ‖ ^ 2 - ‖ξ'‖ ^ 2| ≤ 4 * π ^ 2 * ε⁻¹ * (2 * R * ‖ξ - ξ'‖) :=
        mul_le_mul (by gcongr) hd (abs_nonneg _)
          (mul_nonneg (by positivity) (inv_nonneg.mpr hε.le))
    _ = _ := by ring

theorem heatFactor_decay {ε τ : ℝ} (hε : 0 < ε) (hτ : ε ≤ τ) (ξ : Space) :
    Freq.heatFactor τ ξ * (1 + ‖ξ‖) ^ 6 ≤ 8 * (1 + 3 / (4 * π ^ 2 * ε)) ^ 3 := by
  have ha : 0 < 4 * π ^ 2 * ε := by positivity
  set a := 4 * π ^ 2 * ε with hadef
  set u := ‖ξ‖ with hudef
  have hu : 0 ≤ u := norm_nonneg _
  have h1 : Freq.heatFactor τ ξ ≤ Real.exp (-(a * u ^ 2)) := by
    unfold Freq.heatFactor
    apply Real.exp_le_exp.mpr
    have : ε ≤ max τ 0 := le_max_of_le_left hτ
    apply neg_le_neg
    rw [hadef]
    gcongr
  have h2 : (1 + u) ^ 2 ≤ 2 * (1 + 3 / a) * Real.exp (a * u ^ 2 / 3) := by
    have e := Real.add_one_le_exp (a * u ^ 2 / 3)
    have h3a : 0 ≤ 3 / a := by positivity
    have hau : 0 ≤ a * u ^ 2 / 3 := by positivity
    have hc : 3 / a * (a * u ^ 2 / 3) = u ^ 2 := by field_simp
    have h4 : 1 + u ^ 2 ≤ (1 + 3 / a) * (a * u ^ 2 / 3 + 1) := by nlinarith
    have h5 : (1 + u) ^ 2 ≤ 2 * (1 + u ^ 2) := by nlinarith [sq_nonneg (1 - u)]
    calc (1 + u) ^ 2 ≤ 2 * ((1 + 3 / a) * (a * u ^ 2 / 3 + 1)) := by linarith
      _ ≤ 2 * ((1 + 3 / a) * Real.exp (a * u ^ 2 / 3)) := by gcongr
      _ = _ := by ring
  have h3 : (1 + u) ^ 6 ≤ 8 * (1 + 3 / a) ^ 3 * Real.exp (a * u ^ 2) := by
    have := pow_le_pow_left₀ (by positivity) h2 3
    calc (1 + u) ^ 6 = ((1 + u) ^ 2) ^ 3 := by ring
      _ ≤ (2 * (1 + 3 / a) * Real.exp (a * u ^ 2 / 3)) ^ 3 := this
      _ = 8 * (1 + 3 / a) ^ 3 * Real.exp (a * u ^ 2 / 3) ^ 3 := by ring
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 2
        push_cast
        ring
  calc Freq.heatFactor τ ξ * (1 + u) ^ 6 ≤
        Real.exp (-(a * u ^ 2)) * (8 * (1 + 3 / a) ^ 3 * Real.exp (a * u ^ 2)) :=
        mul_le_mul h1 h3 (by positivity) (Real.exp_pos _).le
    _ = _ := by
      rw [Real.exp_neg]
      field_simp

theorem smul_slope {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    {a a' : 𝕜} {u u' : E} {M₁ M₂ L₁ L₂ d : ℝ} (ha' : ‖a'‖ ≤ M₁) (hu : ‖u‖ ≤ M₂)
    (hda : ‖a - a'‖ ≤ L₁ * d) (hdu : ‖u - u'‖ ≤ L₂ * d) :
    ‖a • u - a' • u'‖ ≤ (L₁ * M₂ + M₁ * L₂) * d := by
  have h0 : a • u - a' • u' = (a - a') • u + a' • (u - u') := by
    rw [sub_smul, smul_sub]
    abel
  rw [h0]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  calc ‖a - a'‖ * ‖u‖ + ‖a'‖ * ‖u - u'‖ ≤ L₁ * d * M₂ + M₁ * (L₂ * d) :=
        add_le_add (mul_le_mul hda hu (norm_nonneg _) ((norm_nonneg _).trans hda))
          (mul_le_mul ha' hdu (norm_nonneg _) ((norm_nonneg _).trans ha'))
    _ = _ := by ring

theorem inner_slope {a a' c c' : Coef} {M₁ M₂ L₁ L₂ d : ℝ} (ha' : ‖a'‖ ≤ M₁) (hc : ‖c‖ ≤ M₂)
    (hda : ‖a - a'‖ ≤ L₁ * d) (hdc : ‖c - c'‖ ≤ L₂ * d) :
    ‖inner ℂ a c - inner ℂ a' c'‖ ≤ (L₁ * M₂ + M₁ * L₂) * d := by
  have h0 : inner ℂ a c - inner ℂ a' c' = inner ℂ (a - a') c + inner ℂ a' (c - c') := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [h0]
  refine (norm_add_le _ _).trans ?_
  calc ‖inner ℂ (a - a') c‖ + ‖inner ℂ a' (c - c')‖ ≤ ‖a - a'‖ * ‖c‖ + ‖a'‖ * ‖c - c'‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ L₁ * d * M₂ + M₁ * (L₂ * d) :=
        add_le_add (mul_le_mul hda hc (norm_nonneg _) ((norm_nonneg _).trans hda))
          (mul_le_mul ha' hdc (norm_nonneg _) ((norm_nonneg _).trans ha'))
    _ = _ := by ring

theorem divFreeVec_norm_le (ξ : Space) (c : Coef) : ‖divFreeVec ξ c‖ ≤ 2 * ‖c‖ := by
  unfold divFreeVec
  split_ifs with h
  · linarith [norm_nonneg c]
  refine (norm_sub_le _ _).trans ?_
  have hξ : 0 < ‖ξ‖ := norm_pos_iff.mpr h
  have hi := norm_inner_le_norm (𝕜 := ℂ) (Freq.complexifyVec ξ) c
  rw [norm_complexifyVec_eq] at hi
  have h1 : ‖((∑ i, ((ξ i : ℝ) : ℂ) * c i) / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • Freq.complexifyVec ξ‖ ≤ ‖c‖ := by
    rw [inner_eq_sum, norm_smul, norm_div, Complex.norm_real, norm_complexifyVec_eq,
      Real.norm_of_nonneg (by positivity)]
    calc ‖inner ℂ (Freq.complexifyVec ξ) c‖ / ‖ξ‖ ^ 2 * ‖ξ‖ ≤ ‖ξ‖ * ‖c‖ / ‖ξ‖ ^ 2 * ‖ξ‖ := by
          gcongr
      _ = ‖c‖ := by field_simp
  linarith

theorem divFreeVec_eq {ξ : Space} (hξ : ξ ≠ 0) (c : Coef) :
    divFreeVec ξ c = c - inner ℂ (Freq.complexifyVec ξ) c •
      ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) • Freq.complexifyVec ξ) := by
  unfold divFreeVec
  rw [if_neg hξ, inner_eq_sum, smul_smul, div_eq_mul_inv, Complex.ofReal_inv]

theorem invSq_slope {r R : ℝ} (hr : 0 < r) {ξ ξ' : Space} (h1 : r ≤ ‖ξ‖) (h2 : ‖ξ‖ ≤ R)
    (h1' : r ≤ ‖ξ'‖) (h2' : ‖ξ'‖ ≤ R) :
    ‖((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) - ((((‖ξ'‖ ^ 2)⁻¹ : ℝ) : ℂ))‖ ≤
      2 * R / (r ^ 2 * r ^ 2) * ‖ξ - ξ'‖ := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hx : 0 < ‖ξ‖ ^ 2 := by have : 0 < ‖ξ‖ := hr.trans_le h1; positivity
  have hy : 0 < ‖ξ'‖ ^ 2 := by have : 0 < ‖ξ'‖ := hr.trans_le h1'; positivity
  rw [inv_sub_inv hx.ne' hy.ne', abs_div, abs_of_pos (mul_pos hx hy), div_le_iff₀ (mul_pos hx hy)]
  have hd : |‖ξ'‖ ^ 2 - ‖ξ‖ ^ 2| ≤ 2 * R * ‖ξ - ξ'‖ := by
    rw [abs_sub_comm]
    exact sq_norm_sub_le h2 h2'
  have hxy : r ^ 2 * r ^ 2 ≤ ‖ξ‖ ^ 2 * ‖ξ'‖ ^ 2 := by gcongr
  have hRd : 0 ≤ 2 * R * ‖ξ - ξ'‖ := (abs_nonneg _).trans hd
  have hr4 : 0 < r ^ 2 * r ^ 2 := by positivity
  have hk : 0 ≤ 2 * R / (r ^ 2 * r ^ 2) * ‖ξ - ξ'‖ := by
    rw [div_mul_eq_mul_div]
    exact div_nonneg hRd hr4.le
  calc |‖ξ'‖ ^ 2 - ‖ξ‖ ^ 2| ≤ 2 * R * ‖ξ - ξ'‖ := hd
    _ = 2 * R / (r ^ 2 * r ^ 2) * ‖ξ - ξ'‖ * (r ^ 2 * r ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hxy hk

def divFreeSlopeConst (r R MF LF : ℝ) : ℝ :=
  LF + ((1 * MF + R * LF) * ((r ^ 2)⁻¹ * R) + R * MF * (2 * R / (r ^ 2 * r ^ 2) * R + (r ^ 2)⁻¹ * 1))

theorem divFreeVec_slope {r R : ℝ} (hr : 0 < r) {ξ ξ' : Space} (h1 : r ≤ ‖ξ‖) (h2 : ‖ξ‖ ≤ R)
    (h1' : r ≤ ‖ξ'‖) (h2' : ‖ξ'‖ ≤ R) {c c' : Coef} {MF LF : ℝ} (hc : ‖c‖ ≤ MF) (hc' : ‖c'‖ ≤ MF)
    (hdc : ‖c - c'‖ ≤ LF * ‖ξ - ξ'‖) :
    ‖divFreeVec ξ c - divFreeVec ξ' c'‖ ≤ divFreeSlopeConst r R MF LF * ‖ξ - ξ'‖ := by
  have hξ : ξ ≠ 0 := norm_pos_iff.mp (hr.trans_le h1)
  have hξ' : ξ' ≠ 0 := norm_pos_iff.mp (hr.trans_le h1')
  rw [divFreeVec_eq hξ, divFreeVec_eq hξ']
  have hv : ‖Freq.complexifyVec ξ - Freq.complexifyVec ξ'‖ ≤ 1 * ‖ξ - ξ'‖ := by
    rw [← map_sub, norm_complexifyVec_eq, one_mul]
  have hvn : ‖Freq.complexifyVec ξ‖ ≤ R := by rw [norm_complexifyVec_eq]; exact h2
  have hvn' : ‖Freq.complexifyVec ξ'‖ ≤ R := by rw [norm_complexifyVec_eq]; exact h2'
  have hz := inner_slope hvn' hc hv hdc
  have hz' : ‖inner ℂ (Freq.complexifyVec ξ') c'‖ ≤ R * MF :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hvn' hc' (norm_nonneg _) ((norm_nonneg _).trans hvn'))
  have hs' : ‖((((‖ξ'‖ ^ 2)⁻¹ : ℝ) : ℂ))‖ ≤ (r ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (by gcongr)
  have hs : ‖((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ))‖ ≤ (r ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (by gcongr)
  have hw := smul_slope hs' hvn (invSq_slope hr h1 h2 h1' h2') hv
  have hwn : ‖((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) • Freq.complexifyVec ξ‖ ≤ (r ^ 2)⁻¹ * R := by
    rw [norm_smul]
    exact mul_le_mul hs hvn (norm_nonneg _) ((norm_nonneg _).trans hs)
  have hQ := smul_slope hz' hwn hz hw
  calc _ = ‖(c - c') - (inner ℂ (Freq.complexifyVec ξ) c • ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) • Freq.complexifyVec ξ) -
        inner ℂ (Freq.complexifyVec ξ') c' • ((((‖ξ'‖ ^ 2)⁻¹ : ℝ) : ℂ) • Freq.complexifyVec ξ'))‖ := by
        congr 1
        abel
    _ ≤ ‖c - c'‖ + ‖inner ℂ (Freq.complexifyVec ξ) c • ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) • Freq.complexifyVec ξ) -
        inner ℂ (Freq.complexifyVec ξ') c' • ((((‖ξ'‖ ^ 2)⁻¹ : ℝ) : ℂ) • Freq.complexifyVec ξ')‖ :=
        norm_sub_le _ _
    _ ≤ LF * ‖ξ - ξ'‖ + ((1 * MF + R * LF) * ((r ^ 2)⁻¹ * R) +
        R * MF * (2 * R / (r ^ 2 * r ^ 2) * R + (r ^ 2)⁻¹ * 1)) * ‖ξ - ξ'‖ := add_le_add hdc hQ
    _ = _ := by unfold divFreeSlopeConst; ring

theorem norm_two_pi_I_mul (t : ℝ) : ‖(2 * π * Complex.I * ((t : ℝ) : ℂ))‖ = 2 * π * |t| := by
  simp [abs_of_pos pi_pos]

end Breakdown.Periodic.SourceDensity.Internal

namespace Breakdown.Periodic

open SourceDensity.Internal

theorem sourceDensityBounds : SourceDensityBounds := by
  intro b b' ε hε
  set C₀ := (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal with hC₀
  set B₀ := 8 * (1 + 3 / (4 * π ^ 2 * ε)) ^ 3 with hB₀
  have hC : 0 ≤ C₀ := ENNReal.toReal_nonneg
  have hB : 0 ≤ B₀ := by positivity
  refine ⟨(2 * π + 1) * (2 * C₀ * B₀), ?_⟩
  intro A hA hAn y hy τ hτ ξ
  have hF := freqTrVec_bound A b' hA hAn ξ
  have hP : ‖divFreeVec ξ (freqTrVec (⇑A) ξ)‖ ≤ 2 * C₀ := (divFreeVec_norm_le _ _).trans (by linarith)
  have hh : Freq.heatFactor τ ξ * (1 + ‖ξ‖) ^ 6 ≤ B₀ := heatFactor_decay hε hτ.1 ξ
  have h0 := heatFactor_nonneg τ ξ
  have hV : ‖valueDensity τ (⇑A) y ξ‖ ≤ Freq.heatFactor τ ξ * (2 * C₀) := by
    unfold valueDensity
    rw [norm_smul, norm_expChar, one_mul, norm_smul, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left hP h0
  have hu1 : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  have hpos : 0 < (1 + ‖ξ‖) ^ 4 := by positivity
  have hpow : (1 + ‖ξ‖) ^ (-4 : ℝ) = ((1 + ‖ξ‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h46 : (1 + ‖ξ‖) ^ 4 ≤ (1 + ‖ξ‖) ^ 6 := pow_le_pow_right₀ hu1 (by norm_num)
  have h56 : (1 + ‖ξ‖) ^ 5 ≤ (1 + ‖ξ‖) ^ 6 := pow_le_pow_right₀ hu1 (by norm_num)
  have hX : 0 ≤ 2 * C₀ * B₀ := by positivity
  have hK : 2 * C₀ * B₀ ≤ (2 * π + 1) * (2 * C₀ * B₀) :=
    le_mul_of_one_le_left hX (by linarith [pi_pos])
  have hK' : 2 * π * (2 * C₀ * B₀) ≤ (2 * π + 1) * (2 * C₀ * B₀) := by nlinarith
  rw [hpow, ← div_eq_mul_inv]
  constructor
  · rw [le_div_iff₀ hpos]
    calc ‖valueDensity τ (⇑A) y ξ‖ * (1 + ‖ξ‖) ^ 4 ≤
          Freq.heatFactor τ ξ * (2 * C₀) * (1 + ‖ξ‖) ^ 6 :=
          mul_le_mul hV h46 (by positivity) (by positivity)
      _ = 2 * C₀ * (Freq.heatFactor τ ξ * (1 + ‖ξ‖) ^ 6) := by ring
      _ ≤ 2 * C₀ * B₀ := by gcongr
      _ ≤ _ := hK
  · intro j
    rw [le_div_iff₀ hpos]
    unfold gradDensity
    rw [norm_smul]
    have hj : ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ))‖ ≤ 2 * π * (1 + ‖ξ‖) := by
      rw [norm_two_pi_I_mul]
      have := PiLp.norm_apply_le ξ j
      rw [Real.norm_eq_abs] at this
      gcongr
      linarith
    calc ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ))‖ * ‖valueDensity τ (⇑A) y ξ‖ * (1 + ‖ξ‖) ^ 4 ≤
          2 * π * (1 + ‖ξ‖) * (Freq.heatFactor τ ξ * (2 * C₀)) * (1 + ‖ξ‖) ^ 4 := by gcongr
      _ = 2 * π * (2 * C₀) * (Freq.heatFactor τ ξ * (1 + ‖ξ‖) ^ 5) := by ring
      _ ≤ 2 * π * (2 * C₀) * (Freq.heatFactor τ ξ * (1 + ‖ξ‖) ^ 6) := by gcongr
      _ ≤ 2 * π * (2 * C₀) * B₀ := by gcongr
      _ = 2 * π * (2 * C₀ * B₀) := by ring
      _ ≤ _ := hK'

theorem sourceDensitySlope : SourceDensitySlope := by
  intro b b' ε r R hε hr
  set C₀ := (volume (Metric.closedBall (0 : Space) |b'|) ^ (1 / 3 : ℝ)).toReal with hC₀
  set LF := 2 * π * |b'| * C₀ with hLF
  set Le := 2 * π * |b| with hLe
  set Lh := 4 * π ^ 2 * ε⁻¹ * (2 * R) with hLh
  set MP := 2 * C₀ with hMP
  set LP := divFreeSlopeConst r R C₀ LF with hLP
  set LhP := Lh * MP + 1 * LP with hLhP
  set LV := Le * MP + 1 * LhP with hLV
  set Lg := 2 * π * MP + 2 * π * R * LV with hLg
  refine ⟨max LV Lg, ?_⟩
  intro A hA hAn y hy τ hτ ξ ξ' h1 h2 h1' h2'
  have hF := freqTrVec_bound A b' hA hAn ξ
  have hF' := freqTrVec_bound A b' hA hAn ξ'
  have hFL := freqTrVec_slope A b' hA hAn ξ ξ'
  have hPL := divFreeVec_slope hr h1 h2 h1' h2' hF hF' hFL
  have hPn : ‖divFreeVec ξ (freqTrVec (⇑A) ξ)‖ ≤ MP := (divFreeVec_norm_le _ _).trans (by linarith)
  have hh' : ‖Freq.heatFactor τ ξ'‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (heatFactor_nonneg _ _)]
    exact heatFactor_le_one _ _
  have hhL := heatFactor_slope hε hτ.2 h2 h2'
  have hhP := smul_slope hh' hPn hhL hPL
  have hhPn : ‖Freq.heatFactor τ ξ • divFreeVec ξ (freqTrVec (⇑A) ξ)‖ ≤ MP := by
    rw [norm_smul, Real.norm_of_nonneg (heatFactor_nonneg _ _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (heatFactor_le_one _ _)).trans hPn
  have he' : ‖expChar y ξ'‖ ≤ 1 := (norm_expChar y ξ').le
  have heL := expChar_slope hy ξ ξ'
  have hV : ‖valueDensity τ (⇑A) y ξ - valueDensity τ (⇑A) y ξ'‖ ≤ LV * ‖ξ - ξ'‖ :=
    smul_slope he' hhPn heL hhP
  have hVn : ‖valueDensity τ (⇑A) y ξ‖ ≤ MP := by
    unfold valueDensity
    rw [norm_smul, norm_expChar, one_mul]
    exact hhPn
  have hd : 0 ≤ ‖ξ - ξ'‖ := norm_nonneg _
  refine ⟨hV.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd), fun j => ?_⟩
  have hs' : ‖(2 * π * Complex.I * ((ξ' j : ℝ) : ℂ))‖ ≤ 2 * π * R := by
    rw [norm_two_pi_I_mul]
    have := PiLp.norm_apply_le ξ' j
    rw [Real.norm_eq_abs] at this
    gcongr
    linarith
  have hsL : ‖(2 * π * Complex.I * ((ξ j : ℝ) : ℂ)) - (2 * π * Complex.I * ((ξ' j : ℝ) : ℂ))‖ ≤
      2 * π * ‖ξ - ξ'‖ := by
    rw [← mul_sub, ← Complex.ofReal_sub, norm_two_pi_I_mul]
    have := PiLp.norm_apply_le (ξ - ξ') j
    rw [Real.norm_eq_abs, PiLp.sub_apply] at this
    gcongr
  have hg := smul_slope hs' hVn hsL hV
  unfold gradDensity
  exact hg.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hd)

end Breakdown.Periodic
