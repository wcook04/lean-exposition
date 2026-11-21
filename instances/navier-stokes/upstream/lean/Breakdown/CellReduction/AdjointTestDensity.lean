import Breakdown.CellReduction.AdjointTestDensityLimits

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace AdjointDefect

attribute [local instance] CertCell.Internal.ActuatorPairingDensity.prodVolume_addInvariant
attribute [local instance] CertCell.Internal.ActuatorPairingDensity.prodVolume_isNegInvariant

open Internal.TestDensity in
open CertCell.Internal.ActuatorPairingDensity in
theorem testFieldDensityHolds_proof : TestFieldDensityHolds := by
  intro C γ β ζ A ψ hζ hA hψ hψc
  obtain ⟨c, hc0, hc⟩ := round_bounds
  have hC := field_C_nonneg hζ
  have hγ := hζ.rate_gt
  have hβ := hA.rate_gt
  set p := min γ (β + 1) with hpdef
  have hpγ : p ≤ γ := min_le_left _ _
  have hpβ : p ≤ β + 1 := min_le_right _ _
  have hp : 5 / 2 < p := lt_min hγ (by linarith)
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨S, hS⟩ := cutoff_support hψc
  obtain ⟨P0, hP0⟩ := (smooth_one hψ).continuous.bounded_above_of_compact_support hψc
  obtain ⟨P1, hP1⟩ := ((smooth_one hψ).continuous_deriv le_rfl).bounded_above_of_compact_support
    (hψc.deriv (𝕜 := ℝ))
  have hψ0 : ∀ s, |ψ s| ≤ P0 := fun s => by simpa [Real.norm_eq_abs] using hP0 s
  have hψ1 : ∀ s, |deriv ψ s| ≤ P1 := fun s => by simpa [Real.norm_eq_abs] using hP1 s
  have hP00 : 0 ≤ P0 := (abs_nonneg _).trans (hψ0 0)
  have hP10 : 0 ≤ P1 := (abs_nonneg _).trans (hψ1 0)
  have hψ01 : ∀ s, |ψ s| + |deriv ψ s| ≤ P0 + P1 := fun s => add_le_add (hψ0 s) (hψ1 s)
  have hψ01' : ∀ s, 0 ≤ |ψ s| + |deriv ψ s| := fun s => by positivity
  have hBn := norm_nonneg (crossGrad)
  set M := C + ‖crossGrad‖ * (3 * c) * C with hM
  set M1 := C + 3 * c * C + ‖crossGrad‖ * (3 * c) * C + ‖crossGrad‖ * (9 * c) * C with hStrain
  have hCM : C ≤ M := by
    have : 0 ≤ ‖crossGrad‖ * (3 * c) * C := by positivity
    linarith
  have hCM1 : C ≤ M1 := by
    have : 0 ≤ 3 * c * C + ‖crossGrad‖ * (3 * c) * C + ‖crossGrad‖ * (9 * c) * C := by positivity
    linarith
  have hM0 : 0 ≤ M := hC.trans hCM
  have hM10 : 0 ≤ M1 := hC.trans hCM1
  set h : ℕ → ℝ → Space → Space := fun n => trunc ψ ζ A ((n : ℝ) + 1) with hh
  have hR : ∀ n : ℕ, 1 ≤ (n : ℝ) + 1 := fun n => by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hR0 : ∀ n : ℕ, 0 < (n : ℝ) + 1 := fun n => by positivity
  have hcd : ∀ n, ContDiff ℝ 1 (fun z : ℝ × Space => h n z.1 z.2) :=
    fun n => trunc_contDiff hψ hζ.smooth hA.smooth _
  have hb0 : ∀ n s y, ‖h n s y‖ ≤ |ψ s| * (M / (1 + ‖y‖) ^ p) :=
    fun n s y => trunc_bound hζ hA hc0 (fun x => (hc x).1) (hR n) hpγ hpβ s y
  have hb1 : ∀ n s y, ‖gradField (h n) s y‖ ≤ |ψ s| * (M1 / (1 + ‖y‖) ^ (p + 1)) :=
    fun n s y => trunc_grad_bound hζ hA hc0 hc (hR n) hpγ hpβ s y
  have hb2 : ∀ n s y, ‖timeDerivative (h n) s y‖ ≤ (|ψ s| + |deriv ψ s|) * (M / (1 + ‖y‖) ^ p) :=
    fun n s y => trunc_time_bound hψ hζ hA hc0 (fun x => (hc x).1) (hR n) hpγ hpβ s y
  have hg0 : ∀ n s y, ‖h n s y‖ ≤ P0 * M :=
    fun n s y => (hb0 n s y).trans (glob_le hM0 hp0 (abs_nonneg _) (hψ0 s) y)
  have hg1 : ∀ n s y, ‖gradField (h n) s y‖ ≤ P0 * M1 :=
    fun n s y => (hb1 n s y).trans (glob_le hM10 (by linarith) (abs_nonneg _) (hψ0 s) y)
  have hg2 : ∀ n s y, ‖timeDerivative (h n) s y‖ ≤ (P0 + P1) * M :=
    fun n s y => (hb2 n s y).trans (glob_le hM0 hp0 (hψ01' s) (hψ01 s) y)
  have hz0 : ∀ (n : ℕ) s y, S < |s| ∨ 2 * ((n : ℝ) + 1) < ‖y‖ → h n s y = 0 :=
    fun n s y hsy => trunc_zero0 (hR0 n) hS s y hsy
  have hz1 : ∀ (n : ℕ) s y, S < |s| ∨ 2 * ((n : ℝ) + 1) < ‖y‖ → gradField (h n) s y = 0 :=
    fun n s y hsy => trunc_zero1 (hR0 n) hS s y hsy
  have hz2 : ∀ (n : ℕ) s y, S < |s| ∨ 2 * ((n : ℝ) + 1) < ‖y‖ → timeDerivative (h n) s y = 0 :=
    fun n s y hsy => trunc_zero2 hψ hζ.smooth hA.smooth (hR0 n) hS s y hsy
  have hcs0 : ∀ n, HasCompactSupport (fun z : ℝ × Space => h n z.1 z.2) :=
    fun n => box_support (fun s y hsy => hz0 n s y hsy)
  have hcs1 : ∀ n, HasCompactSupport (fun z : ℝ × Space => gradField (h n) z.1 z.2) :=
    fun n => box_support (fun s y hsy => hz1 n s y hsy)
  have hcs2 : ∀ n, HasCompactSupport (fun z : ℝ × Space => timeDerivative (h n) z.1 z.2) :=
    fun n => box_support (fun s y hsy => hz2 n s y hsy)
  have hex : ∀ n : ℕ, ∃ m : ℕ,
      (∀ z : ℝ × Space, ‖(∫ w, kernel m w • h n (z.1 - w.1) (z.2 - w.2)) - h n z.1 z.2‖ ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ z : ℝ × Space, ‖(∫ w, kernel m w • gradField (h n) (z.1 - w.1) (z.2 - w.2))
        - gradField (h n) z.1 z.2‖ ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ z : ℝ × Space, ‖(∫ w, kernel m w • timeDerivative (h n) (z.1 - w.1) (z.2 - w.2))
        - timeDerivative (h n) z.1 z.2‖ ≤ 1 / ((n : ℝ) + 1)) := by
    intro n
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ((kernel_uniform (hcd n).continuous (hcs0 n) hδ).and
      ((kernel_uniform (slice_spaceDeriv_continuous (hcd n)) (hcs1 n) hδ).and
        (kernel_uniform (time_deriv_continuous (hcd n)) (hcs2 n) hδ))).exists
  choose m hm using hex
  set φ : ℕ → ℝ → Space → Space := fun n => smoothed (h n) (m n) with hφ
  have hφc : ∀ n, ContDiff ℝ ∞ (fun z : ℝ × Space => φ n z.1 z.2) :=
    fun n => smoothed_contDiff (hcd n).continuous (m n)
  have hφ1 : ∀ n, ContDiff ℝ 1 (fun z : ℝ × Space => φ n z.1 z.2) := fun n => smooth_one (hφc n)
  have hu1 := cutoff_contDiff hψ hζ.smooth
  have ef0 : ∀ n s y, φ n s y = ∫ w : ℝ × Space, kernel (m n) w • h n (s - w.1) (y - w.2) :=
    fun n s y => smoothed_eq (h n) (m n) s y
  have ef1 : ∀ n s y, fderiv ℝ (φ n s) y =
      ∫ w : ℝ × Space, kernel (m n) w • gradField (h n) (s - w.1) (y - w.2) :=
    fun n s y => smoothed_fderiv (hcd n) (hg0 n) (hg1 n) (m n) s y
  have ef2 : ∀ n s y, timeDerivative (φ n) s y =
      ∫ w : ℝ × Space, kernel (m n) w • timeDerivative (h n) (s - w.1) (y - w.2) :=
    fun n s y => smoothed_timeDerivative (hcd n) (hg0 n) (hg2 n) (m n) s y
  have bφ0 : ∀ n s y, ‖φ n s y‖ ≤ P0 * (2 ^ p * M / (1 + ‖y‖) ^ p) := by
    intro n s y
    rw [ef0]
    exact sm_bound (m n) hM0 hp0 (fun s => abs_nonneg (ψ s)) hψ0 (hb0 n) s y
  have bφ1 : ∀ n s y, ‖fderiv ℝ (φ n s) y‖ ≤ P0 * (2 ^ (p + 1) * M1 / (1 + ‖y‖) ^ (p + 1)) := by
    intro n s y
    rw [ef1]
    exact sm_bound (m n) hM10 (by linarith) (fun s => abs_nonneg (ψ s)) hψ0 (hb1 n) s y
  have bφ2 : ∀ n s y, ‖timeDerivative (φ n) s y‖ ≤ (P0 + P1) * (2 ^ p * M / (1 + ‖y‖) ^ p) := by
    intro n s y
    rw [ef2]
    exact sm_bound (m n) hM0 hp0 hψ01' hψ01 (hb2 n) s y
  have zφ0 : ∀ n s y, S + 1 < |s| → φ n s y = 0 := by
    intro n s y hs
    rw [ef0]
    exact sm_zero (m n) (fun s y hs => hz0 n s y (Or.inl hs)) s y hs
  have zφ1 : ∀ n s y, S + 1 < |s| → fderiv ℝ (φ n s) y = 0 := by
    intro n s y hs
    rw [ef1]
    exact sm_zero (m n) (fun s y hs => hz1 n s y (Or.inl hs)) s y hs
  have zφ2 : ∀ n s y, S + 1 < |s| → timeDerivative (φ n) s y = 0 := by
    intro n s y hs
    rw [ef2]
    exact sm_zero (m n) (fun s y hs => hz2 n s y (Or.inl hs)) s y hs
  have bu0 : ∀ s y, ‖timeCutoff ψ ζ s y‖ ≤ P0 * (M / (1 + ‖y‖) ^ p) := by
    intro s y
    unfold timeCutoff
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hψ0 s) ((hζ.decay s y).1.trans (weight_le_of_le hC hCM hpγ y)) (norm_nonneg _) hP00
  have bu1 : ∀ s y, ‖fderiv ℝ (timeCutoff ψ ζ s) y‖ ≤ P0 * (M1 / (1 + ‖y‖) ^ (p + 1)) := by
    intro s y
    rw [cutoff_spaceDeriv hζ.smooth, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hψ0 s) ((hζ.decay s y).2.2.trans (weight_le_of_le hC hCM1 (by linarith) y))
      (norm_nonneg _) hP00
  have bu2 : ∀ s y, ‖timeDerivative (timeCutoff ψ ζ) s y‖ ≤ (P0 + P1) * (M / (1 + ‖y‖) ^ p) := by
    intro s y
    rw [cutoff_time hψ hζ.smooth, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hψ0 s) ((hζ.decay s y).2.1.trans (weight_le_of_le hC hCM hpγ y)) (norm_nonneg _) hP00
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hψ1 s) ((hζ.decay s y).1.trans (weight_le_of_le hC hCM hpγ y)) (norm_nonneg _) hP10
  have zu0 : ∀ s y, S + 1 < |s| → timeCutoff ψ ζ s y = 0 := by
    intro s y hs
    simp [timeCutoff, (hS s (by linarith)).1]
  have zu1 : ∀ s y, S + 1 < |s| → fderiv ℝ (timeCutoff ψ ζ s) y = 0 := by
    intro s y hs
    rw [cutoff_spaceDeriv hζ.smooth, (hS s (by linarith)).1, zero_smul]
  have zu2 : ∀ s y, S + 1 < |s| → timeDerivative (timeCutoff ψ ζ) s y = 0 := by
    intro s y hs
    rw [cutoff_time hψ hζ.smooth, (hS s (by linarith)).1, (hS s (by linarith)).2, zero_smul, zero_smul, add_zero]
  have ev : ∀ (s : ℝ) (y : Space), ∀ᶠ n : ℕ in atTop, h n s y = timeCutoff ψ ζ s y ∧
      gradField (h n) s y = fderiv ℝ (timeCutoff ψ ζ s) y ∧
      timeDerivative (h n) s y = timeDerivative (timeCutoff ψ ζ) s y := by
    intro s y
    filter_upwards [eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
    have hy : ‖y‖ < (n : ℝ) + 1 := by
      have h1 := Nat.le_ceil ‖y‖
      have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    refine ⟨(trunc_near (hR0 n) s hy).eq_of_nhds, (trunc_near (hR0 n) s hy).fderiv_eq, ?_⟩
    have e : (fun s' => h n s' y) = fun s' => timeCutoff ψ ζ s' y :=
      funext fun s' => (trunc_near (hR0 n) s' hy).eq_of_nhds
    unfold timeDerivative
    rw [e]
  have lim0 : ∀ s y, Tendsto (fun n => φ n s y - timeCutoff ψ ζ s y) atTop (𝓝 0) := by
    intro s y
    refine squeeze_zero_norm' ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [ev s y] with n hn
    rw [← hn.1, ef0]
    exact (hm n).1 (s, y)
  have lim1 : ∀ s y, Tendsto (fun n => fderiv ℝ (φ n s) y - fderiv ℝ (timeCutoff ψ ζ s) y) atTop (𝓝 0) := by
    intro s y
    refine squeeze_zero_norm' ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [ev s y] with n hn
    rw [← hn.2.1, ef1]
    exact (hm n).2.1 (s, y)
  have lim2 : ∀ s y, Tendsto (fun n => timeDerivative (φ n) s y - timeDerivative (timeCutoff ψ ζ) s y) atTop
      (𝓝 0) := by
    intro s y
    refine squeeze_zero_norm' ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [ev s y] with n hn
    rw [← hn.2.2, ef2]
    exact (hm n).2.2 (s, y)
  have lim3 : ∀ s y, Tendsto (fun n => fderiv ℝ (φ n s) y y - fderiv ℝ (timeCutoff ψ ζ s) y y) atTop (𝓝 0) := by
    intro s y
    have h1 := ((ContinuousLinearMap.apply ℝ Space y).continuous.tendsto 0).comp (lim1 s y)
    simpa [Function.comp_def] using h1
  have bd0 : ∀ n s y, ‖φ n s y - timeCutoff ψ ζ s y‖ ≤ (P0 * (2 ^ p * M) + P0 * M) / (1 + ‖y‖) ^ p := by
    intro n s y
    calc ‖φ n s y - timeCutoff ψ ζ s y‖ ≤ ‖φ n s y‖ + ‖timeCutoff ψ ζ s y‖ := norm_sub_le _ _
      _ ≤ P0 * (2 ^ p * M / (1 + ‖y‖) ^ p) + P0 * (M / (1 + ‖y‖) ^ p) := add_le_add (bφ0 n s y) (bu0 s y)
      _ = (P0 * (2 ^ p * M) + P0 * M) / (1 + ‖y‖) ^ p := by ring
  have bd1 : ∀ n s y, ‖fderiv ℝ (φ n s) y - fderiv ℝ (timeCutoff ψ ζ s) y‖ ≤
      (P0 * (2 ^ (p + 1) * M1) + P0 * M1) / (1 + ‖y‖) ^ (p + 1) := by
    intro n s y
    calc ‖fderiv ℝ (φ n s) y - fderiv ℝ (timeCutoff ψ ζ s) y‖
        ≤ ‖fderiv ℝ (φ n s) y‖ + ‖fderiv ℝ (timeCutoff ψ ζ s) y‖ := norm_sub_le _ _
      _ ≤ P0 * (2 ^ (p + 1) * M1 / (1 + ‖y‖) ^ (p + 1)) + P0 * (M1 / (1 + ‖y‖) ^ (p + 1)) :=
          add_le_add (bφ1 n s y) (bu1 s y)
      _ = (P0 * (2 ^ (p + 1) * M1) + P0 * M1) / (1 + ‖y‖) ^ (p + 1) := by ring
  have bd2 : ∀ n s y, ‖timeDerivative (φ n) s y - timeDerivative (timeCutoff ψ ζ) s y‖ ≤
      ((P0 + P1) * (2 ^ p * M) + (P0 + P1) * M) / (1 + ‖y‖) ^ p := by
    intro n s y
    calc ‖timeDerivative (φ n) s y - timeDerivative (timeCutoff ψ ζ) s y‖
        ≤ ‖timeDerivative (φ n) s y‖ + ‖timeDerivative (timeCutoff ψ ζ) s y‖ := norm_sub_le _ _
      _ ≤ (P0 + P1) * (2 ^ p * M / (1 + ‖y‖) ^ p) + (P0 + P1) * (M / (1 + ‖y‖) ^ p) :=
          add_le_add (bφ2 n s y) (bu2 s y)
      _ = ((P0 + P1) * (2 ^ p * M) + (P0 + P1) * M) / (1 + ‖y‖) ^ p := by ring
  have hK0 : 0 ≤ P0 * (2 ^ p * M) + P0 * M := by positivity
  have hK1 : 0 ≤ P0 * (2 ^ (p + 1) * M1) + P0 * M1 := by positivity
  have hK2 : 0 ≤ (P0 + P1) * (2 ^ p * M) + (P0 + P1) * M := by positivity
  refine ⟨φ, fun n => ⟨hφc n, ?_, fun s y => ?_⟩, ⟨-(S + 1), S + 1, fun n s y hs => zφ0 n s y (not_mem_Icc_abs hs)⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (bumpSeq (m n)).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hcs0 n)
  · exact smoothed_divergence (hcd n) (hg0 n) (hg1 n)
      (fun σ y => trunc_divergence hζ.smooth hA.smooth hζ.divergence_free hA.curl_eq _ σ y) (m n) s y
  · exact sq_lintegral_tendsto (v := fun n s y => φ n s y - timeCutoff ψ ζ s y)
      (fun n => (hφ1 n).continuous.sub hu1.continuous) (by linarith) bd0 (S := S + 1)
      (fun n s y hs => by rw [zφ0 n s y hs, zu0 s y hs, sub_zero]) lim0
  · have hsq := sq_lintegral_tendsto (v := fun n s y => fderiv ℝ (φ n s) y - fderiv ℝ (timeCutoff ψ ζ s) y)
      (fun n => (slice_spaceDeriv_continuous (hφ1 n)).sub (slice_spaceDeriv_continuous hu1)) (by linarith) bd1
      (S := S + 1) (fun n s y hs => by rw [zφ1 n s y hs, zu1 s y hs, sub_zero]) lim1
    have h3 := ENNReal.Tendsto.const_mul hsq (Or.inr (ENNReal.ofReal_ne_top (r := 3)))
    rw [mul_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun n => zero_le) (fun n => ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    rw [← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (columnSq_le _)
  · exact mixed_tendsto (v := fun n s y => φ n s y - timeCutoff ψ ζ s y)
      (fun n => (hφ1 n).continuous.sub hu1.continuous) hK0 hp bd0 (S := S + 1)
      (fun n s y hs => by rw [zφ0 n s y hs, zu0 s y hs, sub_zero]) lim0
  · exact mixed_tendsto (v := fun n s y => timeDerivative (φ n) s y - timeDerivative (timeCutoff ψ ζ) s y)
      (fun n => (time_deriv_continuous (hφ1 n)).sub (time_deriv_continuous hu1)) hK2 hp bd2 (S := S + 1)
      (fun n s y hs => by rw [zφ2 n s y hs, zu2 s y hs, sub_zero]) lim2
  · refine mixed_tendsto (v := fun n s y => fderiv ℝ (φ n s) y y - fderiv ℝ (timeCutoff ψ ζ s) y y)
      (fun n => ((slice_spaceDeriv_continuous (hφ1 n)).clm_apply continuous_snd).sub
        ((slice_spaceDeriv_continuous hu1).clm_apply continuous_snd)) hK1 hp (fun n s y => ?_) (S := S + 1)
      (fun n s y hs => by rw [zφ1 n s y hs, zu1 s y hs, zero_apply, sub_zero])
      lim3
    rw [← sub_apply]
    exact radial_le hK1 y (bd1 n s y)

end AdjointDefect

end Breakdown
