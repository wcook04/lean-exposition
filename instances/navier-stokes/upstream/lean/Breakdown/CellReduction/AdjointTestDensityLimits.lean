import Breakdown.CellReduction.AdjointTestDensityCutoff

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal.TestDensity

open CertCell.Internal.ActuatorPairingDensity

attribute [local instance] CertCell.Internal.ActuatorPairingDensity.prodVolume_addInvariant
attribute [local instance] CertCell.Internal.ActuatorPairingDensity.prodVolume_isNegInvariant

open CertCell.TailBand.SquareInternal (roundBump roundBump_contDiff roundBump_hasCompactSupport roundBump_eq_one
  roundBump_eq_zero roundBump_nonneg roundBump_le_one scaledBump scaledBump_contDiff scaledBump_eq_one scaledBump_eq_zero)

variable {ψ : ℝ → ℝ} {ζ A : ℝ → Space → Space}

theorem weight_lintegral_finite {q : ℝ} (hq : 3 < q) (K : ℝ) :
    ∫⁻ y : Space, ENNReal.ofReal (K / (1 + ‖y‖) ^ q) ≠ ⊤ := by
  have e : ∀ y : Space, ENNReal.ofReal (K / (1 + ‖y‖) ^ q) =
      ENNReal.ofReal K * ENNReal.ofReal ((1 + ‖y‖) ^ (-q)) := by
    intro y
    rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg (by positivity) _), Real.rpow_neg (by positivity), div_eq_mul_inv]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (finite_integral_one_add_norm ?_).ne
  rw [finrank_euclideanSpace_fin]
  exact_mod_cast hq

theorem not_mem_Icc_abs {S s : ℝ} (h : s ∉ Set.Icc (-S) S) : S < |s| := by
  rw [Set.mem_Icc, ← abs_le] at h
  exact lt_of_not_ge h

theorem sq_lintegral_tendsto {E : Type*} [NormedAddCommGroup E] {v : ℕ → ℝ → Space → E}
    (hc : ∀ n, Continuous (fun z : ℝ × Space => v n z.1 z.2)) {K q S : ℝ} (hq : 3 / 2 < q)
    (hb : ∀ n s y, ‖v n s y‖ ≤ K / (1 + ‖y‖) ^ q) (hs : ∀ n s y, S < |s| → v n s y = 0)
    (hl : ∀ s y, Tendsto (fun n => v n s y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z : ℝ × Space, ENNReal.ofReal (‖v n z.1 z.2‖ ^ 2)) atTop (𝓝 0) := by
  set f : ℝ → ℝ≥0∞ := (Set.Icc (-S) S).indicator (fun _ => (1 : ℝ≥0∞)) with hf
  set g : Space → ℝ≥0∞ := fun y => ENNReal.ofReal (K ^ 2 / (1 + ‖y‖) ^ (q * (2 : ℕ))) with hg
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n (z : ℝ × Space) => ENNReal.ofReal (‖v n z.1 z.2‖ ^ 2)) (f := fun _ => 0)
    (fun z : ℝ × Space => f z.1 * g z.2)
    (fun n => ((hc n).norm.pow 2).measurable.ennreal_ofReal) (fun n => ae_of_all _ fun z => ?_) ?_
    (ae_of_all _ fun z => ?_)
  · simpa using hlim
  · show ENNReal.ofReal (‖v n z.1 z.2‖ ^ 2) ≤ f z.1 * g z.2
    by_cases hz : z.1 ∈ Set.Icc (-S) S
    · rw [hf, Set.indicator_of_mem hz, one_mul]
      apply ENNReal.ofReal_le_ofReal
      calc ‖v n z.1 z.2‖ ^ 2 ≤ (K / (1 + ‖z.2‖) ^ q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb n z.1 z.2) 2
        _ = K ^ 2 / (1 + ‖z.2‖) ^ (q * (2 : ℕ)) := by rw [div_pow, Real.rpow_mul_natCast (by positivity)]
    · rw [hs n z.1 z.2 (not_mem_Icc_abs hz)]
      simp
  · have hfm : AEMeasurable f volume := (measurable_const.indicator measurableSet_Icc).aemeasurable
    have hgc : Continuous (fun y : Space => K ^ 2 / (1 + ‖y‖) ^ (q * (2 : ℕ))) :=
      continuous_const.div ((continuous_const.add continuous_norm).rpow_const
        (fun y : Space => Or.inl (by have h := norm_nonneg y; exact (show (0 : ℝ) < 1 + ‖y‖ by linarith).ne'))) (fun y => (Real.rpow_pos_of_pos (by positivity) _).ne')
    have hgm : AEMeasurable g volume := hgc.measurable.ennreal_ofReal.aemeasurable
    rw [Measure.volume_eq_prod, lintegral_prod_mul hfm hgm]
    refine ENNReal.mul_ne_top ?_ (weight_lintegral_finite (by push_cast; linarith) _)
    rw [hf, lintegral_indicator_const measurableSet_Icc, one_mul, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  · have h1 := ((continuous_norm.tendsto 0).comp (hl z.1 z.2)).pow 2
    have h2 := (ENNReal.continuous_ofReal.tendsto _).comp h1
    simpa [Function.comp_def] using h2

theorem mixed_tendsto {v : ℕ → ℝ → Space → Space}
    (hc : ∀ n, Continuous (fun z : ℝ × Space => v n z.1 z.2)) {K q S : ℝ} (hK : 0 ≤ K) (hq : 5 / 2 < q)
    (hb : ∀ n s y, ‖v n s y‖ ≤ K / (1 + ‖y‖) ^ q) (hs : ∀ n s y, S < |s| → v n s y = 0)
    (hl : ∀ s y, Tendsto (fun n => v n s y) atTop (𝓝 0)) :
    Tendsto (fun n => mixedNorm (v n)) atTop (𝓝 0) := by
  set g : Space → ℝ≥0∞ := fun y => ENNReal.ofReal (K ^ (6 / 5 : ℝ) / (1 + ‖y‖) ^ (q * (6 / 5 : ℝ))) with hgdef
  have hg : ∫⁻ y, g y ≠ ⊤ := weight_lintegral_finite (by linarith) _
  have hpt : ∀ n s y, ENNReal.ofReal (‖v n s y‖ ^ (6 / 5 : ℝ)) ≤ g y := by
    intro n s y
    apply ENNReal.ofReal_le_ofReal
    calc ‖v n s y‖ ^ (6 / 5 : ℝ) ≤ (K / (1 + ‖y‖) ^ q) ^ (6 / 5 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) (hb n s y) (by norm_num)
      _ = K ^ (6 / 5 : ℝ) / (1 + ‖y‖) ^ (q * (6 / 5 : ℝ)) := by
          rw [Real.div_rpow hK (by positivity), ← Real.rpow_mul (by positivity)]
  have hin : ∀ s, Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (‖v n s y‖ ^ (6 / 5 : ℝ))) atTop (𝓝 0) := by
    intro s
    have h := tendsto_lintegral_of_dominated_convergence (μ := volume)
      (F := fun n y => ENNReal.ofReal (‖v n s y‖ ^ (6 / 5 : ℝ))) (f := fun _ => 0) g
      (fun n => (((hc n).comp (continuous_const.prodMk continuous_id)).norm.rpow_const
        (fun _ => Or.inr (by norm_num))).measurable.ennreal_ofReal)
      (fun n => ae_of_all _ (hpt n s)) hg (ae_of_all _ fun y => ?_)
    · simpa using h
    · have h1 : Tendsto (fun n => ‖v n s y‖ ^ (6 / 5 : ℝ)) atTop (𝓝 (‖(0 : Space)‖ ^ (6 / 5 : ℝ))) :=
        ((continuous_norm.tendsto 0).comp (hl s y)).rpow_const (Or.inr (by norm_num))
      rw [norm_zero, Real.zero_rpow (by norm_num)] at h1
      have h2 := (ENNReal.continuous_ofReal.tendsto _).comp h1
      simpa [Function.comp_def] using h2
  have hmeas : ∀ n, Measurable (fun s => (∫⁻ y, ENNReal.ofReal (‖v n s y‖ ^ (6 / 5 : ℝ))) ^ (5 / 3 : ℝ)) := by
    intro n
    exact (Measurable.lintegral_prod_right' (f := fun z : ℝ × Space => ENNReal.ofReal (‖v n z.1 z.2‖ ^ (6 / 5 : ℝ)))
      ((hc n).norm.rpow_const (fun _ => Or.inr (by norm_num))).measurable.ennreal_ofReal).pow_const _
  have h := tendsto_lintegral_of_dominated_convergence (μ := volume) (f := fun _ => 0)
    (fun s => (Set.Icc (-S) S).indicator (fun _ => (∫⁻ y, g y) ^ (5 / 3 : ℝ)) s) hmeas
    (fun n => ae_of_all _ fun s => ?_) ?_ (ae_of_all _ fun s => ?_)
  · simpa [mixedNorm] using h
  · by_cases hz : s ∈ Set.Icc (-S) S
    · dsimp only
      rw [Set.indicator_of_mem hz]
      exact ENNReal.rpow_le_rpow (lintegral_mono (hpt n s)) (by norm_num)
    · have e : (fun y => ENNReal.ofReal (‖v n s y‖ ^ (6 / 5 : ℝ))) = fun _ => 0 := by
        funext y
        rw [hs n s y (not_mem_Icc_abs hz), norm_zero, Real.zero_rpow (by norm_num), ENNReal.ofReal_zero]
      show (∫⁻ y, ENNReal.ofReal (‖v n s y‖ ^ (6 / 5 : ℝ))) ^ (5 / 3 : ℝ) ≤ _
      rw [e, lintegral_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
  · rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hg) ENNReal.ofReal_ne_top
  · have h1 := (ENNReal.continuous_rpow_const (y := (5 / 3 : ℝ))).tendsto 0 |>.comp (hin s)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
    exact h1

theorem cutoff_contDiff (hψ : ContDiff ℝ ∞ ψ) (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) :
    ContDiff ℝ 1 (fun z : ℝ × Space => timeCutoff ψ ζ z.1 z.2) :=
  ((smooth_one hψ).comp contDiff_fst).smul hζ

theorem cutoff_spaceDeriv (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) (s : ℝ) (y : Space) :
    fderiv ℝ (timeCutoff ψ ζ s) y = ψ s • fderiv ℝ (ζ s) y :=
  ((slice_differentiableAt hζ s y).hasFDerivAt.const_smul (ψ s)).fderiv

theorem cutoff_time (hψ : ContDiff ℝ ∞ ψ) (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) (s : ℝ) (y : Space) :
    timeDerivative (timeCutoff ψ ζ) s y = ψ s • timeDerivative ζ s y + deriv ψ s • ζ s y := by
  have hψd : HasDerivAt ψ (deriv ψ s) s := ((smooth_one hψ).differentiable one_ne_zero s).hasDerivAt
  exact (hψd.smul (time_hasDerivAt' hζ s y)).deriv

theorem weight_le_of_le {C M q : ℝ} (hC : 0 ≤ C) (hCM : C ≤ M) {r : ℝ} (hqr : q ≤ r) (y : Space) :
    C / (1 + ‖y‖) ^ r ≤ M / (1 + ‖y‖) ^ q := by
  have ht : 1 ≤ 1 + ‖y‖ := by have := norm_nonneg y; linarith
  exact (frac_antitone hC ht hqr).trans (div_le_div_of_nonneg_right hCM (Real.rpow_nonneg (by linarith) _))

theorem cutoff_support {ψ : ℝ → ℝ} (hψc : HasCompactSupport ψ) :
    ∃ S, ∀ s, S < |s| → ψ s = 0 ∧ deriv ψ s = 0 := by
  obtain ⟨S, hS⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  have hU : ∀ s', S < |s'| → ψ s' = 0 := fun s' hs' => image_eq_zero_of_notMem_tsupport (fun h => by
    have := hS h
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith)
  refine ⟨S, fun s hs => ⟨hU s hs, ?_⟩⟩
  have h : ψ =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hs] with s' hs'
    exact hU s' hs'
  rw [h.deriv_eq]
  exact deriv_const s 0

theorem box_support {E : Type*} [NormedAddCommGroup E] {F : ℝ × Space → E} {S R : ℝ}
    (h : ∀ s y, S < |s| ∨ R < ‖y‖ → F (s, y) = 0) : HasCompactSupport F := by
  refine HasCompactSupport.intro ((isCompact_Icc (a := -S) (b := S)).prod (isCompact_closedBall (0 : Space) R))
    fun z hz => ?_
  refine h z.1 z.2 ?_
  by_contra hn
  push Not at hn
  exact hz ⟨abs_le.1 hn.1, by simpa [Metric.mem_closedBall, dist_zero_right] using hn.2⟩

theorem sm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℝ → Space → E} (m : ℕ)
    {K q : ℝ} (hK : 0 ≤ K) (hq : 0 ≤ q) {a : ℝ → ℝ} {P : ℝ} (ha0 : ∀ s, 0 ≤ a s) (haP : ∀ s, a s ≤ P)
    (hb : ∀ s y, ‖h s y‖ ≤ a s * (K / (1 + ‖y‖) ^ q)) (s : ℝ) (y : Space) :
    ‖∫ w : ℝ × Space, kernel m w • h (s - w.1) (y - w.2)‖ ≤ P * (2 ^ q * K / (1 + ‖y‖) ^ q) := by
  refine kernel_integral_norm_le (K := fun z : ℝ × Space => h z.1 z.2) (z := (s, y)) m (fun w hw => ?_)
  show ‖h (s - w.1) (y - w.2)‖ ≤ _
  have hP : 0 ≤ P := (ha0 s).trans (haP s)
  refine (hb _ _).trans (mul_le_mul (haP _) (frac_shift hK hq y w.2 ((norm_snd_le w).trans hw.le))
    (by positivity) hP)

theorem sm_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℝ → Space → E} (m : ℕ) {S : ℝ}
    (hz : ∀ s y, S < |s| → h s y = 0) (s : ℝ) (y : Space) (hs : S + 1 < |s|) :
    ∫ w : ℝ × Space, kernel m w • h (s - w.1) (y - w.2) = 0 := by
  refine norm_le_zero_iff.1 (kernel_integral_norm_le (K := fun z : ℝ × Space => h z.1 z.2) (z := (s, y)) m
    (fun w hw => ?_))
  show ‖h (s - w.1) (y - w.2)‖ ≤ 0
  have h1 : |w.1| < 1 := by
    have := (norm_fst_le w).trans_lt hw
    rwa [Real.norm_eq_abs] at this
  have h2 := abs_sub_abs_le_abs_sub s w.1
  rw [hz _ _ (by linarith), norm_zero]

theorem columnSq_le (M : Space →L[ℝ] Space) : matSq M ≤ 3 * ‖M‖ ^ 2 := by
  unfold matSq
  have h : ∀ i : Fin 3, ‖M (unitVector i)‖ ^ 2 ≤ ‖M‖ ^ 2 := by
    intro i
    have h1 : ‖unitVector i‖ = 1 := by simp [unitVector]
    have h2 := M.le_opNorm (unitVector i)
    rw [h1, mul_one] at h2
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem trunc_zero0 {R S : ℝ} (hR : 0 < R) (hS : ∀ s, S < |s| → ψ s = 0 ∧ deriv ψ s = 0) (s : ℝ) (y : Space)
    (h : S < |s| ∨ 2 * R < ‖y‖) : trunc ψ ζ A R s y = 0 := by
  rcases h with h | h
  · simp [trunc, (hS s h).1]
  · exact trunc_far hR s h

theorem trunc_zero1 {R S : ℝ} (hR : 0 < R) (hS : ∀ s, S < |s| → ψ s = 0 ∧ deriv ψ s = 0) (s : ℝ) (y : Space)
    (h : S < |s| ∨ 2 * R < ‖y‖) : fderiv ℝ (trunc ψ ζ A R s) y = 0 := by
  rcases h with h | h
  · have e : trunc ψ ζ A R s = fun _ => 0 := by
      funext y'
      simp [trunc, (hS s h).1]
    rw [e]
    exact fderiv_const_apply 0
  · exact trunc_far_spaceDeriv hR s h

theorem trunc_zero2 (hψ : ContDiff ℝ ∞ ψ) (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2))
    (hA : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)) {R S : ℝ} (hR : 0 < R)
    (hS : ∀ s, S < |s| → ψ s = 0 ∧ deriv ψ s = 0) (s : ℝ) (y : Space)
    (h : S < |s| ∨ 2 * R < ‖y‖) : timeDerivative (trunc ψ ζ A R) s y = 0 := by
  rcases h with h | h
  · unfold timeDerivative
    rw [(trunc_time_hasDerivAt hψ hζ hA R s y).deriv, (hS s h).1, (hS s h).2, zero_smul, zero_smul, add_zero]
  · have e : (fun s' => trunc ψ ζ A R s' y) = fun _ => 0 := funext fun s' => trunc_far hR s' h
    unfold timeDerivative
    rw [e]
    exact deriv_const s 0

theorem glob_le {K q a P : ℝ} (hK : 0 ≤ K) (hq : 0 ≤ q) (ha : 0 ≤ a) (haP : a ≤ P) (y : Space) :
    a * (K / (1 + ‖y‖) ^ q) ≤ P * K := by
  have ht : 1 ≤ 1 + ‖y‖ := by have := norm_nonneg y; linarith
  exact mul_le_mul haP (div_le_self hK (Real.one_le_rpow ht hq)) (by positivity) (ha.trans haP)

theorem radial_le {K q : ℝ} (hK : 0 ≤ K) {L : Space →L[ℝ] Space} (y : Space)
    (hL : ‖L‖ ≤ K / (1 + ‖y‖) ^ (q + 1)) : ‖L y‖ ≤ K / (1 + ‖y‖) ^ q := by
  have ht0 : 0 < 1 + ‖y‖ := by positivity
  have h1 : ‖y‖ ≤ 1 + ‖y‖ := by linarith
  calc ‖L y‖ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
    _ ≤ K / (1 + ‖y‖) ^ (q + 1) * (1 + ‖y‖) := mul_le_mul hL h1 (norm_nonneg _) (by positivity)
    _ = K / (1 + ‖y‖) ^ q := by
        rw [Real.rpow_add_one ht0.ne']
        have := Real.rpow_pos_of_pos ht0 q
        field_simp

end Internal.TestDensity

end AdjointDefect

end Breakdown
