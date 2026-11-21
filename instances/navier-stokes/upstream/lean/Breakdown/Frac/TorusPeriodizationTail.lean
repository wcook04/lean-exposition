import Breakdown.Frac.StTorusApprox
import Breakdown.Frac.StOperator
import Breakdown.Torus.HeatComparisonStep

open MeasureTheory Set Real Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Breakdown.Periodic

private lemma tail_coord_le (v : Space) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i

private lemma tail_center_apply (i : Fin 3) : center i = 1 / 2 := by
  simp [center, unitVector, Pi.single_apply]

private lemma tail_freq_apply (k : Lattice) (i : Fin 3) : freq k i = (k i : ℝ) := by
  simp [freq, unitVector, Pi.single_apply]

private lemma tail_freq_zero : freq 0 = 0 := by
  simp [freq]

private lemma tail_lattice_eq {k k' : Lattice} (h : ‖freq k - freq k'‖ < 1) : k = k' := by
  funext i
  have h1 := (tail_coord_le (freq k - freq k') i).trans_lt h
  rw [PiLp.sub_apply, tail_freq_apply, tail_freq_apply] at h1
  have h3 : |k i - k' i| < 1 := by
    have : |((k i - k' i : ℤ) : ℝ)| < 1 := by push_cast; exact h1
    exact_mod_cast this
  have := abs_lt.1 h3
  omega

private lemma tail_supp {f : Space → Space}
    (hs : ∀ x, f x ≠ 0 → dist x center ≤ centralRadius / 2) {y : Space} (hy : f y ≠ 0) :
    ‖y - center‖ ≤ 1 / 8 := by
  have := hs y hy
  rw [dist_eq_norm] at this
  simp only [centralRadius] at this
  linarith

private lemma tail_unique {f : Space → Space}
    (hs : ∀ x, f x ≠ 0 → dist x center ≤ centralRadius / 2) {y y' : Space} {j j' : Lattice}
    (hyy : ‖y - y'‖ < 3 / 4) (h : f (y + freq j) ≠ 0) (h' : f (y' + freq j') ≠ 0) : j = j' := by
  apply tail_lattice_eq
  have a := tail_supp hs h
  have b := tail_supp hs h'
  have e : freq j - freq j' = (y + freq j - center) - (y' + freq j' - center) - (y - y') := by
    abel
  rw [e]
  calc _ ≤ ‖(y + freq j - center) - (y' + freq j' - center)‖ + ‖y - y'‖ := norm_sub_le _ _
    _ ≤ ‖y + freq j - center‖ + ‖y' + freq j' - center‖ + ‖y - y'‖ := by
        gcongr; exact norm_sub_le _ _
    _ < 1 := by linarith

private lemma tail_local {f : Space → Space}
    (hs : ∀ x, f x ≠ 0 → dist x center ≤ centralRadius / 2) (y₀ : Space) :
    ∃ j₀ : Lattice, ∀ y ∈ Metric.ball y₀ (1 / 4), ∀ j ≠ j₀, f (y + freq j) = 0 := by
  by_cases h : ∃ y₁ ∈ Metric.ball y₀ (1 / 4), ∃ j₁, f (y₁ + freq j₁) ≠ 0
  · obtain ⟨y₁, hy₁, j₁, hj₁⟩ := h
    refine ⟨j₁, fun y hy j hj => ?_⟩
    by_contra hne
    apply hj
    refine tail_unique hs ?_ hne hj₁
    rw [Metric.mem_ball, dist_eq_norm] at hy hy₁
    calc ‖y - y₁‖ = ‖(y - y₀) - (y₁ - y₀)‖ := by congr 1; abel
      _ ≤ ‖y - y₀‖ + ‖y₁ - y₀‖ := norm_sub_le _ _
      _ < 3 / 4 := by linarith
  · push Not at h
    exact ⟨0, fun y hy j _ => h y hy j⟩

private lemma tail_contDiff {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (hs : ∀ x, f x ≠ 0 → dist x center ≤ centralRadius / 2) :
    ContDiff ℝ ∞ (latticePeriodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro y₀
  obtain ⟨j₀, hj₀⟩ := tail_local hs y₀
  have hc : ContDiffAt ℝ ∞ (fun y => f (y + freq j₀)) y₀ :=
    (hf.comp (contDiff_id.add contDiff_const)).contDiffAt
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds y₀ (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
  simp only [latticePeriodize]
  exact tsum_eq_single j₀ (hj₀ y hy)

private lemma tail_cases {f : Space → Space}
    (hs : ∀ x, f x ≠ 0 → dist x center ≤ centralRadius / 2) (y : Space) :
    latticePeriodize f y - f y = 0 ∨
      ∃ j ≠ 0, latticePeriodize f y - f y = f (y + freq j) ∧ f (y + freq j) ≠ 0 := by
  by_cases h : ∃ j ≠ 0, f (y + freq j) ≠ 0
  · obtain ⟨j₁, hj₁, hne⟩ := h
    right
    have hu : ∀ j ≠ j₁, f (y + freq j) = 0 := fun j hj => by
      by_contra h'
      exact hj (tail_unique hs (by rw [sub_self, norm_zero]; norm_num) h' hne)
    have h0 : f y = 0 := by simpa [tail_freq_zero] using hu 0 (Ne.symm hj₁)
    refine ⟨j₁, hj₁, ?_, hne⟩
    simp only [latticePeriodize]
    rw [tsum_eq_single j₁ hu, h0, sub_zero]
  · left
    push Not at h
    simp only [latticePeriodize]
    rw [tsum_eq_single 0 h, tail_freq_zero, add_zero, sub_self]

private lemma tail_cell_norm {x : Space} (hx : x ∈ cell) : ‖x - center‖ ≤ 1 := by
  have hsq : ‖x - center‖ ^ 2 ≤ 3 / 4 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    have hb : ∀ i, ‖(x - center) i‖ ^ 2 ≤ 1 / 4 := fun i => by
      rw [PiLp.sub_apply, tail_center_apply, Real.norm_eq_abs, sq_abs]
      have := hx i
      rw [mem_Icc] at this
      nlinarith [this.1, this.2]
    linarith [hb 0, hb 1, hb 2]
  nlinarith [norm_nonneg (x - center)]

private lemma tail_geom {f : Space → Space}
    (hs : ∀ x, f x ≠ 0 → dist x center ≤ centralRadius / 2) {x z : Space} (hx : x ∈ cell)
    {j : Lattice} (hj : j ≠ 0) (h : f (z + (x + freq j)) ≠ 0) :
    3 / 8 ≤ ‖z‖ ∧ (1 + ‖freq j‖) / 8 ≤ ‖z‖ := by
  have hw := tail_supp hs h
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hj
  have hji : (1 : ℝ) ≤ |(j i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
  have hwi := (tail_coord_le _ i).trans hw
  rw [PiLp.sub_apply, PiLp.add_apply, PiLp.add_apply, tail_freq_apply, tail_center_apply] at hwi
  have hxi := hx i
  rw [mem_Icc] at hxi
  have hzi := tail_coord_le z i
  have h38 : 3 / 8 ≤ ‖z‖ := by
    rcases le_abs'.1 hji with hn | hp
    · have := (abs_le.1 hwi).1
      have : 3 / 8 ≤ z i := by linarith
      linarith [le_abs_self (z i)]
    · have := (abs_le.1 hwi).2
      have : z i ≤ -(3 / 8) := by linarith
      linarith [neg_abs_le (z i)]
  refine ⟨h38, ?_⟩
  have hc := tail_cell_norm hx
  have e1 : z + freq j = (z + (x + freq j) - center) - (x - center) := by abel
  have h1 : ‖z + freq j‖ ≤ 9 / 8 := by
    rw [e1]
    calc _ ≤ ‖z + (x + freq j) - center‖ + ‖x - center‖ := norm_sub_le _ _
      _ ≤ 9 / 8 := by linarith
  have e2 : freq j = (z + freq j) - z := by abel
  have h2 : ‖freq j‖ ≤ ‖z + freq j‖ + ‖z‖ := by
    calc ‖freq j‖ = ‖(z + freq j) - z‖ := by rw [← e2]
      _ ≤ _ := norm_sub_le _ _
  by_cases hb : ‖freq j‖ ≤ 2
  · linarith
  · linarith

private lemma tail_summable (α : ℝ) (h1 : 1 < α) :
    Summable (fun j : Lattice => ((1 + ‖freq j‖) / 8) ^ (-(3 + 2 * α))) := by
  have hd := StepSum.Internal.summable_decay 1 one_pos
  simp only [one_smul] at hd
  refine Summable.of_nonneg_of_le (fun j => Real.rpow_nonneg (by positivity) _) (fun j => ?_)
    (hd.mul_right ((8 : ℝ)⁻¹ ^ (-(3 + 2 * α))))
  rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by norm_num)]
  gcongr
  all_goals linarith [norm_nonneg (freq j)]

theorem fracPeriodizationTail_of (α : ℝ) (h1 : 1 < α) (h2 : α < 3 / 2)
    (hAdd : AdditivityStatement) (hI : RemainderIntegrableStatement)
    (hN : NormalizerStatement) : FracPeriodizationTail α := by
  set c : Lattice → ℝ := fun j => ((1 + ‖freq j‖) / 8) ^ (-(3 + 2 * α)) with hc_def
  have hcn : ∀ j, 0 ≤ c j := fun j => Real.rpow_nonneg (by positivity) _
  have hsum := tail_summable α h1
  set S : ℝ := ∑' j, c j with hS_def
  have hS : 0 ≤ S := tsum_nonneg hcn
  refine ⟨|(fractionalNormalizer α)⁻¹| * S + 1, by positivity, ?_⟩
  intro f hf hs x hx
  have hfc : Continuous f := hf.continuous
  have hcs : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_closedBall center (centralRadius / 2))
      (fun y hy => by
        by_contra h
        exact hy (Metric.mem_closedBall.2 (hs y h)))
  obtain ⟨Cf, hCf⟩ := hfc.bounded_above_of_compact_support hcs
  set g : Space → Space := fun y => latticePeriodize f y - f y with hg_def
  have hper : latticePeriodize f = f + g := by
    funext y
    simp [g]
  have hgd : ContDiff ℝ ∞ g := (tail_contDiff hf hs).sub hf
  have hCg : ∀ y, ‖g y‖ ≤ Cf := fun y => by
    rcases tail_cases hs y with h0 | ⟨j, _, heq, _⟩
    · simp only [g, h0, norm_zero]
      exact (norm_nonneg _).trans (hCf y)
    · simp only [g, heq]
      exact hCf _
  have hadd := hAdd α f g x (hI α h1 h2 f hf (Or.inr ⟨Cf, hCf⟩) x)
    (hI α h1 h2 g hgd (Or.inr ⟨Cf, hCg⟩) x) (hf.differentiable (by simp) x)
    (hgd.differentiable (by simp) x) (hf.contDiffAt.of_le (by norm_cast))
    (hgd.contDiffAt.of_le (by norm_cast))
  rw [hper, hadd, add_sub_cancel_left]
  have hloc : g =ᶠ[𝓝 x] fun _ => (0 : Space) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 3 / 8)] with y hy
    rcases tail_cases hs y with h0 | ⟨j, hj, _, hne⟩
    · exact h0
    · exfalso
      have hne' : f ((y - x) + (x + freq j)) ≠ 0 := by
        rwa [show (y - x) + (x + freq j) = y + freq j by abel]
      have := (tail_geom hs hx hj hne').1
      rw [Metric.mem_ball, dist_eq_norm] at hy
      linarith
  have hg0 : g x = 0 := hloc.eq_of_nhds
  have hd0 : fderiv ℝ g x = 0 := by
    rw [hloc.fderiv_eq]
    simp
  have hd2 : iteratedFDeriv ℝ 2 g x = 0 := by
    rw [(hloc.iteratedFDeriv ℝ 2).eq_of_nhds]
    simp
  have hrem : ∀ z, secondOrderRemainder g x z = g (x + z) := fun z => by
    simp [secondOrderRemainder, hg0, hd0, hd2]
  unfold fractionalPowerAt
  simp_rw [hrem]
  have hint : Integrable (fun y => ‖f y‖) := (hfc.integrable_of_hasCompactSupport hcs).norm
  have hpt : ∀ z, ENNReal.ofReal ‖‖z‖ ^ (-(3 + 2 * α)) • g (x + z)‖ ≤
      ∑' j, ENNReal.ofReal (c j) * ENNReal.ofReal ‖f (z + (x + freq j))‖ := fun z => by
    rcases tail_cases hs (x + z) with h0 | ⟨j, hj, heq, hne⟩
    · simp only [g, h0, smul_zero, norm_zero, ENNReal.ofReal_zero]
      exact bot_le
    · have e : x + z + freq j = z + (x + freq j) := by abel
      rw [e] at heq hne
      have hz := (tail_geom hs hx hj hne).2
      have hK : ‖z‖ ^ (-(3 + 2 * α)) ≤ c j :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hz (by linarith)
      refine le_trans ?_ (ENNReal.le_tsum j)
      rw [← ENNReal.ofReal_mul (hcn j), norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      simp only [g, heq]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have hmeas : ∀ j, Measurable fun z => ENNReal.ofReal ‖f (z + (x + freq j))‖ := fun j =>
    ((hfc.comp (continuous_add_const _)).norm.measurable).ennreal_ofReal
  have hlint : ∫⁻ z, ENNReal.ofReal ‖‖z‖ ^ (-(3 + 2 * α)) • g (x + z)‖ ≤
      ENNReal.ofReal (S * ∫ y, ‖f y‖) := by
    calc ∫⁻ z, ENNReal.ofReal ‖‖z‖ ^ (-(3 + 2 * α)) • g (x + z)‖
        ≤ ∫⁻ z, ∑' j, ENNReal.ofReal (c j) * ENNReal.ofReal ‖f (z + (x + freq j))‖ :=
          lintegral_mono hpt
      _ = ∑' j, ∫⁻ z, ENNReal.ofReal (c j) * ENNReal.ofReal ‖f (z + (x + freq j))‖ :=
          lintegral_tsum fun j => (measurable_const.mul (hmeas j)).aemeasurable
      _ = ∑' j, ENNReal.ofReal (c j) * ∫⁻ z, ENNReal.ofReal ‖f z‖ := by
          congr 1
          funext j
          rw [lintegral_const_mul _ (hmeas j),
            lintegral_add_right_eq_self (fun z => ENNReal.ofReal ‖f z‖) (x + freq j)]
      _ = (∑' j, ENNReal.ofReal (c j)) * ∫⁻ z, ENNReal.ofReal ‖f z‖ := ENNReal.tsum_mul_right
      _ = ENNReal.ofReal S * ENNReal.ofReal (∫ y, ‖f y‖) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg hcn hsum,
            ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => norm_nonneg _)]
      _ = ENNReal.ofReal (S * ∫ y, ‖f y‖) := (ENNReal.ofReal_mul hS).symm
  have hI0 : 0 ≤ ∫ y, ‖f y‖ := integral_nonneg fun _ => norm_nonneg _
  have hbound : ‖∫ z, ‖z‖ ^ (-(3 + 2 * α)) • g (x + z)‖ ≤ S * ∫ y, ‖f y‖ := by
    refine (norm_integral_le_lintegral_norm _).trans ?_
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint).trans ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg hS hI0)]
  rw [norm_smul, Real.norm_eq_abs]
  calc |(fractionalNormalizer α)⁻¹| * ‖∫ z, ‖z‖ ^ (-(3 + 2 * α)) • g (x + z)‖
      ≤ |(fractionalNormalizer α)⁻¹| * (S * ∫ y, ‖f y‖) :=
        mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ ≤ (|(fractionalNormalizer α)⁻¹| * S + 1) * ∫ y, ‖f y‖ := by nlinarith [abs_nonneg (fractionalNormalizer α)⁻¹]

end Breakdown.Periodic
