import Breakdown.FracCell.StHeightModeIbp
import Breakdown.FracCell.ModeWeakIdentity
import Breakdown.FracCell.LowEntry

open scoped ContDiff
open MeasureTheory Filter Topology Set

noncomputable section

namespace Breakdown.FracInternal.HeightModeIbp

def cutBump (a b : ℝ) (hab : a < b) (k : ℕ) : ContDiffBump ((a + b) / 2) where
  rIn := (b - a) / 2 - 2 * ((b - a) / (8 * (k + 1)))
  rOut := (b - a) / 2 - (b - a) / (8 * (k + 1))
  rIn_pos := by
    have h1 : (b - a) / (8 * (k + 1)) ≤ (b - a) / 8 := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    linarith
  rIn_lt_rOut := by
    have : 0 < (b - a) / (8 * (k + 1)) := by
      apply div_pos (by linarith); positivity
    linarith

theorem cutEps_pos (a b : ℝ) (hab : a < b) (k : ℕ) : 0 < (b - a) / (8 * ((k : ℝ) + 1)) := by
  apply div_pos (by linarith); positivity

theorem cutEps_le (a b : ℝ) (hab : a < b) (k : ℕ) : (b - a) / (8 * ((k : ℝ) + 1)) ≤ (b - a) / 8 := by
  apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem poly_smooth (P : Polynomial ℝ) : ContDiff ℝ ∞ (fun x => P.eval x) := by
  have h := P.contDiff_aeval (𝕜 := ℝ) (∞ : WithTop ℕ∞)
  have e : (fun x : ℝ => Polynomial.aeval x P) = fun x => P.eval x := by
    funext x
    rfl
  rwa [e] at h

theorem cutBump_zero (a b : ℝ) (hab : a < b) (k : ℕ) (x : ℝ)
    (hx : x ∉ Ioo (a + (b - a) / (8 * (k + 1))) (b - (b - a) / (8 * (k + 1)))) :
    cutBump a b hab k x = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simp only [cutBump, Real.dist_eq]
  simp only [mem_Ioo, not_and_or, not_lt] at hx
  have := cutEps_le a b hab k
  rcases hx with hx | hx
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

theorem cutBump_one (a b : ℝ) (hab : a < b) (k : ℕ) (x : ℝ)
    (hx : x ∈ Icc (a + 2 * ((b - a) / (8 * (k + 1)))) (b - 2 * ((b - a) / (8 * (k + 1))))) :
    cutBump a b hab k x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simp only [cutBump, Metric.mem_closedBall, Real.dist_eq]
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem cutBump_eventually (a b : ℝ) (hab : a < b) (x : ℝ) (hx : x ∈ Ioo a b) :
    ∀ᶠ k : ℕ in atTop, cutBump a b hab k x = 1 := by
  have ht : Tendsto (fun k : ℕ => 2 * ((b - a) / (8 * ((k : ℝ) + 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 := (h1.const_mul_atTop (by norm_num : (0 : ℝ) < 8)).inv_tendsto_atTop
    have h3 := h2.const_mul (2 * (b - a))
    simp only [mul_zero] at h3
    refine h3.congr (fun k => ?_)
    simp only [Pi.inv_apply]
    rw [div_eq_mul_inv]; ring
  have hm : 0 < min (x - a) (b - x) := lt_min (by linarith [hx.1]) (by linarith [hx.2])
  filter_upwards [(ht.eventually (gt_mem_nhds hm))] with k hk
  apply cutBump_one
  constructor <;> linarith [min_le_left (x - a) (b - x), min_le_right (x - a) (b - x)]

theorem cutBump_tendsto (a b : ℝ) (hab : a < b) (x : ℝ) (hx : x ∈ Ioo a b) :
    Tendsto (fun k => cutBump a b hab k x) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (EventuallyEq.symm (cutBump_eventually a b hab x hx))

theorem bump_bound (a b : ℝ) (hab : a < b) (k : ℕ) (q : ℝ → ℝ) (D : ℝ)
    (hq : ∀ x ∈ Icc a b, |q x| ≤ D) (hD : 0 ≤ D) (x : ℝ) : |cutBump a b hab k x * q x| ≤ D := by
  by_cases hx : x ∈ Icc a b
  · rw [abs_mul, abs_of_nonneg (ContDiffBump.nonneg _)]
    calc cutBump a b hab k x * |q x| ≤ 1 * D :=
          mul_le_mul (ContDiffBump.le_one _) (hq x hx) (abs_nonneg _) (by norm_num)
      _ = D := one_mul _
  · have hx' : x ∉ Ioo (a + (b - a) / (8 * ((k : ℝ) + 1))) (b - (b - a) / (8 * ((k : ℝ) + 1))) := by
      intro h; apply hx
      have := cutEps_pos a b hab k
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [cutBump_zero a b hab k x hx', zero_mul, abs_zero]
    exact hD

theorem approx_cont (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) :
    ∃ φ : ℕ → ℝ → ℝ, (∀ k, ContDiff ℝ ∞ (φ k)) ∧
      (∀ k, ∃ e, 0 < e ∧ ∀ x, x ∉ Ioo (a + e) (b - e) → φ k x = 0) ∧
      (∃ C, ∀ k x, |φ k x| ≤ C) ∧ ∀ x ∈ Ioo a b, Tendsto (fun k => φ k x) atTop (𝓝 (f x)) := by
  have hP : ∀ k : ℕ, ∃ P : Polynomial ℝ, ∀ x ∈ Icc a b, |P.eval x - f x| < 1 / ((k : ℝ) + 1) :=
    fun k => exists_polynomial_near_of_continuousOn a b f hf _ (by positivity)
  choose P hP using hP
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨fun k x => cutBump a b hab k x * (P k).eval x, fun k => ?_, fun k => ?_, ⟨D + 1, fun k x => ?_⟩, ?_⟩
  · exact (ContDiffBump.contDiff _).mul (poly_smooth _)
  · refine ⟨(b - a) / (8 * ((k : ℝ) + 1)), cutEps_pos a b hab k, fun x hx => ?_⟩
    simp only [cutBump_zero a b hab k x hx, zero_mul]
  · have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD a (left_mem_Icc.2 hab.le))
    show |cutBump a b hab k x * (P k).eval x| ≤ D + 1
    refine bump_bound a b hab k (fun y => (P k).eval y) (D + 1) (fun x hx => ?_) (by linarith) x
    have h1 := hP k x hx
    have h2 : |f x| ≤ D := by simpa [Real.norm_eq_abs] using hD x hx
    have h3 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have := abs_sub_abs_le_abs_sub ((P k).eval x) (f x)
    linarith
  · intro x hx
    have hPl : Tendsto (fun k : ℕ => (P k).eval x) atTop (𝓝 (f x)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Real.dist_eq]
      exact (hP k x (Ioo_subset_Icc_self hx)).le
    simpa using (cutBump_tendsto a b hab x hx).mul hPl


theorem bump_off (a b : ℝ) (hab : a < b) (k : ℕ) (x : ℝ) (hx : x ∉ Ioo a b) : cutBump a b hab k x = 0 := by
  apply cutBump_zero
  intro h; apply hx
  have := cutEps_pos a b hab k
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem approx_c1 (a b : ℝ) (hab : a < b) (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (ha : h a = 0) (hb : h b = 0) :
    ∃ β : ℕ → ℝ → ℝ, (∀ k, ContDiff ℝ ∞ (β k)) ∧ (∀ k x, x ∉ Icc a b → β k x = 0) ∧
      (∀ k x, x ∉ Ioo a b → deriv (β k) x = 0) ∧ (∀ k, Continuous (deriv (β k))) ∧
      (∃ C, ∀ k x, |β k x| ≤ C ∧ |deriv (β k) x| ≤ C) ∧
      ∀ x ∈ Ioo a b, Tendsto (fun k => β k x) atTop (𝓝 (h x)) ∧
        Tendsto (fun k => deriv (β k) x) atTop (𝓝 (deriv h x)) := by
  have hd : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hP : ∀ k : ℕ, ∃ P : Polynomial ℝ, ∀ x ∈ Icc a b, |P.eval x - deriv h x| < 1 / ((k : ℝ) + 1) :=
    fun k => exists_polynomial_near_of_continuousOn a b _ hd.continuousOn _ (by positivity)
  choose P hP using hP
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hd.continuousOn (s := Icc a b)
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD a (left_mem_Icc.2 hab.le))
  have hPb : ∀ k, ∀ x ∈ Icc a b, |(P k).eval x| ≤ D + 1 := by
    intro k x hx
    have h1 := hP k x hx
    have h2 : |deriv h x| ≤ D := by simpa [Real.norm_eq_abs] using hD x hx
    have h3 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have := abs_sub_abs_le_abs_sub ((P k).eval x) (deriv h x)
    linarith
  set η : ℝ → ℝ := (cutBump a b hab 0).normed volume with hη
  have hηs : ContDiff ℝ ∞ η := ContDiffBump.contDiff_normed _
  have hηoff : ∀ x, x ∉ Ioo a b → η x = 0 := by
    intro x hx
    have hx' : x ∉ Function.support η := by
      rw [hη, ContDiffBump.support_normed_eq]
      simp only [cutBump, Metric.mem_ball, Real.dist_eq, abs_lt, not_and_or, not_lt]
      simp only [mem_Ioo, not_and_or, not_lt] at hx
      norm_num
      rcases hx with hx | hx
      · left; linarith
      · right; linarith
    simpa using hx'
  have hηint : ∫ x in a..b, η x = 1 := by
    rw [intervalIntegral.integral_of_le hab.le, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact ContDiffBump.integral_normed _
    · intro x hx
      exact hηoff x (fun h' => hx (Ioo_subset_Ioc_self h'))
  obtain ⟨E, hE⟩ := isCompact_Icc.exists_bound_of_continuousOn hηs.continuous.continuousOn (s := Icc a b)
  have hE0 : 0 ≤ E := le_trans (norm_nonneg _) (hE a (left_mem_Icc.2 hab.le))
  have hηb : ∀ x, |η x| ≤ E := by
    intro x
    by_cases hx : x ∈ Icc a b
    · simpa [Real.norm_eq_abs] using hE x hx
    · rw [hηoff x (fun h' => hx (Ioo_subset_Icc_self h')), abs_zero]; exact hE0
  set g : ℕ → ℝ → ℝ := fun k x => cutBump a b hab k x * (P k).eval x with hg
  have hgs : ∀ k, ContDiff ℝ ∞ (g k) := fun k => (ContDiffBump.contDiff _).mul (poly_smooth _)
  have hgb : ∀ k x, |g k x| ≤ D + 1 := fun k x => bump_bound a b hab k _ (D + 1) (hPb k) (by linarith) x
  have hgoff : ∀ k x, x ∉ Ioo a b → g k x = 0 := by
    intro k x hx; simp only [hg, bump_off a b hab k x hx, zero_mul]
  set c : ℕ → ℝ := fun k => ∫ x in a..b, g k x with hc
  have hcb : ∀ k, |c k| ≤ (D + 1) * (b - a) := by
    intro k
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := g k) (C := D + 1)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hgb k x)
    rw [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < b - a)] at this
    exact this
  set γ : ℕ → ℝ → ℝ := fun k x => g k x - c k * η x with hγ
  have hγs : ∀ k, ContDiff ℝ ∞ (γ k) := fun k => (hgs k).sub (contDiff_const.mul hηs)
  have hγc : ∀ k, Continuous (γ k) := fun k => (hγs k).continuous
  have hγoff : ∀ k x, x ∉ Ioo a b → γ k x = 0 := by
    intro k x hx; simp only [hγ, hgoff k x hx, hηoff x hx, mul_zero, sub_zero]
  set C1 : ℝ := (D + 1) + (D + 1) * (b - a) * E with hC1
  have hC10 : 0 ≤ C1 := by
    have : 0 ≤ (D + 1) * (b - a) * E := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hE0
    linarith
  have hγb : ∀ k x, |γ k x| ≤ C1 := by
    intro k x
    have h1 := hgb k x
    have h2 : |c k * η x| ≤ (D + 1) * (b - a) * E := by
      rw [abs_mul]; exact mul_le_mul (hcb k) (hηb x) (abs_nonneg _) (by nlinarith)
    calc |γ k x| ≤ |g k x| + |c k * η x| := abs_sub _ _
      _ ≤ C1 := by linarith
  set β : ℕ → ℝ → ℝ := fun k x => ∫ t in a..x, γ k t with hβ
  have hβd : ∀ k x, HasDerivAt (β k) (γ k x) x := fun k x => ((hγc k).integral_hasStrictDerivAt a x).hasDerivAt
  have hβdeq : ∀ k, deriv (β k) = γ k := fun k => funext fun x => (hβd k x).deriv
  have hγint : ∀ k, ∫ x in a..b, γ k x = 0 := by
    intro k
    simp only [hγ]
    have i1 : IntervalIntegrable (g k) volume a b := (hgs k).continuous.intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x => c k * η x) volume a b :=
      (continuous_const.mul hηs.continuous).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul, hηint]
    simp [hc]
  have hβoff : ∀ k x, x ∉ Icc a b → β k x = 0 := by
    intro k x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · simp only [hβ]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => ?_)]
      · simp
      · rw [uIcc_of_ge hx.le] at ht
        exact hγoff k t (fun h' => by linarith [h'.1, ht.2])
    · simp only [hβ]
      rw [← intervalIntegral.integral_add_adjacent_intervals ((hγc k).intervalIntegrable a b)
        ((hγc k).intervalIntegrable b x), hγint k,
        intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => ?_)]
      · simp
      · rw [uIcc_of_le hx.le] at ht
        exact hγoff k t (fun h' => by linarith [h'.2, ht.1])
  have hgl : ∀ y ∈ Ioo a b, Tendsto (fun k => g k y) atTop (𝓝 (deriv h y)) := by
    intro y hy
    have hPl : Tendsto (fun k : ℕ => (P k).eval y) atTop (𝓝 (deriv h y)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Real.dist_eq]
      exact (hP k y (Ioo_subset_Icc_self hy)).le
    simpa using (cutBump_tendsto a b hab y hy).mul hPl
  have hcl : Tendsto c atTop (𝓝 0) := by
    have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume) (a := a) (b := b)
      (F := g) (f := deriv h) (fun _ => D + 1)
      (Eventually.of_forall fun k => (hgs k).continuous.aestronglyMeasurable)
      (Eventually.of_forall fun k => Eventually.of_forall fun x _ => by rw [Real.norm_eq_abs]; exact hgb k x)
      intervalIntegrable_const
      (by
        filter_upwards [Measure.ae_ne volume b] with y hyb hy
        rw [uIoc_of_le hab.le] at hy
        exact hgl y ⟨hy.1, lt_of_le_of_ne hy.2 hyb⟩)
    rw [intervalIntegral.integral_deriv_eq_sub' h rfl (fun x _ => (hh.differentiable one_ne_zero).differentiableAt)
      hd.continuousOn, ha, hb, sub_zero] at hlim
    exact hlim
  have hγl : ∀ y ∈ Ioo a b, Tendsto (fun k => γ k y) atTop (𝓝 (deriv h y)) := by
    intro y hy
    simpa using (hgl y hy).sub (hcl.mul_const (η y))
  refine ⟨β, fun k => ?_, hβoff, fun k x hx => by rw [hβdeq]; exact hγoff k x hx,
    fun k => by rw [hβdeq]; exact hγc k, ⟨C1 + C1 * (b - a), fun k x => ⟨?_, ?_⟩⟩, fun x hx => ⟨?_, ?_⟩⟩
  · rw [contDiff_infty_iff_deriv, hβdeq]
    exact ⟨fun x => (hβd k x).differentiableAt, hγs k⟩
  · by_cases hx : x ∈ Icc a b
    · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := x) (f := γ k) (C := C1)
        (fun t _ => by rw [Real.norm_eq_abs]; exact hγb k t)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - a)] at this
      have h2 : C1 * (x - a) ≤ C1 * (b - a) := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hC10
      simp only [hβ]
      linarith
    · rw [hβoff k x hx, abs_zero]; nlinarith
  · rw [hβdeq]
    have : 0 ≤ C1 * (b - a) := mul_nonneg hC10 (by linarith)
    linarith [hγb k x]
  · have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume) (a := a) (b := x)
      (F := γ) (f := deriv h) (fun _ => C1)
      (Eventually.of_forall fun k => (hγc k).aestronglyMeasurable)
      (Eventually.of_forall fun k => Eventually.of_forall fun y _ => by rw [Real.norm_eq_abs]; exact hγb k y)
      intervalIntegrable_const
      (Eventually.of_forall fun y hy => by
        rw [uIoc_of_le hx.1.le] at hy
        exact hγl y ⟨hy.1, lt_of_le_of_lt hy.2 hx.2⟩)
    rw [intervalIntegral.integral_deriv_eq_sub' h rfl (fun x _ => (hh.differentiable one_ne_zero).differentiableAt)
      hd.continuousOn, ha, sub_zero] at hlim
    exact hlim
  · exact (hγl x hx).congr (fun k => by rw [hβdeq])

theorem line_fst (c : ℝ) : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ c := by
  have h0 : volume ({c} ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp hpc
  exact hp ⟨hpc, trivial⟩

theorem line_snd (c : ℝ) : ∀ᵐ p : ℝ × ℝ ∂volume, p.2 ≠ c := by
  have h0 : volume ((univ : Set ℝ) ×ˢ {c}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp hpc
  exact hp ⟨trivial, hpc⟩

end Breakdown.FracInternal.HeightModeIbp

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis
open Breakdown.FracInternal.HeightModeIbp

theorem heightModeIbp_holds : HeightModeIbpStatement := by
  intro m n v G H hs K hK a
  have hA := LowEntry.Internal.modeVec_int K hK m n hs.velocity_six a
  have hB := LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two a 2
  refine ⟨hB, fun f h hf hh h1 h2 => ?_⟩
  obtain ⟨φ, hφs, hφsupp, ⟨Cφ, hCφ⟩, hφlim⟩ := approx_cont K.r₁ K.r₂ hK.r_order.2 f hf.continuousOn
  obtain ⟨β, hβs, hβ0, hβd0, hβdc, ⟨Cβ, hCβ⟩, hβlim⟩ := approx_c1 K.z₁ K.z₂ hK.z_order.2 h hh h1 h2
  have hCφ0 : 0 ≤ Cφ := le_trans (abs_nonneg _) (hCφ 0 0)
  have hCβ0 : 0 ≤ Cβ := le_trans (abs_nonneg _) (hCβ 0 0).1
  have hw : ContDiff ℝ ∞ K.lineWeight := by
    by_cases h0 : K.r₁ = 0
    · have e : K.lineWeight = fun r => r := funext fun r => by simp [CellBox.lineWeight, h0]
      rw [e]; exact contDiff_id
    · have e : K.lineWeight = fun _ => 1 := funext fun r => by simp [CellBox.lineWeight, h0]
      rw [e]; exact contDiff_const
  have key : ∀ k, ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
      ((φ k p.1 * deriv (β k) p.2 : ℝ) : ℂ) =
      -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((φ k p.1 * β k p.2 : ℝ) : ℂ) := by
    intro k
    set ψ : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * φ k p.1 * β k p.2 with hψ
    have hψs : ContDiff ℝ ∞ ψ :=
      ((hw.comp contDiff_fst).mul ((hφs k).comp contDiff_fst)).mul ((hβs k).comp contDiff_snd)
    obtain ⟨e, he, hφe⟩ := hφsupp k
    have hφoff : ∀ r, r ∉ Icc K.r₁ K.r₂ → φ k r = 0 :=
      fun r hr => hφe r (fun h' => hr ⟨by linarith [h'.1], by linarith [h'.2]⟩)
    have hψoff : ∀ p, p ∉ K.rect → ψ p = 0 := by
      intro p hp
      simp only [CellBox.rect, mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · simp [hψ, hφoff p.1 hp]
      · simp [hψ, hβ0 k p.2 hp]
    have hψc : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) hψoff
    have hψpos : ∀ p ∈ tsupport ψ, 0 < p.1 := by
      intro p hp
      have hsub : tsupport ψ ⊆ {q : ℝ × ℝ | K.r₁ + e ≤ q.1} := by
        refine closure_minimal (fun q hq => ?_) (isClosed_le continuous_const continuous_fst)
        by_contra hc
        apply hq
        simp only [mem_ofPred_eq, not_le] at hc
        simp [hψ, hφe q.1 (fun h' => by linarith [h'.1])]
      have := hsub hp
      simp only [mem_ofPred_eq] at this
      linarith [hK.r_order.1]
    have hder : ∀ p, fderiv ℝ ψ p (0, 1) = K.lineWeight p.1 * φ k p.1 * deriv (β k) p.2 := by
      intro p
      have hl : HasDerivAt (fun z : ℝ => (p.1, z)) ((0 : ℝ), (1 : ℝ)) p.2 :=
        (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
      have h1 := ((hψs.differentiable (by simp)) (p.1, p.2)).hasFDerivAt.comp_hasDerivAt p.2 hl
      have h2 : HasDerivAt (fun z => ψ (p.1, z)) (K.lineWeight p.1 * φ k p.1 * deriv (β k) p.2) p.2 := by
        have h4 := (((hβs k).differentiable (by simp)) p.2).hasDerivAt.const_mul (K.lineWeight p.1 * φ k p.1)
        simpa only [hψ] using h4
      have h3 := h1.unique h2
      rw [Prod.mk.eta] at h3
      exact h3
    have hid := (modeWeakIdentity m v G H hs n a ψ hψs hψc hψpos).2.1
    have eL : ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a =
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
          ((φ k p.1 * deriv (β k) p.2 : ℝ) : ℂ) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · congr 1; funext p; rw [hder]; push_cast; ring
      · intro p hp
        simp only [CellBox.rect, mem_prod, not_and_or] at hp
        rcases hp with hp | hp
        · simp [hφoff p.1 hp]
        · simp [hβd0 k p.2 (fun h' => hp (Ioo_subset_Icc_self h'))]
    have eR : ∫ p, (ψ p : ℂ) * gradMode m n G a 2 p =
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((φ k p.1 * β k p.2 : ℝ) : ℂ) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · congr 1; funext p; simp only [hψ]; push_cast; ring
      · intro p hp
        simp only [CellBox.rect, mem_prod, not_and_or] at hp
        rcases hp with hp | hp
        · simp [hφoff p.1 hp]
        · simp [hβ0 k p.2 hp]
    rw [eL, eR] at hid
    exact hid
  have hint : ∀ᵐ p ∂(volume.restrict K.rect), p.1 ∈ Ioo K.r₁ K.r₂ ∧ p.2 ∈ Ioo K.z₁ K.z₂ := by
    filter_upwards [ae_restrict_mem (LowEntry.Internal.rect_meas K), ae_restrict_of_ae (line_fst K.r₁),
      ae_restrict_of_ae (line_fst K.r₂), ae_restrict_of_ae (line_snd K.z₁), ae_restrict_of_ae (line_snd K.z₂)]
      with p hp hr1 hr2 hz1 hz2
    exact ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm hr1), lt_of_le_of_ne hp.1.2 hr2⟩,
      ⟨lt_of_le_of_ne hp.2.1 (Ne.symm hz1), lt_of_le_of_ne hp.2.2 hz2⟩⟩
  have hlimL : Tendsto (fun k => ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
      ((φ k p.1 * deriv (β k) p.2 : ℝ) : ℂ)) atTop
      (𝓝 (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a * ((f p.1 * deriv h p.2 : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun p => ‖(K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a‖ * (Cφ * Cβ)) (fun k => ?_)
      (hA.norm.mul_const _) (fun k => ?_) ?_
    · exact hA.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        (((hφs k).continuous.comp continuous_fst).mul ((hβdc k).comp continuous_snd))).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hCφ k p.1) (hCβ k p.2).2 (abs_nonneg _) hCφ0) (norm_nonneg _)
    · filter_upwards [hint] with p hp
      exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
        ((hφlim p.1 hp.1).mul (hβlim p.2 hp.2).2))
  have hlimR : Tendsto (fun k => ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p *
      ((φ k p.1 * β k p.2 : ℝ) : ℂ)) atTop
      (𝓝 (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((f p.1 * h p.2 : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun p => ‖(K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p‖ * (Cφ * Cβ)) (fun k => ?_)
      (hB.norm.mul_const _) (fun k => ?_) ?_
    · exact hB.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        (((hφs k).continuous.comp continuous_fst).mul ((hβs k).continuous.comp continuous_snd))).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hCφ k p.1) (hCβ k p.2).1 (abs_nonneg _) hCφ0) (norm_nonneg _)
    · filter_upwards [hint] with p hp
      exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
        ((hφlim p.1 hp.1).mul (hβlim p.2 hp.2).1))
  exact tendsto_nhds_unique hlimL (hlimR.neg.congr (fun k => (key k).symm))

end Breakdown.CellCert.CellFormula

