import Breakdown.FracCell.VelocityTailSt
import Breakdown.FracCell.ModeRadialWeak

open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

namespace ModeRadialLineInternal

def bumpAt (k : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / ((k : ℝ) + 4)
  rOut := 2 / ((k : ℝ) + 4)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply div_lt_div_of_pos_right (by norm_num) (by positivity)

def width (k : ℕ) : ℝ := 2 / ((k : ℝ) + 4)

def kern (k : ℕ) (t : ℝ) : ℝ := (bumpAt k).normed volume t

def step (k : ℕ) (s : ℝ) : ℝ := ∫ t in (-1 : ℝ)..s, kern k t

def test (k : ℕ) (x y : ℝ) (r : ℝ) : ℝ := step k (r - x) - step k (r - y)

lemma width_pos (k : ℕ) : 0 < width k := by unfold width; positivity

lemma width_le (k : ℕ) : width k ≤ 1 / 2 := by
  unfold width
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [div_le_iff₀ (by positivity)]
  linarith

lemma width_tendsto : Tendsto width atTop (𝓝 0) := by
  unfold width
  exact Tendsto.div_atTop tendsto_const_nhds
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

lemma width_eventually {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ k in atTop, width k < δ :=
  width_tendsto.eventually (gt_mem_nhds hδ)

lemma kern_nonneg (k : ℕ) (t : ℝ) : 0 ≤ kern k t := ContDiffBump.nonneg_normed _ _

lemma kern_cont (k : ℕ) : Continuous (kern k) := ContDiffBump.continuous_normed _

lemma kern_integrable (k : ℕ) : Integrable (kern k) := ContDiffBump.integrable_normed _

lemma kern_int (k : ℕ) : ∫ t, kern k t = 1 := ContDiffBump.integral_normed _

lemma kern_zero (k : ℕ) {t : ℝ} (h : width k ≤ |t|) : kern k t = 0 := by
  by_contra hne
  have hs : t ∈ Function.support (kern k) := hne
  have hr : (bumpAt k).rOut = width k := rfl
  rw [show kern k = (bumpAt k).normed volume from rfl, ContDiffBump.support_normed_eq] at hs
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, hr] at hs
  linarith

lemma kern_bound (k : ℕ) : ∃ C, ∀ t, |kern k t| ≤ C := by
  obtain ⟨C, hC⟩ := (kern_cont k).bounded_above_of_compact_support
    (ContDiffBump.hasCompactSupport_normed (bumpAt k))
  exact ⟨C, fun t => by simpa [Real.norm_eq_abs] using hC t⟩

lemma step_hasDeriv (k : ℕ) (s : ℝ) : HasDerivAt (step k) (kern k s) s :=
  ((kern_cont k).integral_hasStrictDerivAt (-1) s).hasDerivAt

lemma step_cont (k : ℕ) : Continuous (step k) :=
  continuous_iff_continuousAt.2 fun s => (step_hasDeriv k s).continuousAt

lemma step_low (k : ℕ) {s : ℝ} (h : s ≤ -width k) : step k s = 0 := by
  unfold step
  have hw := width_le k
  have hw0 := width_pos k
  have heq : EqOn (kern k) (fun _ => (0 : ℝ)) (uIcc (-1) s) := by
    intro t ht
    apply kern_zero
    rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
  rw [intervalIntegral.integral_congr heq]
  simp

lemma step_high (k : ℕ) {s : ℝ} (h : width k ≤ s) : step k s = 1 := by
  unfold step
  have hw := width_le k
  have hw0 := width_pos k
  rw [intervalIntegral.integral_of_le (by linarith : (-1 : ℝ) ≤ s),
    setIntegral_eq_integral_of_forall_compl_eq_zero, kern_int]
  intro t ht
  apply kern_zero
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
  rcases ht with h1 | h1
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma step_nonneg (k : ℕ) (s : ℝ) : 0 ≤ step k s := by
  by_cases h : -1 ≤ s
  · exact intervalIntegral.integral_nonneg h (fun t _ => kern_nonneg k t)
  · rw [step_low k (by linarith [width_le k])]

lemma step_le_one (k : ℕ) (s : ℝ) : step k s ≤ 1 := by
  by_cases h : -1 ≤ s
  · rw [step, intervalIntegral.integral_of_le h, ← kern_int k]
    exact setIntegral_le_integral (kern_integrable k) (Eventually.of_forall (kern_nonneg k))
  · rw [step_low k (by linarith [width_le k])]; norm_num

lemma abs_step_le (k : ℕ) (s : ℝ) : |step k s| ≤ 1 :=
  abs_le.2 ⟨by linarith [step_nonneg k s], step_le_one k s⟩

lemma test_hasDeriv (k : ℕ) (x y r : ℝ) :
    HasDerivAt (test k x y) (kern k (r - x) - kern k (r - y)) r := by
  have h1 := HasDerivAt.comp_sub_const r x (step_hasDeriv k (r - x))
  have h2 := HasDerivAt.comp_sub_const r y (step_hasDeriv k (r - y))
  exact h1.sub h2

lemma test_deriv (k : ℕ) (x y r : ℝ) : deriv (test k x y) r = kern k (r - x) - kern k (r - y) :=
  (test_hasDeriv k x y r).deriv

lemma test_deriv_cont (k : ℕ) (x y : ℝ) : Continuous (deriv (test k x y)) := by
  rw [show deriv (test k x y) = fun r => kern k (r - x) - kern k (r - y) from
    funext (test_deriv k x y)]
  exact ((kern_cont k).comp (continuous_id.sub continuous_const)).sub
    ((kern_cont k).comp (continuous_id.sub continuous_const))

lemma test_contDiff (k : ℕ) (x y : ℝ) : ContDiff ℝ 1 (test k x y) :=
  contDiff_one_iff_deriv.2 ⟨fun r => (test_hasDeriv k x y r).differentiableAt, test_deriv_cont k x y⟩

lemma test_cont (k : ℕ) (x y : ℝ) : Continuous (test k x y) :=
  ((step_cont k).comp (continuous_id.sub continuous_const)).sub
    ((step_cont k).comp (continuous_id.sub continuous_const))

lemma test_deriv_bound (k : ℕ) (x y : ℝ) : ∃ C, ∀ r, |deriv (test k x y) r| ≤ C := by
  obtain ⟨C, hC⟩ := kern_bound k
  refine ⟨2 * C, fun r => ?_⟩
  rw [test_deriv]
  have h1 := abs_le.1 (hC (r - x))
  have h2 := abs_le.1 (hC (r - y))
  exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

lemma abs_test_le (k : ℕ) (x y r : ℝ) : |test k x y r| ≤ 2 := by
  unfold test
  have h1 := abs_le.1 (abs_step_le k (r - x))
  have h2 := abs_le.1 (abs_step_le k (r - y))
  exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩


lemma ae_ne_pt (c : ℝ) : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ c := by
  rw [ae_iff]
  simp

lemma integrable_kern_mul {k : ℕ} {a b : ℝ} {u : ℝ → ℂ} (hu : IntegrableOn u (Icc a b)) (x : ℝ) :
    IntegrableOn (fun r => ((kern k (r - x) : ℝ) : ℂ) * u r) (Icc a b) := by
  obtain ⟨C, hC⟩ := kern_bound k
  refine Integrable.bdd_mul (c := C) hu ?_ ?_
  · exact (Complex.continuous_ofReal.comp ((kern_cont k).comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable
  · exact Eventually.of_forall fun r => by
      show ‖((kern k (r - x) : ℝ) : ℂ)‖ ≤ C
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hC _

lemma integrable_step_mul {k : ℕ} {a b : ℝ} {g : ℝ → ℂ}
    (hg : ∀ x', a < x' → IntegrableOn g (Icc x' b)) {x : ℝ} (hx : a < x - width k) :
    IntegrableOn (fun r => ((step k (r - x) : ℝ) : ℂ) * g r) (Icc a b) := by
  have h2 : IntegrableOn (fun r => ((step k (r - x) : ℝ) : ℂ) * g r) (Icc (x - width k) b) := by
    refine Integrable.bdd_mul (c := 1) (hg _ hx) ?_ ?_
    · exact (Complex.continuous_ofReal.comp ((step_cont k).comp
        (continuous_id.sub continuous_const))).aestronglyMeasurable
    · exact Eventually.of_forall fun r => by
        show ‖((step k (r - x) : ℝ) : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_step_le k _
  have h1 : IntegrableOn (fun r => ((step k (r - x) : ℝ) : ℂ) * g r) (Icc a (x - width k)) := by
    refine (integrableOn_zero).congr_fun (fun r hr => ?_) measurableSet_Icc
    show (0 : ℂ) = ((step k (r - x) : ℝ) : ℂ) * g r
    rw [step_low k (by linarith [hr.2])]
    simp
  refine (h1.union h2).mono_set fun r hr => ?_
  by_cases h : r ≤ x - width k
  · exact Or.inl ⟨hr.1, h⟩
  · exact Or.inr ⟨le_of_lt (not_le.1 h), hr.2⟩

def avgVal (k : ℕ) (a b : ℝ) (u g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ r in Icc a b, (((kern k (r - x) : ℝ) : ℂ) * u r + ((step k (r - x) : ℝ) : ℂ) * g r)

lemma avgVal_cont {k : ℕ} {a b : ℝ} {u g : ℝ → ℂ} (hu : IntegrableOn u (Icc a b))
    (hg : ∀ x', a < x' → IntegrableOn g (Icc x' b)) {x0 : ℝ} (hx0 : a < x0 - width k) :
    ContinuousAt (avgVal k a b u g) x0 := by
  obtain ⟨C, hC⟩ := kern_bound k
  have hax1 : a < (a + (x0 - width k)) / 2 := by linarith
  have hnb : ∀ᶠ x in 𝓝 x0, (a + (x0 - width k)) / 2 < x - width k :=
    ((continuous_sub_right (width k)).tendsto x0).eventually (lt_mem_nhds (show _ < x0 - width k by linarith))
  have hmeas : ∀ᶠ x in 𝓝 x0, AEStronglyMeasurable (fun r =>
      ((kern k (r - x) : ℝ) : ℂ) * u r + ((step k (r - x) : ℝ) : ℂ) * g r) (volume.restrict (Icc a b)) := by
    filter_upwards [hnb] with x hx
    exact ((integrable_kern_mul hu x).add (integrable_step_mul hg (by linarith))).aestronglyMeasurable
  have hbd : ∀ᶠ x in 𝓝 x0, ∀ᵐ r ∂(volume.restrict (Icc a b)),
      ‖((kern k (r - x) : ℝ) : ℂ) * u r + ((step k (r - x) : ℝ) : ℂ) * g r‖ ≤
        C * ‖u r‖ + Set.indicator (Icc ((a + (x0 - width k)) / 2) b) (fun r => ‖g r‖) r := by
    filter_upwards [hnb] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    · by_cases h : (a + (x0 - width k)) / 2 ≤ r
      · rw [Set.indicator_of_mem (show r ∈ Icc ((a + (x0 - width k)) / 2) b from ⟨h, hr.2⟩), norm_mul,
          Complex.norm_real, Real.norm_eq_abs]
        calc |step k (r - x)| * ‖g r‖ ≤ 1 * ‖g r‖ :=
              mul_le_mul_of_nonneg_right (abs_step_le k _) (norm_nonneg _)
          _ = ‖g r‖ := one_mul _
      · rw [step_low k (by linarith [not_le.1 h])]
        simp only [Complex.ofReal_zero, zero_mul, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
  have hbi : Integrable (fun r => C * ‖u r‖ + Set.indicator (Icc ((a + (x0 - width k)) / 2) b)
      (fun r => ‖g r‖) r) (volume.restrict (Icc a b)) :=
    (hu.norm.const_mul C).add ((IntegrableOn.integrable_indicator (hg _ hax1).norm measurableSet_Icc).integrableOn)
  have hc : ∀ᵐ r ∂(volume.restrict (Icc a b)), ContinuousAt (fun x =>
      ((kern k (r - x) : ℝ) : ℂ) * u r + ((step k (r - x) : ℝ) : ℂ) * g r) x0 :=
    Eventually.of_forall fun r =>
      (((Complex.continuous_ofReal.comp ((kern_cont k).comp (continuous_const.sub continuous_id))).mul
        continuous_const).add
        ((Complex.continuous_ofReal.comp ((step_cont k).comp (continuous_const.sub continuous_id))).mul
          continuous_const)).continuousAt
  exact continuousAt_of_dominated hmeas hbd hbi hc

lemma step_limit {a b : ℝ} {g : ℝ → ℂ} (hg : ∀ x', a < x' → IntegrableOn g (Icc x' b))
    {x : ℝ} (hax : a < x) (hxb : x < b) :
    Tendsto (fun k => ∫ r in Icc a b, ((step k (r - x) : ℝ) : ℂ) * g r) atTop
      (𝓝 (∫ t in x..b, g t)) := by
  have hax1 : a < (a + x) / 2 := by linarith
  have hev := width_eventually (show 0 < x - (a + x) / 2 by linarith)
  have hmeas : ∀ᶠ k in atTop, AEStronglyMeasurable (fun r => ((step k (r - x) : ℝ) : ℂ) * g r)
      (volume.restrict (Icc a b)) := by
    filter_upwards [hev] with k hk
    exact (integrable_step_mul hg (by linarith)).aestronglyMeasurable
  have hbd : ∀ᶠ k in atTop, ∀ᵐ r ∂(volume.restrict (Icc a b)),
      ‖((step k (r - x) : ℝ) : ℂ) * g r‖ ≤ Set.indicator (Icc ((a + x) / 2) b) (fun r => ‖g r‖) r := by
    filter_upwards [hev] with k hk
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    by_cases h : (a + x) / 2 ≤ r
    · rw [Set.indicator_of_mem (show r ∈ Icc ((a + x) / 2) b from ⟨h, hr.2⟩), norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      calc |step k (r - x)| * ‖g r‖ ≤ 1 * ‖g r‖ :=
            mul_le_mul_of_nonneg_right (abs_step_le k _) (norm_nonneg _)
        _ = ‖g r‖ := one_mul _
    · rw [step_low k (by linarith [not_le.1 h])]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
  have hbi : Integrable (fun r => Set.indicator (Icc ((a + x) / 2) b) (fun r => ‖g r‖) r)
      (volume.restrict (Icc a b)) :=
    (IntegrableOn.integrable_indicator (hg _ hax1).norm measurableSet_Icc).integrableOn
  have hl : ∀ᵐ r ∂(volume.restrict (Icc a b)), Tendsto (fun k => ((step k (r - x) : ℝ) : ℂ) * g r)
      atTop (𝓝 (Set.indicator (Ioi x) g r)) := by
    filter_upwards [ae_restrict_of_ae (ae_ne_pt x)] with r hr
    rcases lt_or_gt_of_ne hr with h | h
    · rw [Set.indicator_of_notMem (show r ∉ Ioi x by simp only [mem_Ioi]; linarith)]
      apply tendsto_const_nhds.congr'
      filter_upwards [width_eventually (show 0 < x - r by linarith)] with k hk
      rw [step_low k (by linarith)]; simp
    · rw [Set.indicator_of_mem (show r ∈ Ioi x from h)]
      apply tendsto_const_nhds.congr'
      filter_upwards [width_eventually (show 0 < r - x by linarith)] with k hk
      rw [step_high k (by linarith)]; simp
  have hlim := tendsto_integral_filter_of_dominated_convergence _ hmeas hbd hbi hl
  rw [setIntegral_indicator measurableSet_Ioi] at hlim
  have hset : Icc a b ∩ Ioi x = Ioc x b := by
    ext r; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]; constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [hset, ← intervalIntegral.integral_of_le hxb.le] at hlim
  exact hlim

lemma kern_density {a b : ℝ} {u : ℝ → ℂ} (hu : IntegrableOn u (Icc a b)) :
    ∀ᵐ x ∂volume, Tendsto (fun k => ∫ r in Icc a b, ((kern k (r - x) : ℝ) : ℂ) * u r) atTop
      (𝓝 (Set.indicator (Icc a b) u x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    (φ := bumpAt) (l := atTop) (K := 2) width_tendsto
    (Eventually.of_forall fun k => by
      show 2 / ((k : ℝ) + 4) ≤ 2 * (1 / ((k : ℝ) + 4)); rw [mul_one_div])
    (hu.integrable_indicator measurableSet_Icc).locallyIntegrable
  filter_upwards [h] with x hx
  refine hx.congr fun k => ?_
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply]
  have hs := integral_sub_left_eq_self
    (fun r => (bumpAt k).normed volume (x - r) • Set.indicator (Icc a b) u r) volume x
  simp only [sub_sub_cancel] at hs
  rw [hs, ← integral_indicator measurableSet_Icc]
  congr 1
  funext r
  by_cases hr : r ∈ Icc a b
  · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, Complex.real_smul, kern,
      show r - x = -(x - r) by ring, ContDiffBump.normed_neg]
  · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, smul_zero]

lemma line_core (a b : ℝ) (hab : a < b) (u g : ℝ → ℂ)
    (hu : IntegrableOn u (Icc a b)) (hg : ∀ x', a < x' → IntegrableOn g (Icc x' b))
    (hid : ∀ k : ℕ, ∀ x y : ℚ, a < (x : ℝ) - width k → (x : ℝ) + width k < b →
      a < (y : ℝ) - width k → (y : ℝ) + width k < b →
      ∫ r in Icc a b, ((deriv (test k x y) r : ℝ) : ℂ) * u r + ((test k x y r : ℝ) : ℂ) * g r = 0) :
    ∃ L : ℂ, ∀ᵐ x ∂(volume.restrict (Icc a b)), u x = L - ∫ t in x..b, g t := by
  have hEq : ∀ k : ℕ, ∀ x y : ℚ, a < (x : ℝ) - width k → (x : ℝ) + width k < b →
      a < (y : ℝ) - width k → (y : ℝ) + width k < b → avgVal k a b u g x = avgVal k a b u g y := by
    intro k x y hx1 hx2 hy1 hy2
    have h := hid k x y hx1 hx2 hy1 hy2
    have heq : (fun r => ((deriv (test k x y) r : ℝ) : ℂ) * u r + ((test k x y r : ℝ) : ℂ) * g r) =
        fun r => (((kern k (r - x) : ℝ) : ℂ) * u r + ((step k (r - x) : ℝ) : ℂ) * g r) -
          (((kern k (r - y) : ℝ) : ℂ) * u r + ((step k (r - y) : ℝ) : ℂ) * g r) := by
      funext r
      rw [test_deriv]
      simp only [test, Complex.ofReal_sub]
      ring
    have hi1 : IntegrableOn (fun r => ((kern k (r - x) : ℝ) : ℂ) * u r + ((step k (r - x) : ℝ) : ℂ) * g r)
        (Icc a b) := (integrable_kern_mul hu _).add (integrable_step_mul hg hx1)
    have hi2 : IntegrableOn (fun r => ((kern k (r - y) : ℝ) : ℂ) * u r + ((step k (r - y) : ℝ) : ℂ) * g r)
        (Icc a b) := (integrable_kern_mul hu _).add (integrable_step_mul hg hy1)
    rw [heq, integral_sub hi1 hi2] at h
    exact sub_eq_zero.1 h
  have hconst : ∀ k x x', a < x - width k → x + width k < b → a < x' - width k → x' + width k < b →
      avgVal k a b u g x = avgVal k a b u g x' := by
    intro k x x' hx1 hx2 hx1' hx2'
    have hUo : IsOpen {x : ℝ | a < x - width k ∧ x + width k < b} :=
      (isOpen_lt continuous_const (continuous_sub_right (width k))).inter
        (isOpen_lt (continuous_add_const (width k)) continuous_const)
    have hq : ∀ x ∈ {x : ℝ | a < x - width k ∧ x + width k < b}, ∀ q : ℚ,
        (q : ℝ) ∈ {x : ℝ | a < x - width k ∧ x + width k < b} →
        avgVal k a b u g x = avgVal k a b u g q := by
      intro x hx q hqU
      have hcl := Dense.open_subset_closure_inter Rat.denseRange_cast hUo hx
      have hm := mem_closure_image (avgVal_cont hu hg hx.1) hcl
      have hsub : (avgVal k a b u g) '' ({x : ℝ | a < x - width k ∧ x + width k < b} ∩
          range ((↑) : ℚ → ℝ)) ⊆ {avgVal k a b u g q} := by
        rintro _ ⟨_, ⟨hpU, p, rfl⟩, rfl⟩
        exact hEq k p q hpU.1 hpU.2 hqU.1 hqU.2
      have := closure_mono hsub hm
      rwa [closure_singleton] at this
    obtain ⟨q, hqU⟩ := Rat.denseRange_cast.exists_mem_open hUo ⟨x, hx1, hx2⟩
    rw [hq x ⟨hx1, hx2⟩ q hqU, hq x' ⟨hx1', hx2'⟩ q hqU]
  have hne : volume.restrict (Icc a b) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hP : ∀ᵐ x ∂(volume.restrict (Icc a b)), a < x ∧ x < b ∧
      Tendsto (fun k => ∫ r in Icc a b, ((kern k (r - x) : ℝ) : ℂ) * u r) atTop (𝓝 (u x)) := by
    filter_upwards [ae_restrict_of_ae (kern_density hu), ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (ae_ne_pt a), ae_restrict_of_ae (ae_ne_pt b)] with x h1 h2 h3 h4
    rw [Set.indicator_of_mem h2] at h1
    exact ⟨lt_of_le_of_ne h2.1 (Ne.symm h3), lt_of_le_of_ne h2.2 h4, h1⟩
  have hlimE : ∀ x, (a < x ∧ x < b ∧ Tendsto (fun k => ∫ r in Icc a b, ((kern k (r - x) : ℝ) : ℂ) * u r)
      atTop (𝓝 (u x))) → Tendsto (fun k => avgVal k a b u g x) atTop (𝓝 (u x + ∫ t in x..b, g t)) := by
    rintro x ⟨h1, h2, h3⟩
    refine (h3.add (step_limit hg h1 h2)).congr' ?_
    filter_upwards [width_eventually (show 0 < x - a by linarith)] with k hk
    rw [avgVal, integral_add (integrable_kern_mul hu x) (integrable_step_mul hg (by linarith))]
  have := ae_neBot.2 hne
  obtain ⟨xs, hxs⟩ := hP.exists
  refine ⟨u xs + ∫ t in xs..b, g t, ?_⟩
  filter_upwards [hP] with x hx
  have hlx := hlimE x hx
  have hls := hlimE xs hxs
  have hev : ∀ᶠ k in atTop, avgVal k a b u g x = avgVal k a b u g xs := by
    filter_upwards [width_eventually (show 0 < x - a by linarith [hx.1]),
      width_eventually (show 0 < b - x by linarith [hx.2.1]),
      width_eventually (show 0 < xs - a by linarith [hxs.1]),
      width_eventually (show 0 < b - xs by linarith [hxs.2.1])] with k h1 h2 h3 h4
    exact hconst k x xs (by linarith) (by linarith) (by linarith) (by linarith)
  have := tendsto_nhds_unique (hlx.congr' hev) hls
  rw [← this]; ring

lemma rect_measure (a b c d : ℝ) :
    volume.restrict (Icc a b ×ˢ Icc c d) =
      (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

lemma slice_integrable {E : Type*} [NormedAddCommGroup E] {a b c d : ℝ} {f : ℝ × ℝ → E}
    (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    ∀ᵐ z ∂(volume.restrict (Icc c d)), IntegrableOn (fun r => f (r, z)) (Icc a b) := by
  rw [IntegrableOn, rect_measure] at hf
  exact hf.prod_left_ae

lemma slice_zero {a b c d : ℝ} {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F (Icc a b ×ˢ Icc c d))
    (h : ∀ t : ℝ → ℝ, Continuous t → ∫ p in Icc a b ×ˢ Icc c d, F p * ((t p.2 : ℝ) : ℂ) = 0) :
    ∀ᵐ z ∂(volume.restrict (Icc c d)), ∫ r in Icc a b, F (r, z) = 0 := by
  rw [IntegrableOn, rect_measure] at hF
  have hΦ : Integrable (fun z => ∫ r in Icc a b, F (r, z)) (volume.restrict (Icc c d)) :=
    hF.integral_prod_right
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hΦ.locallyIntegrable ?_
  intro φ hφ hφc
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hi : Integrable (fun p : ℝ × ℝ => F p * ((φ p.2 : ℝ) : ℂ))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
    refine hF.mul_bdd (c := C) ?_ (Eventually.of_forall fun p => ?_)
    · exact (Complex.continuous_ofReal.comp (hφ.continuous.comp continuous_snd)).aestronglyMeasurable
    · show ‖((φ p.2 : ℝ) : ℂ)‖ ≤ C
      rw [Complex.norm_real]; exact hC _
  have h1 := h φ hφ.continuous
  rw [rect_measure, integral_prod_symm _ hi] at h1
  rw [← h1]
  congr 1
  funext z
  rw [← integral_smul]
  congr 1
  funext r
  rw [Complex.real_smul]
  ring

lemma lw_meas (K : CellBox) : Measurable K.lineWeight := by
  by_cases h0 : K.r₁ = 0
  · have : K.lineWeight = fun r => r := by funext r; rw [CellBox.lineWeight, if_pos h0]
    rw [this]; exact measurable_id
  · have : K.lineWeight = fun _ => 1 := by funext r; rw [CellBox.lineWeight, if_neg h0]
    rw [this]; exact measurable_const

lemma lw_ge (K : CellBox) {x' r : ℝ} (hr : x' ≤ r) : min x' 1 ≤ K.lineWeight r := by
  by_cases h0 : K.r₁ = 0
  · rw [CellBox.lineWeight, if_pos h0]; exact (min_le_left _ _).trans hr
  · rw [CellBox.lineWeight, if_neg h0]; exact min_le_right _ _

lemma lw_ne (K : CellBox) {r : ℝ} (hr : r ≠ 0) : K.lineWeight r ≠ 0 := by
  by_cases h0 : K.r₁ = 0
  · rw [CellBox.lineWeight, if_pos h0]; exact hr
  · rw [CellBox.lineWeight, if_neg h0]; exact one_ne_zero

lemma test_left (k : ℕ) {x y r : ℝ} (hx : r ≤ x - width k) (hy : r ≤ y - width k) :
    test k x y r = 0 := by
  unfold test
  rw [step_low k (by linarith), step_low k (by linarith)]
  simp

lemma test_right (k : ℕ) {x y r : ℝ} (hx : x + width k ≤ r) (hy : y + width k ≤ r) :
    test k x y r = 0 := by
  unfold test
  rw [step_high k (by linarith), step_high k (by linarith)]
  simp

lemma integrable_weak_integrand (K : CellBox) (hK : IsCellBox K) {u g : ℝ × ℝ → ℂ}
    (hU : IntegrableOn u (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂))
    (hW : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * g p) (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂))
    (k : ℕ) {x y : ℝ} (hx : K.r₁ < x - width k) (hy : K.r₁ < y - width k) :
    IntegrableOn (fun p : ℝ × ℝ => ((deriv (test k x y) p.1 : ℝ) : ℂ) * u p +
      ((test k x y p.1 : ℝ) : ℂ) * g p) (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) := by
  obtain ⟨C, hC⟩ := test_deriv_bound k x y
  have hA : IntegrableOn (fun p : ℝ × ℝ => ((deriv (test k x y) p.1 : ℝ) : ℂ) * u p)
      (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) := by
    refine Integrable.bdd_mul (c := C) hU ?_ (Eventually.of_forall fun p => ?_)
    · exact (Complex.continuous_ofReal.comp
        ((test_deriv_cont k x y).comp continuous_fst)).aestronglyMeasurable
    · show ‖((deriv (test k x y) p.1 : ℝ) : ℂ)‖ ≤ C
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hC _
  have hax' : K.r₁ < min (x - width k) (y - width k) := lt_min hx hy
  have hmpos : 0 < min (min (x - width k) (y - width k)) 1 :=
    lt_min (by linarith [hK.r_order.1]) one_pos
  have hB : IntegrableOn (fun p : ℝ × ℝ => ((test k x y p.1 / K.lineWeight p.1 : ℝ) : ℂ) *
      ((K.lineWeight p.1 : ℂ) * g p)) (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) := by
    refine Integrable.bdd_mul (c := 2 / min (min (x - width k) (y - width k)) 1) hW ?_ ?_
    · exact (Complex.measurable_ofReal.comp (((test_cont k x y).measurable.comp measurable_fst).div
        ((lw_meas K).comp measurable_fst))).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      show ‖((test k x y p.1 / K.lineWeight p.1 : ℝ) : ℂ)‖ ≤ 2 / min (min (x - width k) (y - width k)) 1
      rw [Complex.norm_real, Real.norm_eq_abs]
      by_cases hp : min (x - width k) (y - width k) ≤ p.1
      · have hw := lw_ge K (x' := min (x - width k) (y - width k)) hp
        rw [abs_div, abs_of_pos (lt_of_lt_of_le hmpos hw)]
        exact div_le_div₀ (by norm_num) (abs_test_le k x y _) hmpos hw
      · rw [test_left k (le_of_lt (lt_of_lt_of_le (not_le.1 hp) (min_le_left _ _)))
          (le_of_lt (lt_of_lt_of_le (not_le.1 hp) (min_le_right _ _))), zero_div, abs_zero]
        positivity
  have hBeq : (fun p : ℝ × ℝ => ((test k x y p.1 / K.lineWeight p.1 : ℝ) : ℂ) *
      ((K.lineWeight p.1 : ℂ) * g p)) = fun p => ((test k x y p.1 : ℝ) : ℂ) * g p := by
    funext p
    by_cases hp : min (x - width k) (y - width k) ≤ p.1
    · have hw : K.lineWeight p.1 ≠ 0 :=
        (lt_of_lt_of_le hmpos (lw_ge K (x' := min (x - width k) (y - width k)) hp)).ne'
      have hwc : (K.lineWeight p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw
      rw [Complex.ofReal_div]
      field_simp
    · rw [test_left k (le_of_lt (lt_of_lt_of_le (not_le.1 hp) (min_le_left _ _)))
        (le_of_lt (lt_of_lt_of_le (not_le.1 hp) (min_le_right _ _)))]
      simp
  rw [hBeq] at hB
  exact hA.add hB

end ModeRadialLineInternal

open ModeRadialLineInternal

theorem modeRadialLine_of (h1 : ModeRadialWeakStatement) (h2 : ModeGradSquareStatement)
    (h3 : ModeVelSquareStatement) : ModeRadialLineStatement := by
  intro K hK m v G H hv n a
  obtain ⟨hU, hW, hweak⟩ := h1 K hK m v G H hv n a
  obtain ⟨_, hGsq⟩ := h2 K hK m v G H hv n a 0
  obtain ⟨_, hVsq⟩ := h3 K hK m v G H hv n a
  have hab : K.r₁ < K.r₂ := hK.r_order.2
  have hU' : IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) := hU
  have hW' : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode m n G a 0 p)
    (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) := hW
  have hG' : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖gradMode m n G a 0 p‖ ^ 2)
    (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) := hGsq
  have hV' : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖modeVec m n v p.1 p.2 a‖ ^ 2)
    (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) := hVsq
  have hall : ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)), ∀ k : ℕ, ∀ x y : ℚ,
      K.r₁ < (x : ℝ) - width k → (x : ℝ) + width k < K.r₂ →
      K.r₁ < (y : ℝ) - width k → (y : ℝ) + width k < K.r₂ →
      ∫ r in Icc K.r₁ K.r₂, ((deriv (test k x y) r : ℝ) : ℂ) * modeVec m n v r z a +
        ((test k x y r : ℝ) : ℂ) * gradMode m n G a 0 (r, z) = 0 := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun x => ae_all_iff.2 fun y => ?_
    by_cases hg : K.r₁ < (x : ℝ) - width k ∧ (x : ℝ) + width k < K.r₂ ∧
        K.r₁ < (y : ℝ) - width k ∧ (y : ℝ) + width k < K.r₂
    · obtain ⟨hx1, hx2, hy1, hy2⟩ := hg
      have hF := integrable_weak_integrand K hK hU' hW' k hx1 hy1
      have hz := slice_zero hF (fun t ht => hweak _ (test_contDiff k x y)
        (test_left k (by linarith) (by linarith)) (test_right k (by linarith) (by linarith)) t ht)
      filter_upwards [hz] with z hz
      intro _ _ _ _
      exact hz
    · exact Eventually.of_forall fun z hx1 hx2 hy1 hy2 => absurd ⟨hx1, hx2, hy1, hy2⟩ hg
  filter_upwards [hall, slice_integrable hU', slice_integrable hW', slice_integrable hG',
    slice_integrable hV'] with z hz hUz hWz hGz hVz
  have hgI : ∀ x', K.r₁ < x' → IntegrableOn (fun r => gradMode m n G a 0 (r, z)) (Icc x' K.r₂) := by
    intro x' hx'
    have hmpos : 0 < min x' 1 := lt_min (by linarith [hK.r_order.1]) one_pos
    have hm : AEStronglyMeasurable (fun r => (((K.lineWeight r)⁻¹ : ℝ) : ℂ))
        (volume.restrict (Icc x' K.r₂)) :=
      (Complex.measurable_ofReal.comp (lw_meas K).inv).aestronglyMeasurable
    have hb : ∀ᵐ r ∂(volume.restrict (Icc x' K.r₂)), ‖(((K.lineWeight r)⁻¹ : ℝ) : ℂ)‖ ≤ 1 / min x' 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hw := lw_ge K (x' := x') hr.1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos (lt_of_lt_of_le hmpos hw), one_div]
      exact inv_anti₀ hmpos hw
    have hI := Integrable.bdd_mul (hWz.mono_set (Icc_subset_Icc_left hx'.le)) hm hb
    refine hI.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hw : K.lineWeight r ≠ 0 := (lt_of_lt_of_le hmpos (lw_ge K (x' := x') hr.1)).ne'
    show (((K.lineWeight r)⁻¹ : ℝ) : ℂ) * ((K.lineWeight r : ℂ) * gradMode m n G a 0 (r, z)) =
      gradMode m n G a 0 (r, z)
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hw, Complex.ofReal_one, one_mul]
  obtain ⟨L, hL⟩ := line_core K.r₁ K.r₂ hab (fun r => modeVec m n v r z a)
    (fun r => gradMode m n G a 0 (r, z)) hUz hgI hz
  have hII : ∀ x y, x ∈ Ioc K.r₁ K.r₂ → y ∈ Ioc K.r₁ K.r₂ →
      IntervalIntegrable (fun t => gradMode m n G a 0 (t, z)) volume x y := by
    intro x y hx hy
    refine IntegrableOn.intervalIntegrable ((hgI (min x y) (lt_min hx.1 hy.1)).mono_set ?_)
    intro t ht
    rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨(min_le_left _ _).trans h1, h2.trans hy.2⟩
    · exact ⟨(min_le_right _ _).trans h1, h2.trans hx.2⟩
  have hbI : K.r₂ ∈ Ioc K.r₁ K.r₂ := ⟨hab, le_rfl⟩
  refine ⟨fun r => L - ∫ t in r..K.r₂, gradMode m n G a 0 (t, z), ?_, ?_, ?_, hGz, ?_, hL⟩
  · intro x hx y hy
    show L - ∫ t in y..K.r₂, gradMode m n G a 0 (t, z) =
      (L - ∫ t in x..K.r₂, gradMode m n G a 0 (t, z)) + ∫ t in x..y, gradMode m n G a 0 (t, z)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII x y hx hy) (hII y K.r₂ hy hbI)]
    ring
  · intro r0 hr0
    have hx' : K.r₁ < (K.r₁ + r0) / 2 := by linarith [hr0.1]
    have hle : (K.r₁ + r0) / 2 ≤ K.r₂ := by linarith [hr0.1, hr0.2]
    have hc := intervalIntegral.continuousOn_primitive_interval_left (μ := volume)
      (f := fun t => gradMode m n G a 0 (t, z)) (a := (K.r₁ + r0) / 2) (b := K.r₂)
      (by rw [uIcc_of_le hle]; exact hgI _ hx')
    rw [uIcc_of_le hle] at hc
    refine ((continuousOn_const.sub hc) r0 ⟨by linarith [hr0.1], hr0.2⟩).mono_of_mem_nhdsWithin ?_
    refine mem_nhdsWithin.2 ⟨Ioi ((K.r₁ + r0) / 2), isOpen_Ioi, by simp only [mem_Ioi]; linarith [hr0.1], ?_⟩
    rintro t ⟨ht1, ht2⟩
    exact ⟨le_of_lt ht1, ht2.2⟩
  · have hm : AEStronglyMeasurable (fun r => (((K.lineWeight r)⁻¹ : ℝ) : ℂ) *
        ((K.lineWeight r : ℂ) * gradMode m n G a 0 (r, z))) (volume.restrict (Icc K.r₁ K.r₂)) :=
      (Complex.measurable_ofReal.comp (lw_meas K).inv).aestronglyMeasurable.mul hWz.aestronglyMeasurable
    refine hm.congr ?_
    filter_upwards [ae_restrict_of_ae (ae_ne_pt 0)] with r hr
    have hw := lw_ne K hr
    show (((K.lineWeight r)⁻¹ : ℝ) : ℂ) * ((K.lineWeight r : ℂ) * gradMode m n G a 0 (r, z)) =
      gradMode m n G a 0 (r, z)
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hw, Complex.ofReal_one, one_mul]
  · refine hVz.congr ?_
    filter_upwards [hL] with r hr
    simp only [hr]

end CellAnalysis

end CellCert

end Breakdown
