import Breakdown.FracCell.FormulaDataDefs
import Breakdown.FracCell.LowEntry
import Breakdown.FracCell.StCornerModesOpen
import Breakdown.FracCell.ModeHeightAxis
import Breakdown.FracCell.ModeWeakIdentity

open scoped ContDiff
open MeasureTheory Filter Set
open scoped Topology Convolution

noncomputable section

namespace Breakdown.FracInternal.CornerParts

def tentFn (a c b x : ℝ) : ℝ := max 0 (min ((x - a) / (c - a)) ((b - x) / (b - c)))

def tentSlope (a c b x : ℝ) : ℝ := if x ∈ Icc a b then 1 / (c - (if x ≤ c then a else b)) else 0

def bumpSeq (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / (2 * ((n : ℝ) + 2)), 1 / ((n : ℝ) + 2), by positivity, by
    have h : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    rw [div_lt_div_iff₀ (by positivity) h]; linarith⟩

def mollTent (a c b : ℝ) (n : ℕ) : ℝ → ℝ :=
  (bumpSeq n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] tentFn a c b

lemma slope_left (a d : ℝ) : LipschitzWith (Real.toNNReal |1 / d|) (fun x : ℝ => (x - a) / d) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (abs_nonneg _), Real.dist_eq, Real.dist_eq,
    show (x - a) / d - (y - a) / d = 1 / d * (x - y) by ring, abs_mul]

lemma slope_right (b d : ℝ) : LipschitzWith (Real.toNNReal |1 / d|) (fun x : ℝ => (b - x) / d) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (abs_nonneg _), Real.dist_eq, Real.dist_eq,
    show (b - x) / d - (b - y) / d = 1 / d * (y - x) by ring, abs_mul, abs_sub_comm y x]

lemma tent_slope (a c b : ℝ) : ∃ K : NNReal, LipschitzWith K (tentFn a c b) :=
  ⟨_, (LipschitzWith.const (0 : ℝ)).max ((slope_left a (c - a)).min (slope_right b (b - c)))⟩

lemma tent_cont (a c b : ℝ) : Continuous (tentFn a c b) := by
  obtain ⟨K, hK⟩ := tent_slope a c b
  exact hK.continuous

lemma tent_zero {a c b x : ℝ} (hac : a < c) (hcb : c < b) (hx : x ∉ Ioo a b) : tentFn a c b x = 0 := by
  unfold tentFn
  rcases le_or_gt x a with h | h
  · have : (x - a) / (c - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    exact max_eq_left ((min_le_left _ _).trans this)
  · have hb : b ≤ x := by
      by_contra h'
      exact hx ⟨h, lt_of_not_ge h'⟩
    have : (b - x) / (b - c) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    exact max_eq_left ((min_le_right _ _).trans this)

lemma tent_eq_on {a c b x : ℝ} (hac : a < c) (hcb : c < b) (hx : x ∈ Icc a b) :
    tentFn a c b x = (x - (if x ≤ c then a else b)) / (c - (if x ≤ c then a else b)) := by
  unfold tentFn
  have h1 : 0 < c - a := by linarith
  have h2 : 0 < b - c := by linarith
  split_ifs with h
  · have e1 : (x - a) / (c - a) ≤ 1 := by rw [div_le_one h1]; linarith
    have e2 : 1 ≤ (b - x) / (b - c) := by rw [le_div_iff₀ h2]; linarith
    have e3 : 0 ≤ (x - a) / (c - a) := div_nonneg (by linarith [hx.1]) h1.le
    rw [min_eq_left (e1.trans e2), max_eq_right e3]
  · push Not at h
    have e1 : 1 ≤ (x - a) / (c - a) := by rw [le_div_iff₀ h1]; linarith
    have e2 : (b - x) / (b - c) ≤ 1 := by rw [div_le_one h2]; linarith
    have e3 : 0 ≤ (b - x) / (b - c) := div_nonneg (by linarith [hx.2]) h2.le
    rw [min_eq_right (e2.trans e1), max_eq_right e3]
    rw [show (x - b) / (c - b) = (b - x) / (b - c) by
      rw [show x - b = -(b - x) by ring, show c - b = -(b - c) by ring, neg_div_neg_eq]]

lemma tent_local {a c b x : ℝ} (hac : a < c) (hcb : c < b) (ha : x ≠ a) (hc : x ≠ c) (hb : x ≠ b) :
    ∃ δ > 0, ∃ m : ℝ, ∀ y ∈ Metric.ball x δ, tentFn a c b y = m + tentSlope a c b x * y := by
  rcases lt_or_gt_of_ne ha with h1 | h1
  · refine ⟨a - x, by linarith, 0, fun y hy => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have hy' : y < a := by linarith [(abs_lt.1 hy).2]
    have hs : tentSlope a c b x = 0 := by
      unfold tentSlope; rw [if_neg]; intro hm; linarith [hm.1]
    rw [hs, tent_zero hac hcb (fun hm => by linarith [hm.1])]; ring
  rcases lt_or_gt_of_ne hc with h2 | h2
  · refine ⟨min (x - a) (c - x), lt_min (by linarith) (by linarith), -a / (c - a), fun y hy => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have hy1 := (abs_lt.1 hy)
    have l1 := min_le_left (x - a) (c - x)
    have l2 := min_le_right (x - a) (c - x)
    have hyI : y ∈ Icc a b := ⟨by linarith, by linarith⟩
    have hyc : y ≤ c := by linarith
    have hxI : x ∈ Icc a b := ⟨by linarith, by linarith⟩
    have hs : tentSlope a c b x = 1 / (c - a) := by
      unfold tentSlope; rw [if_pos hxI, if_pos h2.le]
    rw [hs, tent_eq_on hac hcb hyI, if_pos hyc]
    have : c - a ≠ 0 := by linarith
    field_simp; ring
  rcases lt_or_gt_of_ne hb with h3 | h3
  · refine ⟨min (x - c) (b - x), lt_min (by linarith) (by linarith), b / (b - c), fun y hy => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have hy1 := (abs_lt.1 hy)
    have l1 := min_le_left (x - c) (b - x)
    have l2 := min_le_right (x - c) (b - x)
    have hyI : y ∈ Icc a b := ⟨by linarith, by linarith⟩
    have hyc : ¬ y ≤ c := by push Not; linarith
    have hxI : x ∈ Icc a b := ⟨by linarith, by linarith⟩
    have hs : tentSlope a c b x = 1 / (c - b) := by
      unfold tentSlope; rw [if_pos hxI, if_neg (by push Not; exact h2)]
    rw [hs, tent_eq_on hac hcb hyI, if_neg hyc]
    have : c - b ≠ 0 := by linarith
    have : b - c ≠ 0 := by linarith
    field_simp; ring
  · refine ⟨x - b, by linarith, 0, fun y hy => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have hy' : b < y := by linarith [(abs_lt.1 hy).1]
    have hs : tentSlope a c b x = 0 := by
      unfold tentSlope; rw [if_neg]; intro hm; linarith [hm.2]
    rw [hs, tent_zero hac hcb (fun hm => by linarith [hm.2])]; ring

lemma bump_rOut (n : ℕ) : (bumpSeq n).rOut = 1 / ((n : ℝ) + 2) := rfl

lemma moll_apply (a c b : ℝ) (n : ℕ) (x : ℝ) :
    mollTent a c b n x = ∫ t, (bumpSeq n).normed volume t * tentFn a c b (x - t) := by
  simp [mollTent, convolution_def]

lemma bump_mul_int (n : ℕ) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun t => (bumpSeq n).normed volume t * g t) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (bumpSeq n).continuous_normed.mul hg
  · exact (bumpSeq n).hasCompactSupport_normed.mul_right

lemma moll_smooth (a c b : ℝ) (n : ℕ) : ContDiff ℝ ∞ (mollTent a c b n) :=
  (bumpSeq n).hasCompactSupport_normed.contDiff_convolution_left _ (bumpSeq n).contDiff_normed
    (tent_cont a c b).locallyIntegrable

lemma moll_slope (a c b : ℝ) {K : NNReal} (hK : LipschitzWith K (tentFn a c b)) (n : ℕ) :
    LipschitzWith K (mollTent a c b n) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have i1 := bump_mul_int n (g := fun t => tentFn a c b (x - t)) ((tent_cont a c b).comp (continuous_sub_left x))
  have i2 := bump_mul_int n (g := fun t => tentFn a c b (y - t)) ((tent_cont a c b).comp (continuous_sub_left y))
  rw [Real.dist_eq, moll_apply, moll_apply, ← integral_sub i1 i2]
  have hb : ∀ t, |(bumpSeq n).normed volume t * tentFn a c b (x - t)
      - (bumpSeq n).normed volume t * tentFn a c b (y - t)| ≤ (bumpSeq n).normed volume t * (K * |x - y|) := by
    intro t
    rw [← mul_sub, abs_mul, abs_of_nonneg ((bumpSeq n).nonneg_normed t)]
    refine mul_le_mul_of_nonneg_left ?_ ((bumpSeq n).nonneg_normed t)
    have := hK.dist_le_mul (x - t) (y - t)
    rw [Real.dist_eq, Real.dist_eq, show x - t - (y - t) = x - y by ring] at this
    exact this
  calc |∫ t, ((bumpSeq n).normed volume t * tentFn a c b (x - t)
        - (bumpSeq n).normed volume t * tentFn a c b (y - t))|
      ≤ ∫ t, (bumpSeq n).normed volume t * (K * |x - y|) := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le ((bumpSeq n).integrable_normed.mul_const _) ?_
        exact Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hb t
    _ = K * |x - y| := by rw [integral_mul_const, (bumpSeq n).integral_normed, one_mul]
    _ = K * dist x y := by rw [Real.dist_eq]

lemma moll_zero_of (a c b : ℝ) (hac : a < c) (hcb : c < b) (n : ℕ) (x : ℝ)
    (hx : x ∉ Ioo (a - 1 / ((n : ℝ) + 2)) (b + 1 / ((n : ℝ) + 2))) : mollTent a c b n x = 0 := by
  rw [moll_apply]
  have : ∀ t, (bumpSeq n).normed volume t * tentFn a c b (x - t) = 0 := by
    intro t
    by_cases ht : (bumpSeq n).normed volume t = 0
    · rw [ht, zero_mul]
    · have hts : t ∈ Function.support ((bumpSeq n).normed volume) := ht
      rw [(bumpSeq n).support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero, bump_rOut] at hts
      have h1 := abs_lt.1 hts
      rw [tent_zero hac hcb, mul_zero]
      intro hm
      exact hx ⟨by linarith [hm.1], by linarith [hm.2]⟩
  simp [this]

lemma moll_vanish (a c b : ℝ) (hac : a < c) (hcb : c < b) (n : ℕ) (x : ℝ)
    (hx : x ∉ Icc (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1))) :
    mollTent a c b n x = 0 ∧ deriv (mollTent a c b n) x = 0 := by
  have hlt : 1 / ((n : ℝ) + 2) < 1 / ((n : ℝ) + 1) := by
    apply one_div_lt_one_div_of_lt (by positivity); linarith
  have hU : IsOpen (Icc (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1)))ᶜ := isClosed_Icc.isOpen_compl
  have hz : ∀ y ∈ (Icc (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1)))ᶜ, mollTent a c b n y = 0 := by
    intro y hy
    refine moll_zero_of a c b hac hcb n y fun hm => hy ⟨by linarith [hm.1], by linarith [hm.2]⟩
  refine ⟨hz x hx, ?_⟩
  have hev : mollTent a c b n =ᶠ[𝓝 x] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hx) hz
  rw [hev.deriv_eq, deriv_const]

lemma rOut_tendsto : Tendsto (fun n : ℕ => (bumpSeq n).rOut) atTop (𝓝 0) := by
  show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0)
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

lemma moll_tendsto (a c b x : ℝ) : Tendsto (fun n => mollTent a c b n x) atTop (𝓝 (tentFn a c b x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous rOut_tendsto (tent_cont a c b) x

lemma moll_deriv_tendsto {a c b x : ℝ} (hac : a < c) (hcb : c < b) (ha : x ≠ a) (hc : x ≠ c) (hb : x ≠ b) :
    Tendsto (fun n => deriv (mollTent a c b n) x) atTop (𝓝 (tentSlope a c b x)) := by
  obtain ⟨δ, hδ, m, hm⟩ := tent_local hac hcb ha hc hb
  set s := tentSlope a c b x
  have hev : ∀ᶠ n in atTop, (bumpSeq n).rOut < δ / 2 := rOut_tendsto.eventually (gt_mem_nhds (by linarith))
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with n hn
  set ρ := (bumpSeq n).normed volume
  have hρi : Integrable ρ := (bumpSeq n).integrable_normed
  have htρ : Integrable (fun t => t * ρ t) := by
    refine Continuous.integrable_of_hasCompactSupport (continuous_id.mul (bumpSeq n).continuous_normed) ?_
    exact (bumpSeq n).hasCompactSupport_normed.mul_left
  have hloc : ∀ y ∈ Metric.ball x (δ / 2), mollTent a c b n y = (m + s * y) - s * ∫ t, t * ρ t := by
    intro y hy
    rw [moll_apply]
    have e : ∀ t, ρ t * tentFn a c b (y - t) = (m + s * y) * ρ t - s * (t * ρ t) := by
      intro t
      by_cases ht : ρ t = 0
      · rw [ht]; ring
      · have hts : t ∈ Function.support ρ := ht
        rw [(bumpSeq n).support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hts
        have hyt : y - t ∈ Metric.ball x δ := by
          rw [Metric.mem_ball, Real.dist_eq] at hy ⊢
          calc |y - t - x| ≤ |y - x| + |t| := by
                rw [show y - t - x = (y - x) + (-t) by ring]
                exact (abs_add_le _ _).trans (by rw [abs_neg])
            _ < δ := by linarith
        rw [hm _ hyt]; ring
    rw [show (∫ t, (bumpSeq n).normed volume t * tentFn a c b (y - t)) = ∫ t, ((m + s * y) * ρ t - s * (t * ρ t))
      from integral_congr_ae (Eventually.of_forall e)]
    rw [integral_sub (hρi.const_mul _) (htρ.const_mul _), integral_const_mul, integral_const_mul,
      (bumpSeq n).integral_normed, mul_one]
  have hev2 : mollTent a c b n =ᶠ[𝓝 x] fun y => (m + s * y) - s * ∫ t, t * ρ t :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds x (by linarith)) hloc
  rw [hev2.deriv_eq]
  have hd : HasDerivAt (fun y => (m + s * y) - s * ∫ t, t * ρ t) s x := by
    have := ((hasDerivAt_id x).const_mul s).const_add m
    simpa using this.sub_const (s * ∫ t, t * ρ t)
  exact hd.deriv.symm


lemma ae_fst_ne (x : ℝ) : ∀ᵐ p : ℝ × ℝ, p.1 ≠ x := by
  rw [ae_iff]
  have : {p : ℝ × ℝ | ¬ p.1 ≠ x} = ({x} : Set ℝ) ×ˢ (univ : Set ℝ) := by
    ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp

lemma ae_snd_ne (x : ℝ) : ∀ᵐ p : ℝ × ℝ, p.2 ≠ x := by
  rw [ae_iff]
  have : {p : ℝ × ℝ | ¬ p.2 ≠ x} = (univ : Set ℝ) ×ˢ ({x} : Set ℝ) := by
    ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]; simp

lemma limit_core {F G : ℝ × ℝ → ℂ} {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hFS : IntegrableOn F S) (hGS : IntegrableOn G S) (u v : ℕ → ℝ × ℝ → ℝ) (d e : ℝ × ℝ → ℝ) (C : ℝ)
    (hu : ∀ n, Continuous (u n)) (hv : ∀ n, Continuous (v n))
    (hout : ∀ᶠ n in atTop, ∀ p, p ∉ S → u n p = 0 ∧ v n p = 0)
    (hde : ∀ p, p ∉ S → d p = 0 ∧ e p = 0)
    (hb : ∀ n p, |u n p| ≤ C ∧ |v n p| ≤ C)
    (hlu : ∀ᵐ p, Tendsto (fun n => u n p) atTop (𝓝 (d p)))
    (hlv : ∀ p, Tendsto (fun n => v n p) atTop (𝓝 (e p)))
    (heq : ∀ᶠ n in atTop, ∫ p, (u n p : ℂ) * F p = -∫ p, (v n p : ℂ) * G p) :
    ∫ p, (d p : ℂ) * F p = -∫ p, (e p : ℂ) * G p := by
  have hF' : Integrable (S.indicator F) := (integrable_indicator_iff hS).2 hFS
  have hG' : Integrable (S.indicator G) := (integrable_indicator_iff hS).2 hGS
  have sw : ∀ (w : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ), (∀ p, p ∉ S → w p = 0) →
      (fun p => (w p : ℂ) * S.indicator H p) = fun p => (w p : ℂ) * H p := by
    intro w H hw; funext p
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp]
    · rw [hw p hp]; simp
  have L1 : Tendsto (fun n => ∫ p, (u n p : ℂ) * S.indicator F p) atTop
      (𝓝 (∫ p, (d p : ℂ) * S.indicator F p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => C * ‖S.indicator F p‖) ?_ ?_
      (hF'.norm.const_mul C) ?_
    · exact Eventually.of_forall fun n =>
        (Complex.continuous_ofReal.comp (hu n)).aestronglyMeasurable.mul hF'.aestronglyMeasurable
    · refine Eventually.of_forall fun n => Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb n p).1 (norm_nonneg _)
    · filter_upwards [hlu] with p hp
      exact ((Complex.continuous_ofReal.tendsto _).comp hp).mul_const _
  have L2 : Tendsto (fun n => ∫ p, (v n p : ℂ) * S.indicator G p) atTop
      (𝓝 (∫ p, (e p : ℂ) * S.indicator G p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => C * ‖S.indicator G p‖) ?_ ?_
      (hG'.norm.const_mul C) ?_
    · exact Eventually.of_forall fun n =>
        (Complex.continuous_ofReal.comp (hv n)).aestronglyMeasurable.mul hG'.aestronglyMeasurable
    · refine Eventually.of_forall fun n => Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb n p).2 (norm_nonneg _)
    · exact Eventually.of_forall fun p => ((Complex.continuous_ofReal.tendsto _).comp (hlv p)).mul_const _
  have E : ∀ᶠ n in atTop, -∫ p, (v n p : ℂ) * S.indicator G p = ∫ p, (u n p : ℂ) * S.indicator F p := by
    filter_upwards [heq, hout] with n hn ho
    rw [sw (u n) F (fun p hp => (ho p hp).1), sw (v n) G (fun p hp => (ho p hp).2)]
    exact hn.symm
  have := tendsto_nhds_unique (L1.congr' (E.mono fun n h => h.symm) |>.congr' (Eventually.of_forall fun _ => rfl)) L2.neg
  rw [← sw d F (fun p hp => (hde p hp).1), ← sw e G (fun p hp => (hde p hp).2)]
  exact this

lemma fderiv_prod_apply {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => f q.1 * g q.2) p (1, 0) = deriv f p.1 * g p.2 ∧
    fderiv ℝ (fun q : ℝ × ℝ => f q.1 * g q.2) p (0, 1) = f p.1 * deriv g p.2 := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => f q.1) (deriv f p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    (hf p.1).hasDerivAt.comp_hasFDerivAt p (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => g q.2) (deriv g p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (hg p.2).hasDerivAt.comp_hasFDerivAt p (hasFDerivAt_snd)
  have h3 : HasFDerivAt (fun q : ℝ × ℝ => f q.1 * g q.2) _ p := h1.mul h2
  rw [h3.fderiv]
  constructor <;> simp <;> ring

lemma tsupp_sym {χ : ℝ → ℝ} (hχc : HasCompactSupport χ) : ∃ Z : ℝ, tsupport χ ⊆ Icc (-Z) Z := by
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun z hm => ?_⟩
  have := hR hm
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  exact ⟨by linarith [neg_abs_le z], by linarith [le_abs_self z]⟩

lemma sym_bound {χ : ℝ → ℝ} (hχc : HasCompactSupport χ) : ∃ Z : ℝ, ∀ z, z ∉ Icc (-Z) Z → χ z = 0 := by
  obtain ⟨Z, hZ⟩ := tsupp_sym hχc
  exact ⟨Z, fun z hz => image_eq_zero_of_notMem_tsupport fun hm => hz (hZ hm)⟩

lemma pos_bound {χ : ℝ → ℝ} (hχc : HasCompactSupport χ) (hχp : ∀ r ∈ tsupport χ, 0 < r) :
    ∃ δ > 0, ∃ R : ℝ, ∀ r, r ∉ Icc δ R → χ r = 0 := by
  obtain ⟨R, hR⟩ := tsupp_sym hχc
  by_cases h : (tsupport χ).Nonempty
  · obtain ⟨r0, hr0, hmin⟩ := hχc.isCompact.exists_isMinOn h continuousOn_id
    exact ⟨r0, hχp r0 hr0, R, fun r hr => image_eq_zero_of_notMem_tsupport fun hm => hr ⟨hmin hm, (hR hm).2⟩⟩
  · exact ⟨1, one_pos, 0, fun r _ => image_eq_zero_of_notMem_tsupport fun hm => h ⟨r, hm⟩⟩

lemma moll_bound {a c b : ℝ} (hac : a < c) (hcb : c < b) {K : NNReal} (hK : LipschitzWith K (tentFn a c b))
    (n : ℕ) (x : ℝ) : |mollTent a c b n x| ≤ K * (b - a + 2) ∧ |deriv (mollTent a c b n) x| ≤ K := by
  have hL := moll_slope a c b hK n
  refine ⟨?_, by rw [← Real.norm_eq_abs]; exact norm_deriv_le_of_lipschitz hL⟩
  have h1 : 1 / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  have hK0 : (0 : ℝ) ≤ K := K.2
  by_cases hx : x ∈ Icc (a - 1) (b + 1)
  · have hz : mollTent a c b n (b + 1) = 0 :=
      moll_zero_of a c b hac hcb n _ fun hm => by linarith [hm.2]
    have := hL.dist_le_mul x (b + 1)
    rw [Real.dist_eq, Real.dist_eq, hz, sub_zero] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  · rw [(moll_vanish a c b hac hcb n x fun hm => hx ⟨by linarith [hm.1], by linarith [hm.2]⟩).1, abs_zero]
    have : 0 ≤ b - a + 2 := by linarith
    positivity

lemma moll_hasCompactSupport {a c b : ℝ} (hac : a < c) (hcb : c < b) (n : ℕ) :
    HasCompactSupport (mollTent a c b n) :=
  HasCompactSupport.intro (isCompact_Icc (a := a - 1 / ((n : ℝ) + 1)) (b := b + 1 / ((n : ℝ) + 1)))
    fun x hx => (moll_vanish a c b hac hcb n x hx).1

lemma small_eventually {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ε :=
  (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε))

theorem radial_core {F G : ℝ × ℝ → ℂ}
    (hF : ∀ δ R Z : ℝ, 0 < δ → IntegrableOn F (Icc δ R ×ˢ Icc (-Z) Z))
    (hG : ∀ δ R Z : ℝ, 0 < δ → IntegrableOn G (Icc δ R ×ˢ Icc (-Z) Z))
    (hw : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * G p)
    {a c b : ℝ} (ha : 0 < a) (hac : a < c) (hcb : c < b) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ∫ p, ((tentSlope a c b p.1 * χ p.2 : ℝ) : ℂ) * F p = -∫ p, ((tentFn a c b p.1 * χ p.2 : ℝ) : ℂ) * G p := by
  obtain ⟨Z, hZ⟩ := sym_bound hχc
  obtain ⟨K, hK⟩ := tent_slope a c b
  obtain ⟨Cχ, hCχ⟩ := hχc.exists_bound_of_continuous hχ.continuous
  set S := Icc (a / 2) (b + 1) ×ˢ Icc (-Z) Z
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hev := small_eventually (show 0 < min (a / 2) 1 by positivity)
  have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ 0)
  refine limit_core hS (hF _ _ _ (by positivity)) (hG _ _ _ (by positivity))
    (fun n p => deriv (mollTent a c b n) p.1 * χ p.2) (fun n p => mollTent a c b n p.1 * χ p.2)
    (fun p => tentSlope a c b p.1 * χ p.2) (fun p => tentFn a c b p.1 * χ p.2)
    (max (K : ℝ) (K * (b - a + 2)) * Cχ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n
    exact (((moll_smooth a c b n).continuous_deriv (by simp)).comp continuous_fst).mul
      (hχ.continuous.comp continuous_snd)
  · intro n
    exact ((moll_smooth a c b n).continuous.comp continuous_fst).mul (hχ.continuous.comp continuous_snd)
  · filter_upwards [hev] with n hn p hp
    have hn1 := (min_le_left _ _).trans' hn
    have hn2 := (min_le_right _ _).trans' hn
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc (a / 2) (b + 1) ∧ p.2 ∈ Icc (-Z) Z) from hp) with h | h
    · have hv := moll_vanish a c b hac hcb n p.1 fun hm => h ⟨by linarith [hm.1], by linarith [hm.2]⟩
      simp [hv.1, hv.2]
    · simp [hZ _ h]
  · intro p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc (a / 2) (b + 1) ∧ p.2 ∈ Icc (-Z) Z) from hp) with h | h
    · have h1 : p.1 ∉ Icc a b := fun hm => h ⟨by linarith [hm.1], by linarith [hm.2]⟩
      have h2 : tentSlope a c b p.1 = 0 := by unfold tentSlope; rw [if_neg h1]
      rw [h2, tent_zero hac hcb (fun hm => h1 ⟨hm.1.le, hm.2.le⟩)]; simp
    · simp [hZ _ h]
  · intro n p
    have hb := moll_bound hac hcb hK n p.1
    have hc := hCχ p.2
    rw [Real.norm_eq_abs] at hc
    constructor
    · rw [abs_mul]
      exact mul_le_mul (hb.2.trans (le_max_left _ _)) hc (abs_nonneg _) ((le_max_left _ _).trans' K.2)
    · rw [abs_mul]
      exact mul_le_mul (hb.1.trans (le_max_right _ _)) hc (abs_nonneg _) ((le_max_left _ _).trans' K.2)
  · filter_upwards [ae_fst_ne a, ae_fst_ne c, ae_fst_ne b] with p h1 h2 h3
    exact (moll_deriv_tendsto hac hcb h1 h2 h3).mul_const _
  · intro p
    exact (moll_tendsto a c b p.1).mul_const _
  · filter_upwards [hev] with n hn
    have hn1 := (min_le_left _ _).trans' hn
    have hsm : ContDiff ℝ ∞ (fun q : ℝ × ℝ => mollTent a c b n q.1 * χ q.2) :=
      ((moll_smooth a c b n).comp contDiff_fst).mul (hχ.comp contDiff_snd)
    have hcs : HasCompactSupport (fun q : ℝ × ℝ => mollTent a c b n q.1 * χ q.2) := by
      refine HasCompactSupport.intro ((moll_hasCompactSupport hac hcb n).isCompact.prod hχc.isCompact) ?_
      intro q hq
      rcases not_and_or.1 (show ¬ (q.1 ∈ tsupport (mollTent a c b n) ∧ q.2 ∈ tsupport χ) from hq) with h | h
      · simp [image_eq_zero_of_notMem_tsupport h]
      · simp [image_eq_zero_of_notMem_tsupport h]
    have hpos : ∀ q ∈ tsupport (fun q : ℝ × ℝ => mollTent a c b n q.1 * χ q.2), 0 < q.1 := by
      intro q hq
      have hsub : tsupport (fun q : ℝ × ℝ => mollTent a c b n q.1 * χ q.2) ⊆
          Icc (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1)) ×ˢ univ := by
        refine closure_minimal ?_ (isClosed_Icc.prod isClosed_univ)
        intro r hr
        refine ⟨?_, trivial⟩
        by_contra hm
        exact hr (by simp [(moll_vanish a c b hac hcb n r.1 hm).1])
      have := (hsub hq).1.1
      linarith
    have hfd := fun q => fderiv_prod_apply ((moll_smooth a c b n).differentiable (by simp))
      (hχ.differentiable (by simp)) q
    have := hw _ hsm hcs hpos
    simp only [(hfd _).1] at this
    exact this

theorem height_core {F G : ℝ × ℝ → ℂ}
    (hF : ∀ δ R Z : ℝ, 0 < δ → IntegrableOn F (Icc δ R ×ˢ Icc (-Z) Z))
    (hG : ∀ δ R Z : ℝ, 0 < δ → IntegrableOn G (Icc δ R ×ˢ Icc (-Z) Z))
    (hw : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * G p)
    {a c b : ℝ} (hac : a < c) (hcb : c < b) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχp : ∀ r ∈ tsupport χ, 0 < r) :
    ∫ p, ((χ p.1 * tentSlope a c b p.2 : ℝ) : ℂ) * F p = -∫ p, ((χ p.1 * tentFn a c b p.2 : ℝ) : ℂ) * G p := by
  obtain ⟨δ, hδ, R, hR⟩ := pos_bound hχc hχp
  obtain ⟨K, hK⟩ := tent_slope a c b
  obtain ⟨Cχ, hCχ⟩ := hχc.exists_bound_of_continuous hχ.continuous
  set Z := |a| + |b| + 1
  have hZd : Z = |a| + |b| + 1 := rfl
  set S := Icc δ R ×ˢ Icc (-Z) Z
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ 0)
  have hZ1 : ∀ n : ℕ, ∀ z, z ∉ Icc (-Z) Z → z ∉ Icc (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1)) := by
    intro n z hz hm
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    exact hz ⟨by linarith [hm.1, neg_abs_le a, abs_nonneg b], by linarith [hm.2, le_abs_self b, abs_nonneg a]⟩
  refine limit_core hS (hF _ _ _ hδ) (hG _ _ _ hδ)
    (fun n p => χ p.1 * deriv (mollTent a c b n) p.2) (fun n p => χ p.1 * mollTent a c b n p.2)
    (fun p => χ p.1 * tentSlope a c b p.2) (fun p => χ p.1 * tentFn a c b p.2)
    (Cχ * max (K : ℝ) (K * (b - a + 2))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n
    exact (hχ.continuous.comp continuous_fst).mul
      (((moll_smooth a c b n).continuous_deriv (by simp)).comp continuous_snd)
  · intro n
    exact (hχ.continuous.comp continuous_fst).mul ((moll_smooth a c b n).continuous.comp continuous_snd)
  · refine Eventually.of_forall fun n p hp => ?_
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc δ R ∧ p.2 ∈ Icc (-Z) Z) from hp) with h | h
    · simp [hR _ h]
    · have hv := moll_vanish a c b hac hcb n p.2 (hZ1 n _ h)
      simp [hv.1, hv.2]
  · intro p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc δ R ∧ p.2 ∈ Icc (-Z) Z) from hp) with h | h
    · simp [hR _ h]
    · have h1 : p.2 ∉ Icc a b := fun hm =>
        h ⟨by linarith [hm.1, neg_abs_le a, abs_nonneg b], by linarith [hm.2, le_abs_self b, abs_nonneg a]⟩
      have h2 : tentSlope a c b p.2 = 0 := by unfold tentSlope; rw [if_neg h1]
      rw [h2, tent_zero hac hcb (fun hm => h1 ⟨hm.1.le, hm.2.le⟩)]; simp
  · intro n p
    have hb := moll_bound hac hcb hK n p.2
    have hc := hCχ p.1
    rw [Real.norm_eq_abs] at hc
    constructor
    · rw [abs_mul]
      exact mul_le_mul hc (hb.2.trans (le_max_left _ _)) (abs_nonneg _) hCχ0
    · rw [abs_mul]
      exact mul_le_mul hc (hb.1.trans (le_max_right _ _)) (abs_nonneg _) hCχ0
  · filter_upwards [ae_snd_ne a, ae_snd_ne c, ae_snd_ne b] with p h1 h2 h3
    exact (moll_deriv_tendsto hac hcb h1 h2 h3).const_mul _
  · intro p
    exact (moll_tendsto a c b p.2).const_mul _
  · refine Eventually.of_forall fun n => ?_
    have hsm : ContDiff ℝ ∞ (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) :=
      (hχ.comp contDiff_fst).mul ((moll_smooth a c b n).comp contDiff_snd)
    have hcs : HasCompactSupport (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) := by
      refine HasCompactSupport.intro (hχc.isCompact.prod (moll_hasCompactSupport hac hcb n).isCompact) ?_
      intro q hq
      rcases not_and_or.1 (show ¬ (q.1 ∈ tsupport χ ∧ q.2 ∈ tsupport (mollTent a c b n)) from hq) with h | h
      · simp [image_eq_zero_of_notMem_tsupport h]
      · simp [image_eq_zero_of_notMem_tsupport h]
    have hpos : ∀ q ∈ tsupport (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2), 0 < q.1 := by
      intro q hq
      have hsub : tsupport (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) ⊆ tsupport χ ×ˢ univ := by
        refine closure_minimal ?_ ((isClosed_tsupport χ).prod isClosed_univ)
        intro r hr
        refine ⟨subset_tsupport _ ?_, trivial⟩
        intro h0
        exact hr (by simp [h0])
      exact hχp _ (hsub hq).1
    have hfd := fun q => fderiv_prod_apply (hχ.differentiable (by simp))
      ((moll_smooth a c b n).differentiable (by simp)) q
    have := hw _ hsm hcs hpos
    simp only [(hfd _).2] at this
    exact this

lemma tentSlope_meas (a c b : ℝ) : Measurable (tentSlope a c b) := by
  have e : tentSlope a c b = fun x => if x ∈ Icc a b then (if x ≤ c then 1 / (c - a) else 1 / (c - b)) else 0 := by
    funext x; unfold tentSlope; split_ifs <;> rfl
  rw [e]
  exact Measurable.ite measurableSet_Icc
    (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const)
    measurable_const

lemma tentSlope_bound (a c b x : ℝ) : |tentSlope a c b x| ≤ |1 / (c - a)| + |1 / (c - b)| := by
  unfold tentSlope
  have e1 := inv_nonneg.2 (abs_nonneg (c - a))
  have e2 := inv_nonneg.2 (abs_nonneg (c - b))
  split_ifs <;> simp <;> linarith

lemma tentFn_bound {a c b : ℝ} (hac : a < c) (hcb : c < b) : ∃ C, ∀ x, |tentFn a c b x| ≤ C := by
  have hcs : HasCompactSupport (tentFn a c b) :=
    HasCompactSupport.intro (isCompact_Icc (a := a) (b := b))
      fun x hx => tent_zero hac hcb fun hm => hx ⟨hm.1.le, hm.2.le⟩
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous (tent_cont a c b)
  exact ⟨C, fun x => by rw [← Real.norm_eq_abs]; exact hC x⟩

lemma tent_out {a c b x : ℝ} (hac : a < c) (hcb : c < b) (hx : x ∉ Icc a b) :
    tentSlope a c b x = 0 ∧ tentFn a c b x = 0 := by
  refine ⟨by unfold tentSlope; rw [if_neg hx], tent_zero hac hcb fun hm => hx ⟨hm.1.le, hm.2.le⟩⟩

lemma int_region {H : ℝ × ℝ → ℂ} {s1 s2 : Set ℝ} (h1 : MeasurableSet s1) (h2 : MeasurableSet s2)
    (hH : IntegrableOn H (s1 ×ˢ s2)) {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v) {Cu Cv : ℝ}
    (hbu : ∀ x, |u x| ≤ Cu) (hbv : ∀ x, |v x| ≤ Cv) (hzu : ∀ x, x ∉ s1 → u x = 0)
    (hzv : ∀ x, x ∉ s2 → v x = 0) :
    Integrable (fun p : ℝ × ℝ => ((u p.1 * v p.2 : ℝ) : ℂ) * H p) := by
  have e : (fun p : ℝ × ℝ => ((u p.1 * v p.2 : ℝ) : ℂ) * H p) =
      fun p => ((u p.1 * v p.2 : ℝ) : ℂ) * (s1 ×ˢ s2).indicator H p := by
    funext p
    by_cases hp : p ∈ s1 ×ˢ s2
    · rw [Set.indicator_of_mem hp]
    · rcases not_and_or.1 (show ¬ (p.1 ∈ s1 ∧ p.2 ∈ s2) from hp) with h | h
      · simp [hzu _ h]
      · simp [hzv _ h]
  rw [e]
  have hCu : 0 ≤ Cu := (abs_nonneg _).trans (hbu 0)
  refine ((integrable_indicator_iff (h1.prod h2)).2 hH).bdd_mul (c := Cu * Cv)
    (Complex.measurable_ofReal.comp ((hu.comp measurable_fst).mul (hv.comp measurable_snd))).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hbu _) (hbv _) (abs_nonneg _) hCu

lemma slice_zero {Φ : ℝ × ℝ → ℂ} {lo hi : ℝ} {t : Set ℝ}
    (hI : IntegrableOn Φ (Icc lo hi ×ˢ t))
    (hχ : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo lo hi →
      ∫ p in Icc lo hi ×ˢ t, (χ p.1 : ℂ) * Φ p = 0) :
    ∫ p in Icc lo hi ×ˢ t, Φ p = 0 := by
  have hIp : Integrable Φ ((volume.restrict (Icc lo hi)).prod (volume.restrict t)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hI
  have hk : IntegrableOn (fun x => ∫ y in t, Φ (x, y)) (Icc lo hi) := hIp.integral_prod_left
  have hz : ∀ᵐ x, x ∈ Ioo lo hi → (∫ y in t, Φ (x, y)) = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hk.mono_set Ioo_subset_Icc_self).locallyIntegrableOn ?_
    intro χ hχs hχc hχt
    obtain ⟨C, hC⟩ := hχc.exists_bound_of_continuous hχs.continuous
    have e1 : ∫ x, χ x • ∫ y in t, Φ (x, y) = ∫ x in Icc lo hi, χ x • ∫ y in t, Φ (x, y) := by
      symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (Ioo_subset_Icc_self (hχt hm))), zero_smul]
    have hIχ : Integrable (fun p : ℝ × ℝ => (χ p.1 : ℂ) * Φ p)
        ((volume.restrict (Icc lo hi)).prod (volume.restrict t)) := by
      refine hIp.bdd_mul (c := C)
        (Complex.continuous_ofReal.comp (hχs.continuous.comp continuous_fst)).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      rw [Complex.norm_real]; exact hC _
    have e2 : ∫ x in Icc lo hi, χ x • ∫ y in t, Φ (x, y) = ∫ p in Icc lo hi ×ˢ t, (χ p.1 : ℂ) * Φ p := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hIχ]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show χ x • ∫ y in t, Φ (x, y) = ∫ y in t, (χ x : ℂ) * Φ (x, y)
      rw [← integral_smul]
      simp only [Complex.real_smul]
    rw [e1, e2]
    exact hχ χ hχs hχc hχt
  have e3 : ∫ p in Icc lo hi ×ˢ t, Φ p = ∫ x in Icc lo hi, ∫ y in t, Φ (x, y) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hIp]
  rw [e3, integral_Icc_eq_integral_Ioo]
  exact setIntegral_eq_zero_of_ae_eq_zero hz

lemma bdd_of_csupp {χ : ℝ → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) : ∃ C, ∀ x, |χ x| ≤ C := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hχ
  exact ⟨C, fun x => by rw [← Real.norm_eq_abs]; exact hC x⟩

end Breakdown.FracInternal.CornerParts

namespace Breakdown.FracInternal.CornerModes

open Set Real
open Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.CellAnalysis
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem half_le (R Z : ℝ) :
    volume.restrict (Icc (0 : ℝ) R ×ˢ Icc (-Z) Z) ≤ volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  refine Measure.restrict_mono_ae ?_
  have hsub : Icc (0 : ℝ) R ×ˢ Icc (-Z) Z ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨hp.1.1, trivial⟩
  refine hsub.eventuallyLE.trans ?_
  have : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) =ᵐ[volume] Ici (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    Measure.set_prod_ae_eq Ioi_ae_eq_Ici (ae_eq_refl _)
  exact this.symm.le

theorem kmeas {X : Space → E} (hXm : AEStronglyMeasurable X volume)
    (φ : ℝ → E → ℂ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2)))
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  have hf : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => φ q.2 (X (cylArg q))) muU :=
    hφc.comp_aestronglyMeasurable (measurable_snd.aestronglyMeasurable.prodMk
      (hXm.comp_quasiMeasurePreserving qmp))
  rw [muU_def] at hf
  exact hf.integral_prod_right'

theorem half_eq (g : Space → ENNReal) (hgm : AEMeasurable g volume) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
      ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) = ∫⁻ y, g y := by
  rw [← key g, muU_def, lintegral_prod]
  · congr 1; funext p
    dsimp only
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  · exact (ENNReal.measurable_ofReal.comp measurable_fst.fst).aemeasurable.mul
      (hgm.comp_quasiMeasurePreserving (muU_def ▸ qmp))

theorem weighted_int (R Z : ℝ) {X : Space → E} (hX : LocallyIntegrable X volume)
    (φ : ℝ → E → ℂ) (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2)))
      (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have hXm := hX.aestronglyMeasurable
  have hF := kmeas hXm φ hφc
  have hS : MeasurableSet (Icc (0 : ℝ) R ×ˢ Icc (-Z) Z) := measurableSet_Icc.prod measurableSet_Icc
  set ρ : ℝ := 2 * |R| + |Z| with hρ
  set g : Space → ENNReal := (Metric.closedBall (0 : Space) ρ).indicator (fun y => ‖X y‖ₑ) with hg_def
  have hball : ∀ p ∈ Icc (0 : ℝ) R ×ˢ Icc (-Z) Z, ∀ θ,
      cylPoint p.1 θ p.2 ∈ Metric.closedBall (0 : Space) ρ := by
    intro p hp θ
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (LowEntry.Internal.cylPoint_norm _ _ _).trans ?_
    have h1 : |p.1| ≤ |R| := by rw [abs_of_nonneg hp.1.1]; exact hp.1.2.trans (le_abs_self R)
    have h2 : |p.2| ≤ |Z| := abs_le.2 ⟨by linarith [hp.2.1, le_abs_self Z], hp.2.2.trans (le_abs_self Z)⟩
    rw [hρ]
    linarith
  have hpt : ∀ p ∈ Icc (0 : ℝ) R ×ˢ Icc (-Z) Z,
      ‖(p.1 : ℂ) * ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ ≤
        ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
    intro p hp
    have hi : ‖∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ ≤
        ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun θ => ?_)
      rw [hg_def, Set.indicator_of_mem (hball p hp θ), ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hφb θ _)
    have hw : ‖((p.1 : ℝ) : ℂ)‖ₑ = ENNReal.ofReal p.1 := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.1.1]
    rw [enorm_mul, hw]
    exact mul_le_mul' le_rfl hi
  have hgm : AEMeasurable g volume := hXm.enorm.indicator measurableSet_closedBall
  have hfin : ∫⁻ y, g y < ⊤ := by
    rw [hg_def, lintegral_indicator measurableSet_closedBall]
    exact (hX.integrableOn_isCompact (isCompact_closedBall 0 ρ)).2
  refine ⟨(Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul
    (hF.mono_measure (half_le R Z)), ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt ?_ hfin
  calc ∫⁻ p in Icc (0 : ℝ) R ×ˢ Icc (-Z) Z,
        ‖(p.1 : ℂ) * ∫ θ in Ioo (-π) π, φ θ (X (cylPoint p.1 θ p.2))‖ₑ
      ≤ ∫⁻ p in Icc (0 : ℝ) R ×ˢ Icc (-Z) Z,
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := setLIntegral_mono' hS hpt
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := lintegral_mono' (half_le R Z) le_rfl
    _ = ∫⁻ y, g y := half_eq g hgm

theorem root_power_bound (r t : ℝ) (hr : 0 < r) (_ht : 0 ≤ t) : t ≤ r ^ (-(1 / 5 : ℝ)) + r * t ^ 6 := by
  set s := r ^ (-(1 / 5 : ℝ)) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hr _
  have h5 : s ^ 5 = r⁻¹ := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hr.le,
      show (-(1 / 5 : ℝ)) * ((5 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have h6 : 0 ≤ r * t ^ 6 := by positivity
  by_cases h : t ≤ s
  · linarith
  · push Not at h
    have h5' : s ^ 5 < t ^ 5 := pow_lt_pow_left₀ h hs0.le (by norm_num)
    have h1 : 1 < r * t ^ 5 := by
      rw [h5] at h5'
      have := mul_lt_mul_of_pos_left h5' hr
      rwa [mul_inv_cancel₀ hr.ne'] at this
    have ht0 : 0 < t := hs0.trans h
    have h2 : t * 1 < t * (r * t ^ 5) := mul_lt_mul_of_pos_left h1 ht0
    have e : t * (r * t ^ 5) = r * t ^ 6 := by ring
    linarith

theorem pt_bound (r : ℝ) (hr : 0 < r) (φ : ℝ → Space → ℂ) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) (θ : ℝ) (u : Space) :
    ‖φ θ u‖ₑ ≤ ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) + ENNReal.ofReal r * ‖u‖ₑ ^ 6 := by
  have h := (hφb θ u).trans (root_power_bound r ‖u‖ hr (norm_nonneg _))
  calc ‖φ θ u‖ₑ = ENNReal.ofReal ‖φ θ u‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (r ^ (-(1 / 5 : ℝ)) + r * ‖u‖ ^ 6) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) + ENNReal.ofReal r * ‖u‖ₑ ^ 6 := by
      rw [ENNReal.ofReal_add (Real.rpow_nonneg hr.le _) (by positivity), ENNReal.ofReal_mul hr.le,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem vel_int (R Z : ℝ) {v : Space → Space} (hv : MemLp v 6 volume) (φ : ℝ → Space → ℂ)
    (hφc : Continuous (fun q : ℝ × Space => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖) :
    IntegrableOn (fun p : ℝ × ℝ => ∫ θ in Ioo (-π) π, φ θ (v (cylPoint p.1 θ p.2)))
      (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have hvm := hv.aestronglyMeasurable
  have hF := kmeas hvm φ hφc
  have hS : MeasurableSet (Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z) := measurableSet_Ioc.prod measurableSet_Icc
  have hSI : (Icc (0 : ℝ) R ×ˢ Icc (-Z) Z : Set (ℝ × ℝ)) =ᵐ[volume] Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z :=
    Measure.set_prod_ae_eq Ioc_ae_eq_Icc.symm (ae_eq_refl _)
  refine IntegrableOn.congr_set_ae ?_ hSI
  have hsub : Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := fun p hp => ⟨hp.1.1, trivial⟩
  set g : Space → ENNReal := fun y => ‖v y‖ₑ ^ 6 with hg_def
  have hgm : AEMeasurable g volume := hvm.enorm.pow_const 6
  have hfin : ∫⁻ y, g y < ⊤ := by
    have h6 : Integrable (fun y => ‖v y‖ ^ 6) :=
      (show MemLp v ((6 : ℕ) : ENNReal) volume by exact_mod_cast hv).integrable_norm_pow (by norm_num)
    have := h6.hasFiniteIntegral
    unfold HasFiniteIntegral at this
    simpa only [enorm_pow, enorm_norm, hg_def] using this
  have hP : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ (-(1 / 5 : ℝ))) (Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z) := by
    have h1 : IntegrableOn (fun r : ℝ => r ^ (-(1 / 5 : ℝ))) (Ioc 0 R) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) (by norm_num : (-1 : ℝ) < -(1 / 5))).1
    have h2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-Z) Z) := integrableOn_const (by simp)
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    simpa using h1.mul_prod h2
  have hpt : ∀ p ∈ Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z,
      ‖∫ θ in Ioo (-π) π, φ θ (v (cylPoint p.1 θ p.2))‖ₑ ≤
        ENNReal.ofReal (2 * π) * ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ +
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
    intro p hp
    have hr : 0 < p.1 := hp.1.1
    have hc : ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ = ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) :=
      Real.enorm_eq_ofReal (Real.rpow_nonneg hr.le _)
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ θ in Ioo (-π) π, ‖φ θ (v (cylPoint p.1 θ p.2))‖ₑ
        ≤ ∫⁻ θ in Ioo (-π) π, (ENNReal.ofReal (p.1 ^ (-(1 / 5 : ℝ))) +
            ENNReal.ofReal p.1 * g (cylPoint p.1 θ p.2)) :=
          lintegral_mono fun θ => pt_bound p.1 hr φ hφb θ _
      _ = ENNReal.ofReal (2 * π) * ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ +
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Real.volume_Ioo, hc,
            show π - -π = 2 * π by ring]
          ring
  have hA : ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ < ⊤ := hP.2
  have hB : ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z,
      ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) < ⊤ := by
    refine lt_of_le_of_lt ?_ hfin
    rw [← half_eq g hgm]
    exact lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
  refine ⟨hF.mono_measure (Measure.restrict_mono hsub le_rfl), ?_⟩
  unfold HasFiniteIntegral
  have hm1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (2 * π) * ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ :=
    measurable_const.mul (measurable_fst.pow_const _).enorm
  calc ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, ‖∫ θ in Ioo (-π) π, φ θ (v (cylPoint p.1 θ p.2))‖ₑ
      ≤ ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, (ENNReal.ofReal (2 * π) * ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ +
          ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2)) := setLIntegral_mono' hS hpt
    _ = ENNReal.ofReal (2 * π) * (∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z, ‖p.1 ^ (-(1 / 5 : ℝ))‖ₑ) +
          ∫⁻ p in Ioc (0 : ℝ) R ×ˢ Icc (-Z) Z,
            ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
        rw [lintegral_add_left hm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA, hB⟩

theorem off_int (δ R Z : ℝ) (hδ : 0 < δ) {F : ℝ × ℝ → ℂ}
    (hw : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Icc 0 R ×ˢ Icc (-Z) Z))
    (hm : AEStronglyMeasurable F (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)))) :
    IntegrableOn F (Icc δ R ×ˢ Icc (-Z) Z) := by
  have hsub : Icc δ R ×ˢ Icc (-Z) Z ⊆ Icc 0 R ×ˢ Icc (-Z) Z :=
    prod_mono (Icc_subset_Icc_left hδ.le) le_rfl
  have hsub' : Icc δ R ×ˢ Icc (-Z) Z ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    fun p hp => ⟨hδ.trans_le hp.1.1, trivial⟩
  have hS : MeasurableSet (Icc δ R ×ˢ Icc (-Z) Z) := measurableSet_Icc.prod measurableSet_Icc
  refine Integrable.mono' (((hw.mono_set hsub).norm).const_mul δ⁻¹)
    (hm.mono_measure (Measure.restrict_mono hsub' le_rfl)) ?_
  filter_upwards [ae_restrict_mem hS] with p hp
  have h1 : δ ≤ p.1 := hp.1.1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hδ.trans_le h1)]
  have h2 : 1 ≤ δ⁻¹ * p.1 := by rw [inv_mul_eq_div, le_div_iff₀ hδ]; linarith
  nlinarith [norm_nonneg (F p)]

theorem memLp_grad {G : Space → (Space →L[ℝ] Space)} (hG1 : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => entrySq (G y))) : MemLp G 2 volume :=
  (memLp_two_iff_integrable_sq_norm hG1).2 ((hG2.const_mul 3).mono'
    ((hG1.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact EmbedWeak.Internal.norm_sq_le (G y)))

theorem third_eq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) (p : ℝ × ℝ) :
    modeThird m n H a 0 2 p = gradMode m n (fun y => H y axialUnit) a 0 p := rfl

theorem axial_meas {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume) :
    AEStronglyMeasurable (fun y => H y axialUnit) volume :=
  (continuous_id.clm_apply (continuous_const (y := axialUnit))).comp_aestronglyMeasurable hH

theorem axial_sq {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    Integrable (fun y => entrySq (H y axialUnit)) := by
  have hc : Continuous entrySq := by
    unfold entrySq
    fun_prop
  refine h2.mono' (hc.comp_aestronglyMeasurable (axial_meas hH)) (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ entrySq (H y axialUnit) := by unfold entrySq; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  calc entrySq (H y axialUnit) = ∑ j : Fin 3, ‖H y (unitVector 2) (unitVector j)‖ ^ 2 := rfl
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)
        (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ 2)

end Breakdown.FracInternal.CornerModes

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

theorem modes_integrable_height_axis_of (h : ModeHeightAxisStatement) {k N : ℕ} (c : FracCellData k N)
    (x : FieldTuple k) (hx : IsAdmissible c x) (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3)
    (R Z : ℝ) :
    IntegrableOn (L.gradModeOf n x a 2) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z) :=
  h L.order x.1 x.2.1 x.2.2.1 (by rw [hL]; exact hx.1) n a R Z

theorem modes_weak_identities_of (h : ModeWeakIdentityStatement) {k N : ℕ} (c : FracCellData k N)
    (x : FieldTuple k) (hx : IsAdmissible c x) (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * L.velMode n x a p = -∫ p, (ψ p : ℂ) * L.gradModeOf n x a 0 p) ∧
    (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * L.velMode n x a p = -∫ p, (ψ p : ℂ) * L.gradModeOf n x a 2 p) ∧
    (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * L.gradModeOf n x a 2 p =
      -∫ p, (ψ p : ℂ) * L.secondModeOf n x a 0 2 p) ∧
    (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * L.gradModeOf n x a 0 p =
      -∫ p, (ψ p : ℂ) * L.secondModeOf n x a 0 2 p) :=
  h L.order x.1 x.2.1 x.2.2.1 (by rw [hL]; exact hx.1) n a ψ hψ hc hpos


open Breakdown.FracInternal.CornerModes LowEntry.Internal in
theorem modes_integrable_weighted {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) (R Z : ℝ) :
    IntegrableOn (L.velMode n x a) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z) ∧
    IntegrableOn (fun p => (p.1 : ℂ) * L.gradModeOf n x a 0 p) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z) ∧
    IntegrableOn (fun p => (p.1 : ℂ) * L.secondModeOf n x a 0 2 p) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z) := by
  have hs : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := by rw [hL]; exact hx.1
  refine ⟨?_, ?_, ?_⟩
  · have h := vel_int R Z hs.velocity_six (velKernel L.order n a) (velKernel_cont L.order n a)
      (velKernel_bound L.order n a)
    have e : L.velMode n x a = fun p => (1 / (2 * Real.pi) : ℂ) *
        ∫ θ in Set.Ioo (-Real.pi) Real.pi, velKernel L.order n a θ (x.1 (cylPoint p.1 θ p.2)) := by
      funext p
      exact modeVec_eq L.order n x.1 a p
    rw [e]
    exact h.const_mul _
  · have hG := memLp_grad hs.measurable_gradient hs.gradient_two
    have h := weighted_int R Z (hG.locallyIntegrable (by norm_num)) (gradKernel L.order n a 0)
      (gradKernel_cont L.order n a 0) (gradKernel_bound L.order n a 0)
    have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * L.gradModeOf n x a 0 p) = fun p => (1 / (2 * Real.pi) : ℂ) *
        ((p.1 : ℂ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          gradKernel L.order n a 0 θ (x.2.1 (cylPoint p.1 θ p.2))) := by
      funext p
      rw [show L.gradModeOf n x a 0 p = gradMode L.order n x.2.1 a 0 p from rfl, gradMode_eq]
      ring
    rw [e]
    exact h.const_mul _
  · have hG := memLp_grad (axial_meas hs.measurable_second) (axial_sq hs.measurable_second hs.second_two)
    have h := weighted_int R Z (hG.locallyIntegrable (by norm_num)) (gradKernel L.order n a 0)
      (gradKernel_cont L.order n a 0) (gradKernel_bound L.order n a 0)
    have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * L.secondModeOf n x a 0 2 p) = fun p => (1 / (2 * Real.pi) : ℂ) *
        ((p.1 : ℂ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          gradKernel L.order n a 0 θ (x.2.2.1 (cylPoint p.1 θ p.2) axialUnit)) := by
      funext p
      rw [show L.secondModeOf n x a 0 2 p = modeThird L.order n x.2.2.1 a 0 2 p from rfl, third_eq,
        gradMode_eq]
      ring
    rw [e]
    exact h.const_mul _

theorem modes_integrable_height_axis {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) (R Z : ℝ) :
    IntegrableOn (L.gradModeOf n x a 2) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z) :=
  modes_integrable_height_axis_of modeHeightAxis c x hx L hL n a R Z

open Breakdown.FracInternal.CornerModes LowEntry.Internal in
theorem modes_integrable_off {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) (δ R Z : ℝ) (hδ : 0 < δ) :
    IntegrableOn (L.gradModeOf n x a 0) (Set.Icc δ R ×ˢ Set.Icc (-Z) Z) ∧
    IntegrableOn (L.secondModeOf n x a 0 2) (Set.Icc δ R ×ˢ Set.Icc (-Z) Z) := by
  have hs : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := by rw [hL]; exact hx.1
  have hw := modes_integrable_weighted c x hx L hL n a R Z
  refine ⟨off_int δ R Z hδ hw.2.1 ?_, off_int δ R Z hδ hw.2.2 ?_⟩
  · have h := (kmeas hs.measurable_gradient (gradKernel L.order n a 0) (gradKernel_cont L.order n a 0)).const_mul
      (1 / (2 * Real.pi) : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    exact (gradMode_eq L.order n x.2.1 a 0 p).symm
  · have h := (kmeas (axial_meas hs.measurable_second) (gradKernel L.order n a 0)
      (gradKernel_cont L.order n a 0)).const_mul (1 / (2 * Real.pi) : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    exact (gradMode_eq L.order n (fun y => x.2.2.1 y axialUnit) a 0 p).symm

theorem modes_weak_identities {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * L.velMode n x a p = -∫ p, (ψ p : ℂ) * L.gradModeOf n x a 0 p) ∧
    (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * L.velMode n x a p = -∫ p, (ψ p : ℂ) * L.gradModeOf n x a 2 p) ∧
    (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * L.gradModeOf n x a 2 p =
      -∫ p, (ψ p : ℂ) * L.secondModeOf n x a 0 2 p) ∧
    (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * L.gradModeOf n x a 0 p =
      -∫ p, (ψ p : ℂ) * L.secondModeOf n x a 0 2 p) :=
  modes_weak_identities_of modeWeakIdentity c x hx L hL n a ψ hψ hc hpos

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis
open Breakdown.FracInternal.CornerParts

def IsMixedWeakQuad (F Fr Fz Frz : ℝ × ℝ → ℂ) : Prop :=
  (∀ R Z : ℝ, IntegrableOn F (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z) ∧ IntegrableOn Fz (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z) ∧
      IntegrableOn (fun p => (p.1 : ℂ) * Fr p) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z) ∧
      IntegrableOn (fun p => (p.1 : ℂ) * Frz p) (Set.Icc 0 R ×ˢ Set.Icc (-Z) Z)) ∧
  (∀ δ R Z : ℝ, 0 < δ → IntegrableOn Fr (Set.Icc δ R ×ˢ Set.Icc (-Z) Z) ∧
      IntegrableOn Frz (Set.Icc δ R ×ˢ Set.Icc (-Z) Z)) ∧
  (∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
    (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * Fr p) ∧
    (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * Fz p) ∧
    (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * Fz p = -∫ p, (ψ p : ℂ) * Frz p) ∧
    (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * Fr p = -∫ p, (ψ p : ℂ) * Frz p))

theorem modes_mixedWeak_of_parts {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) :
    IsMixedWeakQuad (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
      (L.secondModeOf n x a 0 2) :=
  ⟨fun R Z => ⟨(modes_integrable_weighted c x hx L hL n a R Z).1,
      modes_integrable_height_axis c x hx L hL n a R Z,
      (modes_integrable_weighted c x hx L hL n a R Z).2.1, (modes_integrable_weighted c x hx L hL n a R Z).2.2⟩,
    fun δ R Z hδ => modes_integrable_off c x hx L hL n a δ R Z hδ,
    fun ψ hψ hc hpos => modes_weak_identities c x hx L hL n a ψ hψ hc hpos⟩

theorem modes_mixedWeak_of_statements (h2 : ModeHeightAxisStatement) (h4 : ModeWeakIdentityStatement)
    {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) :
    IsMixedWeakQuad (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
      (L.secondModeOf n x a 0 2) :=
  ⟨fun R Z => ⟨(modes_integrable_weighted c x hx L hL n a R Z).1,
      modes_integrable_height_axis_of h2 c x hx L hL n a R Z,
      (modes_integrable_weighted c x hx L hL n a R Z).2.1, (modes_integrable_weighted c x hx L hL n a R Z).2.2⟩,
    fun δ R Z hδ => modes_integrable_off c x hx L hL n a δ R Z hδ,
    fun ψ hψ hc hpos => modes_weak_identities_of h4 c x hx L hL n a ψ hψ hc hpos⟩

def cornerTerm (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p
    + (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p
    + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * Fr p
    + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p

theorem modes_mixedWeak {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) :
    IsMixedWeakQuad (L.velMode n x a) (L.gradModeOf n x a 0) (L.gradModeOf n x a 2)
      (L.secondModeOf n x a 0 2) :=
  modes_mixedWeak_of_parts c x hx L hL n a

private lemma quad_F {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz) (δ R Z : ℝ) (hδ : 0 < δ) :
    IntegrableOn F (Set.Icc δ R ×ˢ Set.Icc (-Z) Z) ∧ IntegrableOn Fz (Set.Icc δ R ×ˢ Set.Icc (-Z) Z) := by
  have hs : Set.Icc δ R ×ˢ Set.Icc (-Z) Z ⊆ Set.Icc 0 R ×ˢ Set.Icc (-Z) Z :=
    Set.prod_mono (Set.Icc_subset_Icc_left hδ.le) le_rfl
  exact ⟨(h.1 R Z).1.mono_set hs, (h.1 R Z).2.1.mono_set hs⟩

theorem height_tent_zero {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz)
    {cr orr cz a b : ℝ} (hcr : 0 < cr) (hr : 0 ≤ min cr orr) (hrc : orr ≠ cr) (hac : a < cz) (hcb : cz < b) :
    ∫ p in Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc a b,
      cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p = 0 := by
  set lo := min cr orr
  set hi := max cr orr
  have hmeas : MeasurableSet (Set.Icc lo hi ×ˢ Set.Icc a b) := measurableSet_Icc.prod measurableSet_Icc
  set Φ : ℝ × ℝ → ℂ := fun p =>
    (((1 / (cr - orr) : ℝ)) : ℂ) * (((tentSlope a cz b p.2 : ℝ) : ℂ) * F p + ((tentFn a cz b p.2 : ℝ) : ℂ) * Fz p)
    + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) *
      (((tentSlope a cz b p.2 : ℝ) : ℂ) * Fr p + ((tentFn a cz b p.2 : ℝ) : ℂ) * Frz p) with hΦ
  have heq : Set.EqOn (fun p => cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p) Φ
      (Set.Icc lo hi ×ˢ Set.Icc a b) := by
    intro p hp
    have hz := hp.2
    simp only [cornerTerm, hΦ]
    rw [tent_eq_on hac hcb hz]
    unfold tentSlope
    rw [if_pos hz]
    ring
  by_cases hI : IntegrableOn (fun p => cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p)
      (Set.Icc lo hi ×ˢ Set.Icc a b)
  swap
  · exact integral_undef hI
  rw [setIntegral_congr_fun hmeas heq]
  refine slice_zero (hI.congr_fun heq hmeas) ?_
  intro χ hχs hχc hχt
  have hχp : ∀ r ∈ tsupport χ, 0 < r := fun r hm => lt_of_le_of_lt hr (hχt hm).1
  obtain ⟨δ, hδ, R, hR⟩ := pos_bound hχc hχp
  set Z := |a| + |b| with hZd
  have hab : ∀ z, z ∉ Set.Icc (-Z) Z → z ∉ Set.Icc a b := fun z hz hm =>
    hz ⟨by linarith [hm.1, neg_abs_le a, abs_nonneg b], by linarith [hm.2, le_abs_self b, abs_nonneg a]⟩
  set χ1 : ℝ → ℝ := fun r => χ r * (1 / (cr - orr)) with hχ1
  set χ2 : ℝ → ℝ := fun r => χ r * ((r - orr) / (cr - orr)) with hχ2
  have s1 : ContDiff ℝ ∞ χ1 := hχs.mul contDiff_const
  have s2 : ContDiff ℝ ∞ χ2 := hχs.mul ((contDiff_id.sub contDiff_const).div_const _)
  have c1 : HasCompactSupport χ1 := hχc.mul_right
  have c2 : HasCompactSupport χ2 := hχc.mul_right
  have p1 : ∀ r ∈ tsupport χ1, 0 < r := fun r hm => hχp r (tsupport_mul_subset_left hm)
  have p2 : ∀ r ∈ tsupport χ2, 0 < r := fun r hm => hχp r (tsupport_mul_subset_left hm)
  have z1 : ∀ r, r ∉ Set.Icc δ R → χ1 r = 0 := fun r hm => by simp [hχ1, hR r hm]
  have z2 : ∀ r, r ∉ Set.Icc δ R → χ2 r = 0 := fun r hm => by simp [hχ2, hR r hm]
  obtain ⟨B1, hB1⟩ := bdd_of_csupp s1.continuous c1
  obtain ⟨B2, hB2⟩ := bdd_of_csupp s2.continuous c2
  obtain ⟨Bt, hBt⟩ := tentFn_bound hac hcb
  have zs : ∀ z, z ∉ Set.Icc (-Z) Z → tentSlope a cz b z = 0 := fun z hz => (tent_out hac hcb (hab z hz)).1
  have zt : ∀ z, z ∉ Set.Icc (-Z) Z → tentFn a cz b z = 0 := fun z hz => (tent_out hac hcb (hab z hz)).2
  have hFr := h.2.1 δ R Z hδ
  have hFF := quad_F h δ R Z hδ
  have i1 := int_region measurableSet_Icc measurableSet_Icc hFF.1 s1.continuous.measurable
    (tentSlope_meas a cz b) hB1 (tentSlope_bound a cz b) z1 zs
  have i2 := int_region measurableSet_Icc measurableSet_Icc hFF.2 s1.continuous.measurable
    (tent_cont a cz b).measurable hB1 hBt z1 zt
  have i3 := int_region measurableSet_Icc measurableSet_Icc hFr.1 s2.continuous.measurable
    (tentSlope_meas a cz b) hB2 (tentSlope_bound a cz b) z2 zs
  have i4 := int_region measurableSet_Icc measurableSet_Icc hFr.2 s2.continuous.measurable
    (tent_cont a cz b).measurable hB2 hBt z2 zt
  have k1 := height_core (fun δ R Z hδ => (quad_F h δ R Z hδ).1) (fun δ R Z hδ => (quad_F h δ R Z hδ).2)
    (fun ψ a1 a2 a3 => (h.2.2 ψ a1 a2 a3).2.1) hac hcb s1 c1 p1
  have k2 := height_core (fun δ R Z hδ => (h.2.1 δ R Z hδ).1) (fun δ R Z hδ => (h.2.1 δ R Z hδ).2)
    (fun ψ a1 a2 a3 => (h.2.2 ψ a1 a2 a3).2.2.2) hac hcb s2 c2 p2
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have e : (fun p : ℝ × ℝ => (χ p.1 : ℂ) * Φ p) = fun p =>
        (((χ1 p.1 * tentSlope a cz b p.2 : ℝ) : ℂ) * F p + ((χ1 p.1 * tentFn a cz b p.2 : ℝ) : ℂ) * Fz p) +
        (((χ2 p.1 * tentSlope a cz b p.2 : ℝ) : ℂ) * Fr p + ((χ2 p.1 * tentFn a cz b p.2 : ℝ) : ℂ) * Frz p) := by
      funext p; simp only [hΦ, hχ1, hχ2]; push_cast; ring
    have j1 : Integrable (fun p : ℝ × ℝ => ((χ1 p.1 * tentSlope a cz b p.2 : ℝ) : ℂ) * F p
        + ((χ1 p.1 * tentFn a cz b p.2 : ℝ) : ℂ) * Fz p) := i1.add i2
    have j2 : Integrable (fun p : ℝ × ℝ => ((χ2 p.1 * tentSlope a cz b p.2 : ℝ) : ℂ) * Fr p
        + ((χ2 p.1 * tentFn a cz b p.2 : ℝ) : ℂ) * Frz p) := i3.add i4
    rw [e, integral_add j1 j2, integral_add i1 i2, integral_add i3 i4, k1, k2]
    ring
  · intro p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Set.Icc lo hi ∧ p.2 ∈ Set.Icc a b) from hp) with hh | hh
    · simp [image_eq_zero_of_notMem_tsupport (fun hm => hh (Set.Ioo_subset_Icc_self (hχt hm)))]
    · have ho := tent_out hac hcb hh
      simp [hΦ, ho.1, ho.2]

private theorem radial_pos {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz)
    {cr a b cz oz : ℝ} (ha : 0 < a) (hac : a < cr) (hcb : cr < b) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc (min cz oz) (max cz oz),
      cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p = 0 := by
  set lo := min cz oz
  set hi := max cz oz
  have hmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc lo hi) := measurableSet_Icc.prod measurableSet_Icc
  set Φ : ℝ × ℝ → ℂ := fun p =>
    ((tentSlope a cr b p.1 : ℝ) : ℂ) * ((((1 / (cz - oz)) : ℝ) : ℂ) * F p + (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p)
    + ((tentFn a cr b p.1 : ℝ) : ℂ) *
      ((((1 / (cz - oz)) : ℝ) : ℂ) * Fr p + (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p) with hΦ
  have heq : Set.EqOn (fun p => cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p) Φ
      (Set.Icc a b ×ˢ Set.Icc lo hi) := by
    intro p hp
    have hr := hp.1
    simp only [cornerTerm, hΦ]
    rw [tent_eq_on hac hcb hr]
    unfold tentSlope
    rw [if_pos hr]
    ring
  by_cases hI : IntegrableOn (fun p => cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p)
      (Set.Icc a b ×ˢ Set.Icc lo hi)
  swap
  · exact integral_undef hI
  rw [setIntegral_congr_fun hmeas heq]
  have hIp : Integrable Φ ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc lo hi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hI.congr_fun heq hmeas
  have hsw : ∫ p in Set.Icc a b ×ˢ Set.Icc lo hi, Φ p = ∫ q in Set.Icc lo hi ×ˢ Set.Icc a b, Φ q.swap := by
    rw [Measure.volume_eq_prod]; exact (setIntegral_prod_swap _ _ Φ).symm
  rw [hsw]
  have hIs : IntegrableOn (fun q : ℝ × ℝ => Φ q.swap) (Set.Icc lo hi ×ˢ Set.Icc a b) := by
    have := hIp.swap
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at this
    exact this
  refine slice_zero hIs ?_
  intro χ hχs hχc hχt
  obtain ⟨Z, hZ⟩ := sym_bound hχc
  set χ1 : ℝ → ℝ := fun z => (1 / (cz - oz)) * χ z with hχ1
  set χ2 : ℝ → ℝ := fun z => ((z - oz) / (cz - oz)) * χ z with hχ2
  have s1 : ContDiff ℝ ∞ χ1 := contDiff_const.mul hχs
  have s2 : ContDiff ℝ ∞ χ2 := ((contDiff_id.sub contDiff_const).div_const _).mul hχs
  have c1 : HasCompactSupport χ1 := hχc.mul_left
  have c2 : HasCompactSupport χ2 := hχc.mul_left
  have z1 : ∀ z, z ∉ Set.Icc (-Z) Z → χ1 z = 0 := fun z hm => by simp [hχ1, hZ z hm]
  have z2 : ∀ z, z ∉ Set.Icc (-Z) Z → χ2 z = 0 := fun z hm => by simp [hχ2, hZ z hm]
  obtain ⟨B1, hB1⟩ := bdd_of_csupp s1.continuous c1
  obtain ⟨B2, hB2⟩ := bdd_of_csupp s2.continuous c2
  obtain ⟨Bt, hBt⟩ := tentFn_bound hac hcb
  have zs : ∀ r, r ∉ Set.Icc a b → tentSlope a cr b r = 0 := fun r hm => (tent_out hac hcb hm).1
  have zt : ∀ r, r ∉ Set.Icc a b → tentFn a cr b r = 0 := fun r hm => (tent_out hac hcb hm).2
  have hFr := h.2.1 a b Z ha
  have hFF := quad_F h a b Z ha
  have i1 := int_region measurableSet_Icc measurableSet_Icc hFF.1 (tentSlope_meas a cr b)
    s1.continuous.measurable (tentSlope_bound a cr b) hB1 zs z1
  have i2 := int_region measurableSet_Icc measurableSet_Icc hFr.1 (tent_cont a cr b).measurable
    s1.continuous.measurable hBt hB1 zt z1
  have i3 := int_region measurableSet_Icc measurableSet_Icc hFF.2 (tentSlope_meas a cr b)
    s2.continuous.measurable (tentSlope_bound a cr b) hB2 zs z2
  have i4 := int_region measurableSet_Icc measurableSet_Icc hFr.2 (tent_cont a cr b).measurable
    s2.continuous.measurable hBt hB2 zt z2
  have k1 := radial_core (fun δ R Z hδ => (quad_F h δ R Z hδ).1) (fun δ R Z hδ => (h.2.1 δ R Z hδ).1)
    (fun ψ a1 a2 a3 => (h.2.2 ψ a1 a2 a3).1) ha hac hcb s1 c1
  have k2 := radial_core (fun δ R Z hδ => (quad_F h δ R Z hδ).2) (fun δ R Z hδ => (h.2.1 δ R Z hδ).2)
    (fun ψ a1 a2 a3 => (h.2.2 ψ a1 a2 a3).2.2.1) ha hac hcb s2 c2
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have e : ∫ q : ℝ × ℝ, (χ q.1 : ℂ) * Φ q.swap = ∫ p : ℝ × ℝ, (χ p.2 : ℂ) * Φ p := by
      rw [Measure.volume_eq_prod]; exact integral_prod_swap (fun p : ℝ × ℝ => (χ p.2 : ℂ) * Φ p)
    rw [e]
    have e2 : (fun p : ℝ × ℝ => (χ p.2 : ℂ) * Φ p) = fun p =>
        (((tentSlope a cr b p.1 * χ1 p.2 : ℝ) : ℂ) * F p + ((tentFn a cr b p.1 * χ1 p.2 : ℝ) : ℂ) * Fr p) +
        (((tentSlope a cr b p.1 * χ2 p.2 : ℝ) : ℂ) * Fz p + ((tentFn a cr b p.1 * χ2 p.2 : ℝ) : ℂ) * Frz p) := by
      funext p; simp only [hΦ, hχ1, hχ2]; push_cast; ring
    have j1 : Integrable (fun p : ℝ × ℝ => ((tentSlope a cr b p.1 * χ1 p.2 : ℝ) : ℂ) * F p
        + ((tentFn a cr b p.1 * χ1 p.2 : ℝ) : ℂ) * Fr p) := i1.add i2
    have j2 : Integrable (fun p : ℝ × ℝ => ((tentSlope a cr b p.1 * χ2 p.2 : ℝ) : ℂ) * Fz p
        + ((tentFn a cr b p.1 * χ2 p.2 : ℝ) : ℂ) * Frz p) := i3.add i4
    rw [e2, integral_add j1 j2, integral_add i1 i2, integral_add i3 i4, k1, k2]
    ring
  · intro q hq
    rcases not_and_or.1 (show ¬ (q.1 ∈ Set.Icc lo hi ∧ q.2 ∈ Set.Icc a b) from hq) with hh | hh
    · simp [image_eq_zero_of_notMem_tsupport (fun hm => hh (Set.Ioo_subset_Icc_self (hχt hm)))]
    · have ho := tent_out hac hcb hh
      simp [hΦ, ho.1, ho.2]

private lemma corner_aesm {F Fr Fz Frz : ℝ × ℝ → ℂ} {S : Set (ℝ × ℝ)} {cr cz oz : ℝ} {o : ℝ × ℝ → ℝ}
    (ho : Measurable o) (h1 : AEStronglyMeasurable F (volume.restrict S))
    (h2 : AEStronglyMeasurable Fr (volume.restrict S)) (h3 : AEStronglyMeasurable Fz (volume.restrict S))
    (h4 : AEStronglyMeasurable Frz (volume.restrict S)) :
    AEStronglyMeasurable (fun p => cornerTerm cr (o p) cz oz F Fr Fz Frz p) (volume.restrict S) := by
  have m1 : Measurable (fun p : ℝ × ℝ => (((1 / (cr - o p)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_const.div (measurable_const.sub ho))
  have m2 : Measurable (fun p : ℝ × ℝ => ((((p.1 - o p) / (cr - o p)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_fst.sub ho).div (measurable_const.sub ho))
  have m3 : Measurable (fun p : ℝ × ℝ => ((((p.2 - oz) / (cz - oz)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_snd.sub measurable_const).div measurable_const)
  have m4 : Measurable (fun _ : ℝ × ℝ => (((1 / (cz - oz)) : ℝ) : ℂ)) := measurable_const
  unfold cornerTerm
  exact (((m1.aestronglyMeasurable.mul m4.aestronglyMeasurable).mul h1).add
    ((m1.aestronglyMeasurable.mul m3.aestronglyMeasurable).mul h3)).add
    ((m2.aestronglyMeasurable.mul m4.aestronglyMeasurable).mul h2) |>.add
    ((m2.aestronglyMeasurable.mul m3.aestronglyMeasurable).mul h4)

private theorem radial_zero {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz)
    {cr b cz oz : ℝ} (hcr : 0 < cr) (hcb : cr < b) :
    ∫ p in Set.Icc 0 b ×ˢ Set.Icc (min cz oz) (max cz oz),
      cornerTerm cr (if p.1 ≤ cr then 0 else b) cz oz F Fr Fz Frz p = 0 := by
  set T := Set.Icc (min cz oz) (max cz oz)
  set g : ℝ → ℝ × ℝ → ℂ := fun a p => cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p with hg
  show ∫ p in Set.Icc 0 b ×ˢ T, g 0 p = 0
  set S0 := Set.Icc (0 : ℝ) b ×ˢ T
  have hS0 : MeasurableSet S0 := measurableSet_Icc.prod measurableSet_Icc
  by_cases hI : IntegrableOn (g 0) S0
  swap
  · exact integral_undef hI
  set an : ℕ → ℝ := fun n => cr / ((n : ℝ) + 2) with han
  have han_pos : ∀ n, 0 < an n := fun n => by simp only [han]; positivity
  have han_le : ∀ n, an n ≤ cr / 2 := fun n => by
    simp only [han]
    exact div_le_div_of_nonneg_left hcr.le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
  have han_t : Tendsto an atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hz : ∀ n, ∫ p in Set.Icc (an n) b ×ˢ T, g (an n) p = 0 := fun n =>
    radial_pos h (han_pos n) (by linarith [han_le n]) hcb
  set Z := |cz| + |oz|
  have hTZ : T ⊆ Set.Icc (-Z) Z := by
    intro z hm
    have h1 := hm.1
    have h2 := hm.2
    constructor
    · have : -Z ≤ min cz oz := le_min (by linarith [neg_abs_le cz, abs_nonneg oz])
        (by linarith [neg_abs_le oz, abs_nonneg cz])
      linarith
    · have : max cz oz ≤ Z := max_le (by linarith [le_abs_self cz, abs_nonneg oz])
        (by linarith [le_abs_self oz, abs_nonneg cz])
      linarith
  have hsub : S0 ⊆ Set.Icc 0 b ×ˢ Set.Icc (-Z) Z := Set.prod_mono le_rfl hTZ
  set W := |1 / (cz - oz)|
  set M := 2 / cr * (W + 1)
  have hM : 0 ≤ M := by positivity
  set bound : ℝ × ℝ → ℝ := S0.indicator (fun p => M * (‖F p‖ + ‖Fz p‖ + ‖(p.1 : ℂ) * Fr p‖
    + ‖(p.1 : ℂ) * Frz p‖) + ‖g 0 p‖)
  have hq := h.1 b Z
  have hbi : Integrable bound := by
    refine (integrable_indicator_iff hS0).2 ?_
    refine Integrable.add (Integrable.const_mul ?_ M) hI.norm
    exact (((hq.1.mono_set hsub).norm.add (hq.2.1.mono_set hsub).norm).add
      (hq.2.2.1.mono_set hsub).norm).add (hq.2.2.2.mono_set hsub).norm
  have hreg : ∀ n, MeasurableSet (Set.Icc (an n) b ×ˢ T) := fun n => measurableSet_Icc.prod measurableSet_Icc
  have hregsub : ∀ n, Set.Icc (an n) b ×ˢ T ⊆ Set.Icc (an n) b ×ˢ Set.Icc (-Z) Z := fun n =>
    Set.prod_mono le_rfl hTZ
  have L := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun n => (Set.Icc (an n) b ×ˢ T).indicator (g (an n))) (f := S0.indicator (g 0)) bound ?_ ?_ hbi ?_
  · have e1 : ∀ n, ∫ p, (Set.Icc (an n) b ×ˢ T).indicator (g (an n)) p = 0 := fun n => by
      rw [integral_indicator (hreg n)]; exact hz n
    simp only [e1] at L
    rw [integral_indicator hS0] at L
    exact tendsto_nhds_unique tendsto_const_nhds L |>.symm
  · refine Eventually.of_forall fun n => (aestronglyMeasurable_indicator_iff (hreg n)).2 ?_
    have hq1 := quad_F h (an n) b Z (han_pos n)
    have hq2 := h.2.1 (an n) b Z (han_pos n)
    exact corner_aesm (Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const
        measurable_const)
      (hq1.1.mono_set (hregsub n)).aestronglyMeasurable (hq2.1.mono_set (hregsub n)).aestronglyMeasurable
      (hq1.2.mono_set (hregsub n)).aestronglyMeasurable (hq2.2.mono_set (hregsub n)).aestronglyMeasurable
  · refine Eventually.of_forall fun n => Eventually.of_forall fun p => ?_
    have hbnn : 0 ≤ bound p := Set.indicator_nonneg (fun _ _ => by positivity) _
    by_cases hp : p ∈ Set.Icc (an n) b ×ˢ T
    · have hp0 : p ∈ S0 := ⟨⟨(han_pos n).le.trans hp.1.1, hp.1.2⟩, hp.2⟩
      rw [Set.indicator_of_mem hp]
      simp only [bound]
      rw [Set.indicator_of_mem hp0]
      by_cases hc : p.1 ≤ cr
      · refine le_add_of_le_of_nonneg ?_ (norm_nonneg _)
        simp only [hg, if_pos hc, cornerTerm]
        set a := an n
        have ha0 := han_pos n
        have hale := han_le n
        have hp1 : a ≤ p.1 := hp.1.1
        have hcra : cr / 2 ≤ cr - a := by linarith
        have hcra0 : 0 < cr - a := by linarith
        have b1 : |1 / (cr - a)| ≤ 2 / cr := by
          rw [abs_of_pos (by positivity), div_le_div_iff₀ hcra0 hcr]; linarith
        have b3 : |(p.1 - a) / (cr - a)| ≤ 2 / cr * |p.1| := by
          rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1 - a), abs_of_pos hcra0,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1), div_le_iff₀ hcra0]
          have : 2 / cr * p.1 * (cr - a) ≥ 2 / cr * p.1 * (cr / 2) :=
            mul_le_mul_of_nonneg_left hcra (mul_nonneg (by positivity) (by linarith))
          have e : 2 / cr * p.1 * (cr / 2) = p.1 := by field_simp
          linarith
        have b2 : |(p.2 - oz) / (cz - oz)| ≤ 1 := by
          by_cases hzo : cz = oz
          · simp [hzo]
          · rw [abs_div, div_le_one (abs_pos.2 (sub_ne_zero.2 hzo))]
            have t1 := hp.2.1
            have t2 := hp.2.2
            rcases le_total cz oz with hh | hh
            · rw [min_eq_left hh] at t1; rw [max_eq_right hh] at t2
              rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
            · rw [min_eq_right hh] at t1; rw [max_eq_left hh] at t2
              rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
        have hW : W ≤ W + 1 := by linarith
        have hW0 : 0 ≤ W := abs_nonneg _
        have n1 : ‖(((1 / (cr - a) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p‖ ≤ M * ‖F p‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (mul_le_mul b1 hW (abs_nonneg _) (by positivity)) (norm_nonneg _)
        have n2 : ‖(((1 / (cr - a) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p‖ ≤ M * ‖Fz p‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (mul_le_mul b1 (b2.trans (by linarith : (1 : ℝ) ≤ W + 1)) (abs_nonneg _) (by positivity))
            (norm_nonneg _)
        have n3 : ‖(((p.1 - a) / (cr - a) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * Fr p‖
            ≤ M * ‖(p.1 : ℂ) * Fr p‖ := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
          have := mul_le_mul_of_nonneg_right (mul_le_mul b3 hW (abs_nonneg _) (by positivity)) (norm_nonneg (Fr p))
          calc _ ≤ 2 / cr * |p.1| * (W + 1) * ‖Fr p‖ := this
            _ = M * (|p.1| * ‖Fr p‖) := by ring
        have n4 : ‖(((p.1 - a) / (cr - a) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p‖
            ≤ M * ‖(p.1 : ℂ) * Frz p‖ := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
          have := mul_le_mul_of_nonneg_right (mul_le_mul b3 (b2.trans (by linarith : (1 : ℝ) ≤ W + 1)) (abs_nonneg _)
            (by positivity)) (norm_nonneg (Frz p))
          calc _ ≤ 2 / cr * |p.1| * (W + 1) * ‖Frz p‖ := this
            _ = M * (|p.1| * ‖Frz p‖) := by ring
        calc _ ≤ ‖(((1 / (cr - a) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p‖
              + ‖(((1 / (cr - a) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p‖
              + ‖(((p.1 - a) / (cr - a) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * Fr p‖
              + ‖(((p.1 - a) / (cr - a) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p‖ :=
              norm_add₄_le
          _ ≤ M * ‖F p‖ + M * ‖Fz p‖ + M * ‖(p.1 : ℂ) * Fr p‖ + M * ‖(p.1 : ℂ) * Frz p‖ := by linarith
          _ = _ := by ring
      · have e : g (an n) p = g 0 p := by simp only [hg, if_neg hc]
        rw [e]
        have : 0 ≤ M * (‖F p‖ + ‖Fz p‖ + ‖(p.1 : ℂ) * Fr p‖ + ‖(p.1 : ℂ) * Frz p‖) := by positivity
        linarith
    · rw [Set.indicator_of_notMem hp, norm_zero]; exact hbnn
  · filter_upwards [ae_fst_ne 0] with p hp0
    by_cases hS : p ∈ S0
    · have hpos : 0 < p.1 := lt_of_le_of_ne hS.1.1 (Ne.symm hp0)
      have hev : ∀ᶠ n in atTop, an n < p.1 := han_t.eventually (gt_mem_nhds hpos)
      rw [Set.indicator_of_mem hS]
      by_cases hc : p.1 ≤ cr
      · have c1 : ContinuousAt (fun o : ℝ => (((1 / (cr - o)) : ℝ) : ℂ)) 0 :=
          Complex.continuous_ofReal.continuousAt.comp
            (continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by simp; linarith))
        have c2 : ContinuousAt (fun o : ℝ => ((((p.1 - o) / (cr - o)) : ℝ) : ℂ)) 0 :=
          Complex.continuous_ofReal.continuousAt.comp
            ((continuousAt_const.sub continuousAt_id).div (continuousAt_const.sub continuousAt_id)
              (by simp; linarith))
        have cΨ : ContinuousAt (fun o => cornerTerm cr o cz oz F Fr Fz Frz p) 0 := by
          unfold cornerTerm
          exact ((((c1.mul continuousAt_const).mul continuousAt_const).add
            ((c1.mul continuousAt_const).mul continuousAt_const)).add
            ((c2.mul continuousAt_const).mul continuousAt_const)).add
            ((c2.mul continuousAt_const).mul continuousAt_const)
        have t := cΨ.tendsto.comp han_t
        have e0 : g 0 p = cornerTerm cr 0 cz oz F Fr Fz Frz p := by simp only [hg, if_pos hc]
        rw [e0]
        refine t.congr' ?_
        filter_upwards [hev] with n hn
        have hm : p ∈ Set.Icc (an n) b ×ˢ T := ⟨⟨hn.le, hS.1.2⟩, hS.2⟩
        rw [Set.indicator_of_mem hm]
        simp only [Function.comp, hg, if_pos hc]
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        have hm : p ∈ Set.Icc (an n) b ×ˢ T := ⟨⟨hn.le, hS.1.2⟩, hS.2⟩
        rw [Set.indicator_of_mem hm]
        simp only [hg, if_neg hc]
    · rw [Set.indicator_of_notMem hS]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      have : p ∉ Set.Icc (an n) b ×ˢ T := fun hm =>
        hS ⟨⟨(han_pos n).le.trans hm.1.1, hm.1.2⟩, hm.2⟩
      exact (Set.indicator_of_notMem this _).symm

theorem radial_tent_zero {F Fr Fz Frz : ℝ × ℝ → ℂ} (h : IsMixedWeakQuad F Fr Fz Frz)
    {cr a b cz oz : ℝ} (ha : 0 ≤ a) (hac : a < cr) (hcb : cr < b) (hz : oz ≠ cz) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc (min cz oz) (max cz oz),
      cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p = 0 := by
  rcases ha.lt_or_eq with ha' | ha'
  · exact radial_pos h ha' hac hcb
  · subst ha'
    exact radial_zero h hac hcb

end Breakdown.CellCert.CellFormula
