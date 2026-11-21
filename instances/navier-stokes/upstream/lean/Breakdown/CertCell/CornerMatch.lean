import Breakdown.CertCell.BridgeStatements
import Breakdown.FracCell.CornerIndependenceParts

open scoped ContDiff
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.CertCell.Bridge

open Breakdown.FracInternal.CornerParts

private def tentCombination (cr orr h : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (((1 / (cr - orr) : ℝ)) : ℂ) * ((tentSlope (-h) 0 h p.2 : ℝ) : ℂ) * F p
    + (((1 / (cr - orr) : ℝ)) : ℂ) * ((tentFn (-h) 0 h p.2 : ℝ) : ℂ) * Fz p
    + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * ((tentSlope (-h) 0 h p.2 : ℝ) : ℂ) * Fr p
    + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * ((tentFn (-h) 0 h p.2 : ℝ) : ℂ) * Frz p

private theorem height_identity_full {G Gz : ℝ × ℝ → ℂ} {R : Set (ℝ × ℝ)} {ψ : ℝ × ℝ → ℝ}
    (ht : tsupport ψ ⊆ interior R)
    (hw : ∫ p in R, G p * Complex.ofReal (fderiv ℝ ψ p (0, 1)) = -∫ p in R, Gz p * Complex.ofReal (ψ p)) :
    ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * G p = -∫ p, (ψ p : ℂ) * Gz p := by
  have hout : ∀ p, p ∉ R → p ∉ tsupport ψ := fun p hp hm => hp (interior_subset (ht hm))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      rw [fderiv_of_notMem_tsupport ℝ (hout p hp)]; simp),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      rw [image_eq_zero_of_notMem_tsupport (hout p hp)]; simp)] at hw
  simpa only [mul_comm] using hw

private theorem integrableOn_weight_tent {H : ℝ × ℝ → ℂ} {lo hi Z : ℝ}
    (hH : IntegrableOn H (Icc lo hi ×ˢ Icc (-Z) Z)) {u v : ℝ → ℝ} (hu : Continuous u)
    (hv : Measurable v) {Cv : ℝ} (hbv : ∀ x, |v x| ≤ Cv) :
    IntegrableOn (fun p => (u p.1 : ℂ) * (v p.2 : ℂ) * H p) (Icc lo hi ×ˢ Icc (-Z) Z) := by
  obtain ⟨Cu, hCu⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn hu.continuousOn
  refine Integrable.bdd_mul (c := Cu * Cv) hH ?_ ?_
  · exact ((Complex.measurable_ofReal.comp (hu.measurable.comp measurable_fst)).mul
      (Complex.measurable_ofReal.comp (hv.comp measurable_snd))).aestronglyMeasurable
  · refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 (Eventually.of_forall fun p hp => ?_)
    have h1 := hCu p.1 hp.1
    rw [Real.norm_eq_abs] at h1
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul h1 (hbv _) (abs_nonneg _) ((abs_nonneg _).trans h1)

private theorem tentSlope_upper {h z : ℝ} (hz : z ∈ Ioc 0 h) : tentSlope (-h) 0 h z = 1 / (0 - h) := by
  unfold tentSlope
  rw [if_pos ⟨by linarith [hz.1, hz.2], hz.2⟩, if_neg (not_le.2 hz.1)]

private theorem tentFn_upper {h z : ℝ} (hh : 0 < h) (hz : z ∈ Ioc 0 h) :
    tentFn (-h) 0 h z = (z - h) / (0 - h) := by
  rw [tent_eq_on (by linarith) hh ⟨by linarith [hz.1], hz.2⟩, if_neg (not_le.2 hz.1)]

private theorem tentSlope_lower {h z : ℝ} (hz : z ∈ Icc (-h) 0) : tentSlope (-h) 0 h z = 1 / (0 - -h) := by
  unfold tentSlope
  rw [if_pos ⟨hz.1, by linarith [hz.1, hz.2]⟩, if_pos hz.2]

private theorem tentFn_lower {h z : ℝ} (hh : 0 < h) (hz : z ∈ Icc (-h) 0) :
    tentFn (-h) 0 h z = (z - -h) / (0 - -h) := by
  rw [tent_eq_on (by linarith) hh ⟨hz.1, by linarith [hz.2]⟩, if_pos hz.2]

private theorem tent_height_identity {G Gz : ℝ × ℝ → ℂ} {lo hi Z : ℝ}
    (hG : IntegrableOn G (Icc lo hi ×ˢ Icc (-Z) Z)) (hGz : IntegrableOn Gz (Icc lo hi ×ˢ Icc (-Z) Z))
    (hw : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo lo hi ×ˢ Ioo (-Z) Z →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * G p = -∫ p, (ψ p : ℂ) * Gz p)
    {a c b : ℝ} (hac : a < c) (hcb : c < b) (ha : -Z < a) (hb : b < Z)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχt : tsupport χ ⊆ Ioo lo hi) :
    ∫ p, ((χ p.1 * tentSlope a c b p.2 : ℝ) : ℂ) * G p
      = -∫ p, ((χ p.1 * tentFn a c b p.2 : ℝ) : ℂ) * Gz p := by
  obtain ⟨K, hK⟩ := tent_slope a c b
  obtain ⟨Cχ, hCχ⟩ := hχc.exists_bound_of_continuous hχ.continuous
  have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ 0)
  have hχz : ∀ r, r ∉ Icc lo hi → χ r = 0 := fun r hr =>
    image_eq_zero_of_notMem_tsupport fun hm => hr (Ioo_subset_Icc_self (hχt hm))
  have hε : 0 < min (a + Z) (Z - b) / 2 := by
    have := lt_min (show 0 < a + Z by linarith) (show 0 < Z - b by linarith); linarith
  have hε1 : min (a + Z) (Z - b) / 2 < a + Z := by
    have := min_le_left (a + Z) (Z - b); linarith
  have hε2 : min (a + Z) (Z - b) / 2 < Z - b := by
    have := min_le_right (a + Z) (Z - b); linarith
  have hev := small_eventually hε
  refine limit_core (measurableSet_Icc.prod measurableSet_Icc) hG hGz
    (fun n p => χ p.1 * deriv (mollTent a c b n) p.2) (fun n p => χ p.1 * mollTent a c b n p.2)
    (fun p => χ p.1 * tentSlope a c b p.2) (fun p => χ p.1 * tentFn a c b p.2)
    (Cχ * max (K : ℝ) (K * (b - a + 2))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n
    exact (hχ.continuous.comp continuous_fst).mul
      (((moll_smooth a c b n).continuous_deriv (by simp)).comp continuous_snd)
  · intro n
    exact (hχ.continuous.comp continuous_fst).mul ((moll_smooth a c b n).continuous.comp continuous_snd)
  · filter_upwards [hev] with n hn p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc lo hi ∧ p.2 ∈ Icc (-Z) Z) from hp) with h | h
    · simp [hχz _ h]
    · have hv := moll_vanish a c b hac hcb n p.2 fun hm => h ⟨by linarith [hm.1], by linarith [hm.2]⟩
      simp [hv.1, hv.2]
  · intro p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc lo hi ∧ p.2 ∈ Icc (-Z) Z) from hp) with h | h
    · simp [hχz _ h]
    · have ht := tent_out (x := p.2) hac hcb fun hm => h ⟨by linarith [hm.1], by linarith [hm.2]⟩
      simp [ht.1, ht.2]
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
  · filter_upwards [hev] with n hn
    have hsm : ContDiff ℝ ∞ (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) :=
      (hχ.comp contDiff_fst).mul ((moll_smooth a c b n).comp contDiff_snd)
    have hcs : HasCompactSupport (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) := by
      refine HasCompactSupport.intro (hχc.isCompact.prod (moll_hasCompactSupport hac hcb n).isCompact) ?_
      intro q hq
      rcases not_and_or.1 (show ¬ (q.1 ∈ tsupport χ ∧ q.2 ∈ tsupport (mollTent a c b n)) from hq) with h | h
      · simp [image_eq_zero_of_notMem_tsupport h]
      · simp [image_eq_zero_of_notMem_tsupport h]
    have hsub : tsupport (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) ⊆ Ioo lo hi ×ˢ Ioo (-Z) Z := by
      have h1 : tsupport (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) ⊆
          tsupport χ ×ˢ Icc (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1)) := by
        refine closure_minimal ?_ ((isClosed_tsupport χ).prod isClosed_Icc)
        intro q hq
        have hq' : χ q.1 * mollTent a c b n q.2 ≠ 0 := hq
        refine ⟨subset_tsupport _ (left_ne_zero_of_mul hq'), ?_⟩
        by_contra hm
        exact right_ne_zero_of_mul hq' (moll_vanish a c b hac hcb n q.2 hm).1
      intro q hq
      have hq1 := h1 hq
      exact ⟨hχt hq1.1, by linarith [hq1.2.1], by linarith [hq1.2.2]⟩
    have hfd := fun q => fderiv_prod_apply (hχ.differentiable (by simp))
      ((moll_smooth a c b n).differentiable (by simp)) q
    have := hw _ hsm hcs hsub
    simp only [(hfd _).2] at this
    exact this

private theorem tent_weight_zero {G Gz : ℝ × ℝ → ℂ} {lo hi h : ℝ} (hh : 0 < h)
    (hG : IntegrableOn G (Icc lo hi ×ˢ Icc (-(2 * h)) (2 * h)))
    (hGz : IntegrableOn Gz (Icc lo hi ×ˢ Icc (-(2 * h)) (2 * h)))
    (hw : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo lo hi ×ˢ Ioo (-(2 * h)) (2 * h) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * G p = -∫ p, (ψ p : ℂ) * Gz p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχt : tsupport χ ⊆ Ioo lo hi) :
    (∫ p, ((χ p.1 * tentSlope (-h) 0 h p.2 : ℝ) : ℂ) * G p)
      + ∫ p, ((χ p.1 * tentFn (-h) 0 h p.2 : ℝ) : ℂ) * Gz p = 0 := by
  rw [tent_height_identity (a := -h) (c := 0) (b := h) hG hGz hw (by linarith) hh (by linarith) (by linarith)
    hχ hχc hχt]
  ring

private theorem tent_combination_test {F Fr Fz Frz : ℝ × ℝ → ℂ} {cr orr h lo hi : ℝ} (hh : 0 < h)
    (iF : IntegrableOn F (Icc lo hi ×ˢ Icc (-(2 * h)) (2 * h)))
    (iFr : IntegrableOn Fr (Icc lo hi ×ˢ Icc (-(2 * h)) (2 * h)))
    (iFz : IntegrableOn Fz (Icc lo hi ×ˢ Icc (-(2 * h)) (2 * h)))
    (iFrz : IntegrableOn Frz (Icc lo hi ×ˢ Icc (-(2 * h)) (2 * h)))
    (wF : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo lo hi ×ˢ Ioo (-(2 * h)) (2 * h) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * Fz p)
    (wFr : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo lo hi ×ˢ Ioo (-(2 * h)) (2 * h) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * Fr p = -∫ p, (ψ p : ℂ) * Frz p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχt : tsupport χ ⊆ Ioo lo hi) :
    ∫ p, (χ p.1 : ℂ) * tentCombination cr orr h F Fr Fz Frz p = 0 := by
  have hw1 : ContDiff ℝ ∞ (fun r => χ r * (1 / (cr - orr))) := hχ.mul contDiff_const
  have hw2 : ContDiff ℝ ∞ (fun r => χ r * ((r - orr) / (cr - orr))) :=
    hχ.mul ((contDiff_id.sub contDiff_const).div_const _)
  have hc1 : HasCompactSupport (fun r => χ r * (1 / (cr - orr))) := hχc.mul_right
  have hc2 : HasCompactSupport (fun r => χ r * ((r - orr) / (cr - orr))) := hχc.mul_right
  have ht1 : tsupport (fun r => χ r * (1 / (cr - orr))) ⊆ Ioo lo hi := tsupport_mul_subset_left.trans hχt
  have ht2 : tsupport (fun r => χ r * ((r - orr) / (cr - orr))) ⊆ Ioo lo hi :=
    tsupport_mul_subset_left.trans hχt
  have z1 := tent_weight_zero hh iF iFz wF hw1 hc1 ht1
  have z2 := tent_weight_zero hh iFr iFrz wFr hw2 hc2 ht2
  obtain ⟨C1, hC1⟩ := bdd_of_csupp hw1.continuous hc1
  obtain ⟨C2, hC2⟩ := bdd_of_csupp hw2.continuous hc2
  obtain ⟨Ct, hCt⟩ := tentFn_bound (show -h < 0 by linarith) hh
  have hχz : ∀ r, r ∉ Icc lo hi → χ r = 0 := fun r hr =>
    image_eq_zero_of_notMem_tsupport fun hm => hr (Ioo_subset_Icc_self (hχt hm))
  have zu1 : ∀ r, r ∉ Icc lo hi → χ r * (1 / (cr - orr)) = 0 := fun r hr => by rw [hχz r hr, zero_mul]
  have zu2 : ∀ r, r ∉ Icc lo hi → χ r * ((r - orr) / (cr - orr)) = 0 := fun r hr => by
    rw [hχz r hr, zero_mul]
  have zout : ∀ z, z ∉ Icc (-(2 * h)) (2 * h) → z ∉ Icc (-h) h := fun z hz hm =>
    hz ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have zs : ∀ z, z ∉ Icc (-(2 * h)) (2 * h) → tentSlope (-h) 0 h z = 0 := fun z hz =>
    (tent_out (show -h < 0 by linarith) hh (zout z hz)).1
  have zt : ∀ z, z ∉ Icc (-(2 * h)) (2 * h) → tentFn (-h) 0 h z = 0 := fun z hz =>
    (tent_out (show -h < 0 by linarith) hh (zout z hz)).2
  have i1 := int_region measurableSet_Icc measurableSet_Icc iF hw1.continuous.measurable
    (tentSlope_meas _ _ _) hC1 (tentSlope_bound (-h) 0 h) zu1 zs
  have i2 := int_region measurableSet_Icc measurableSet_Icc iFz hw1.continuous.measurable
    (tent_cont _ _ _).measurable hC1 hCt zu1 zt
  have i3 := int_region measurableSet_Icc measurableSet_Icc iFr hw2.continuous.measurable
    (tentSlope_meas _ _ _) hC2 (tentSlope_bound (-h) 0 h) zu2 zs
  have i4 := int_region measurableSet_Icc measurableSet_Icc iFrz hw2.continuous.measurable
    (tent_cont _ _ _).measurable hC2 hCt zu2 zt
  have e : (fun p : ℝ × ℝ => (χ p.1 : ℂ) * tentCombination cr orr h F Fr Fz Frz p) = fun p =>
      ((χ p.1 * (1 / (cr - orr)) * tentSlope (-h) 0 h p.2 : ℝ) : ℂ) * F p
        + ((χ p.1 * (1 / (cr - orr)) * tentFn (-h) 0 h p.2 : ℝ) : ℂ) * Fz p
        + (((χ p.1 * ((p.1 - orr) / (cr - orr)) * tentSlope (-h) 0 h p.2 : ℝ) : ℂ) * Fr p
          + ((χ p.1 * ((p.1 - orr) / (cr - orr)) * tentFn (-h) 0 h p.2 : ℝ) : ℂ) * Frz p) := by
    funext p
    simp only [tentCombination]
    push_cast
    ring
  rw [e, integral_add ?i12 ?i34, integral_add i1 i2, integral_add i3 i4]
  case i12 => exact i1.add i2
  case i34 => exact i3.add i4
  linear_combination z1 + z2

theorem cornerMatch : CornerMatchHolds := by
  intro F Fr Fz Frz cr orr h lo hi _hne hh hlo hhi hW
  obtain ⟨iF, iFr, iFz, iFrz, hw⟩ := hW
  have hint : ∀ ψ : ℝ × ℝ → ℝ, tsupport ψ ⊆ Ioo lo hi ×ˢ Ioo (-(2 * h)) (2 * h) →
      tsupport ψ ⊆ interior (Icc lo hi ×ˢ Icc (-(2 * h)) (2 * h)) := by
    intro ψ hψ
    rwa [interior_prod_eq, interior_Icc, interior_Icc]
  have wF : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo lo hi ×ˢ Ioo (-(2 * h)) (2 * h) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * Fz p :=
    fun ψ h1 h2 h3 => height_identity_full (hint ψ h3) (hw ψ h1 h2 (hint ψ h3)).2.1
  have wFr : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo lo hi ×ˢ Ioo (-(2 * h)) (2 * h) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * Fr p = -∫ p, (ψ p : ℂ) * Frz p :=
    fun ψ h1 h2 h3 => height_identity_full (hint ψ h3) (hw ψ h1 h2 (hint ψ h3)).2.2
  have hR : IntegrableOn (tentCombination cr orr h F Fr Fz Frz) (Icc lo hi ×ˢ Icc (-(2 * h)) (2 * h)) := by
    have j1 := integrableOn_weight_tent (u := fun _ => 1 / (cr - orr)) iF continuous_const
      (tentSlope_meas (-h) 0 h) (tentSlope_bound (-h) 0 h)
    have j2 := integrableOn_weight_tent (u := fun _ => 1 / (cr - orr)) iFz continuous_const
      (tent_cont (-h) 0 h).measurable (tentFn_bound (show -h < 0 by linarith) hh).choose_spec
    have j3 := integrableOn_weight_tent (u := fun r => (r - orr) / (cr - orr)) iFr (by fun_prop)
      (tentSlope_meas (-h) 0 h) (tentSlope_bound (-h) 0 h)
    have j4 := integrableOn_weight_tent (u := fun r => (r - orr) / (cr - orr)) iFrz (by fun_prop)
      (tent_cont (-h) 0 h).measurable (tentFn_bound (show -h < 0 by linarith) hh).choose_spec
    exact ((j1.add j2).add j3).add j4
  have hsub : Icc (min cr orr) (max cr orr) ×ˢ Icc (-h) h ⊆ Icc lo hi ×ˢ Icc (-(2 * h)) (2 * h) :=
    prod_mono (Icc_subset_Icc hlo.le hhi.le) (Icc_subset_Icc (by linarith) (by linarith))
  have hI := hR.mono_set hsub
  have hzero : ∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc (-h) h, tentCombination cr orr h F Fr Fz Frz p = 0 := by
    refine slice_zero hI (fun χ hχ hχc hχt => ?_)
    have hχt' : tsupport χ ⊆ Ioo lo hi := hχt.trans (Ioo_subset_Ioo hlo.le hhi.le)
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero ?_]
    · exact tent_combination_test hh iF iFr iFz iFrz wF wFr hχ hχc hχt'
    · intro p hp
      rcases not_and_or.1 (show ¬ (p.1 ∈ Icc (min cr orr) (max cr orr) ∧ p.2 ∈ Icc (-h) h) from hp) with h' | h'
      · rw [image_eq_zero_of_notMem_tsupport (fun hm => h' (Ioo_subset_Icc_self (hχt hm)))]
        simp
      · have ht := tent_out (show -h < 0 by linarith) hh h'
        simp [tentCombination, ht.1, ht.2]
  have hsplit : ∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc (-h) h, tentCombination cr orr h F Fr Fz Frz p
      = (∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc (-h) 0, tentCombination cr orr h F Fr Fz Frz p)
        + ∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc 0 h, tentCombination cr orr h F Fr Fz Frz p := by
    rw [← Icc_union_Icc_eq_Icc (show -h ≤ 0 by linarith) hh.le, prod_union] at hI ⊢
    refine setIntegral_union₀ ?_ (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet
      (hI.mono_set subset_union_left) (hI.mono_set subset_union_right)
    refine measure_mono_null (t := (univ : Set ℝ) ×ˢ ({0} : Set ℝ)) ?_ ?_
    · rintro p ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact ⟨trivial, le_antisymm h1.2 h2.1⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
  have hup : CellCert.CellFormula.cornerMoment cr orr 0 h F Fr Fz Frz
      = -(CellCert.CellFormula.edgeSign cr orr *
        ∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc 0 h, tentCombination cr orr h F Fr Fz Frz p) := by
    have e1 : CellCert.CellFormula.edgeSign 0 h = -1 := by
      unfold CellCert.CellFormula.edgeSign
      rw [if_neg (not_lt.2 hh.le)]
    unfold CellCert.CellFormula.cornerMoment
    rw [e1, min_eq_left hh.le, max_eq_right hh.le]
    refine (congrArg (fun x => CellCert.CellFormula.edgeSign cr orr * -1 * x)
      (setIntegral_congr_ae (g := tentCombination cr orr h F Fr Fz Frz)
        (measurableSet_Icc.prod measurableSet_Icc) ?_)).trans (by ring)
    filter_upwards [ae_snd_ne 0] with p hp hmem
    have hz : p.2 ∈ Ioc 0 h := ⟨lt_of_le_of_ne hmem.2.1 (Ne.symm hp), hmem.2.2⟩
    simp only [tentCombination]
    rw [tentSlope_upper hz, tentFn_upper hh hz]
  have hdown : CellCert.CellFormula.cornerMoment cr orr 0 (-h) F Fr Fz Frz
      = CellCert.CellFormula.edgeSign cr orr *
        ∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc (-h) 0, tentCombination cr orr h F Fr Fz Frz p := by
    have e1 : CellCert.CellFormula.edgeSign 0 (-h) = 1 := by
      unfold CellCert.CellFormula.edgeSign
      rw [if_pos (by linarith)]
    unfold CellCert.CellFormula.cornerMoment
    rw [e1, min_eq_right (show -h ≤ 0 by linarith), max_eq_left (show -h ≤ 0 by linarith)]
    refine (congrArg (fun x => CellCert.CellFormula.edgeSign cr orr * 1 * x)
      (setIntegral_congr_fun (g := tentCombination cr orr h F Fr Fz Frz)
        (measurableSet_Icc.prod measurableSet_Icc) fun p hmem => ?_)).trans (by ring)
    have hz : p.2 ∈ Icc (-h) 0 := hmem.2
    simp only [tentCombination]
    rw [tentSlope_lower hz, tentFn_lower hh hz]
  rw [hup, hdown]
  linear_combination (-(CellCert.CellFormula.edgeSign cr orr)) * (hsplit.symm.trans hzero)

end Breakdown.CertCell.Bridge
