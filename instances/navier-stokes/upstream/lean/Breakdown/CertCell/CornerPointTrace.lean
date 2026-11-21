import Breakdown.CertCell.BridgeTraceStatements
import Breakdown.FracCell.CornerIndependenceParts

open scoped ContDiff
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.CertCell.SideTrace

open Breakdown.CellCert.CellFormula Breakdown.FracInternal.CornerParts Breakdown.CertCell.Bridge

namespace Internal

def WeakAlong (G Gd : ℝ × ℝ → ℂ) (v : ℝ × ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∫ p, ((fderiv ℝ ψ p v : ℝ) : ℂ) * G p = -∫ p, (ψ p : ℂ) * Gd p

theorem whole_identity {G Gd : ℝ × ℝ → ℂ} {R : Set (ℝ × ℝ)} {ψ : ℝ × ℝ → ℝ} (v : ℝ × ℝ)
    (ht : tsupport ψ ⊆ interior R)
    (hw : ∫ p in R, G p * Complex.ofReal (fderiv ℝ ψ p v) = -∫ p in R, Gd p * Complex.ofReal (ψ p)) :
    ∫ p, ((fderiv ℝ ψ p v : ℝ) : ℂ) * G p = -∫ p, (ψ p : ℂ) * Gd p := by
  have hout : ∀ p, p ∉ R → p ∉ tsupport ψ := fun p hp hm => hp (interior_subset (ht hm))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      rw [fderiv_of_notMem_tsupport ℝ (hout p hp)]; simp),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      rw [image_eq_zero_of_notMem_tsupport (hout p hp)]; simp)] at hw
  simpa only [mul_comm] using hw

theorem second_swap {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (v w p : ℝ × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ ψ q v) p w = fderiv ℝ (fun q => fderiv ℝ ψ q w) p v := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (m := ∞) le_rfl
  have hdp : DifferentiableAt ℝ (fderiv ℝ ψ) p := hd.differentiable (by simp) p
  rw [fderiv_clm_apply hdp (differentiableAt_const v), fderiv_clm_apply hdp (differentiableAt_const w)]
  simp only [fderiv_const_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add]
  exact ((hψ.contDiffAt (x := p)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top)) w v

theorem mixed_of_three {F Fr Fz Frz : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)}
    (h1 : WeakAlong F Fr (1, 0) U) (h2 : WeakAlong F Fz (0, 1) U) (h3 : WeakAlong Fr Frz (0, 1) U) :
    WeakAlong Fz Frz (1, 0) U := by
  intro ψ hψ hc ht
  have hd : ∀ v : ℝ × ℝ, ContDiff ℝ ∞ (fun q => fderiv ℝ ψ q v) := fun v =>
    (hψ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have a := h2 (fun q => fderiv ℝ ψ q (1, 0)) (hd _) (hc.fderiv_apply (𝕜 := ℝ) _)
    ((tsupport_fderiv_apply_subset ℝ _).trans ht)
  have b := h1 (fun q => fderiv ℝ ψ q (0, 1)) (hd _) (hc.fderiv_apply (𝕜 := ℝ) _)
    ((tsupport_fderiv_apply_subset ℝ _).trans ht)
  have c := h3 ψ hψ hc ht
  simp only [second_swap hψ (1, 0) (0, 1)] at a
  linear_combination a - b + c

theorem radial_tent {G Gd : ℝ × ℝ → ℂ} {lo hi zlo zhi : ℝ}
    (hG : IntegrableOn G (Icc lo hi ×ˢ Icc zlo zhi)) (hGd : IntegrableOn Gd (Icc lo hi ×ˢ Icc zlo zhi))
    (hw : WeakAlong G Gd (1, 0) (Ioo lo hi ×ˢ Ioo zlo zhi))
    {a c b : ℝ} (hac : a < c) (hcb : c < b) (ha : lo < a) (hb : b < hi)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχt : tsupport χ ⊆ Ioo zlo zhi) :
    ∫ p, ((tentSlope a c b p.1 * χ p.2 : ℝ) : ℂ) * G p
      = -∫ p, ((tentFn a c b p.1 * χ p.2 : ℝ) : ℂ) * Gd p := by
  obtain ⟨K, hK⟩ := tent_slope a c b
  obtain ⟨Cχ, hCχ⟩ := hχc.exists_bound_of_continuous hχ.continuous
  have hχz : ∀ z, z ∉ Icc zlo zhi → χ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hm => hz (Ioo_subset_Icc_self (hχt hm))
  have hε : 0 < min (a - lo) (hi - b) / 2 := by
    have := lt_min (show 0 < a - lo by linarith) (show 0 < hi - b by linarith); linarith
  have hε1 : min (a - lo) (hi - b) / 2 < a - lo := by
    have := min_le_left (a - lo) (hi - b); linarith
  have hε2 : min (a - lo) (hi - b) / 2 < hi - b := by
    have := min_le_right (a - lo) (hi - b); linarith
  have hev := small_eventually hε
  refine limit_core (measurableSet_Icc.prod measurableSet_Icc) hG hGd
    (fun n p => deriv (mollTent a c b n) p.1 * χ p.2) (fun n p => mollTent a c b n p.1 * χ p.2)
    (fun p => tentSlope a c b p.1 * χ p.2) (fun p => tentFn a c b p.1 * χ p.2)
    (max (K : ℝ) (K * (b - a + 2)) * Cχ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n
    exact (((moll_smooth a c b n).continuous_deriv (by simp)).comp continuous_fst).mul
      (hχ.continuous.comp continuous_snd)
  · intro n
    exact ((moll_smooth a c b n).continuous.comp continuous_fst).mul (hχ.continuous.comp continuous_snd)
  · filter_upwards [hev] with n hn p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc lo hi ∧ p.2 ∈ Icc zlo zhi) from hp) with h | h
    · have hv := moll_vanish a c b hac hcb n p.1 fun hm => h ⟨by linarith [hm.1], by linarith [hm.2]⟩
      simp [hv.1, hv.2]
    · simp [hχz _ h]
  · intro p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc lo hi ∧ p.2 ∈ Icc zlo zhi) from hp) with h | h
    · have ht := tent_out (x := p.1) hac hcb fun hm => h ⟨by linarith [hm.1], by linarith [hm.2]⟩
      simp [ht.1, ht.2]
    · simp [hχz _ h]
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
    have hsm : ContDiff ℝ ∞ (fun q : ℝ × ℝ => mollTent a c b n q.1 * χ q.2) :=
      ((moll_smooth a c b n).comp contDiff_fst).mul (hχ.comp contDiff_snd)
    have hcs : HasCompactSupport (fun q : ℝ × ℝ => mollTent a c b n q.1 * χ q.2) := by
      refine HasCompactSupport.intro ((moll_hasCompactSupport hac hcb n).isCompact.prod hχc.isCompact) ?_
      intro q hq
      rcases not_and_or.1 (show ¬ (q.1 ∈ tsupport (mollTent a c b n) ∧ q.2 ∈ tsupport χ) from hq) with h | h
      · simp [image_eq_zero_of_notMem_tsupport h]
      · simp [image_eq_zero_of_notMem_tsupport h]
    have hsub : tsupport (fun q : ℝ × ℝ => mollTent a c b n q.1 * χ q.2) ⊆ Ioo lo hi ×ˢ Ioo zlo zhi := by
      have h1 : tsupport (fun q : ℝ × ℝ => mollTent a c b n q.1 * χ q.2) ⊆
          Icc (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1)) ×ˢ tsupport χ := by
        refine closure_minimal ?_ (isClosed_Icc.prod (isClosed_tsupport χ))
        intro q hq
        have hq' : mollTent a c b n q.1 * χ q.2 ≠ 0 := hq
        refine ⟨?_, subset_tsupport _ (right_ne_zero_of_mul hq')⟩
        by_contra hm
        exact left_ne_zero_of_mul hq' (moll_vanish a c b hac hcb n q.1 hm).1
      intro q hq
      have hq1 := h1 hq
      exact ⟨⟨by linarith [hq1.1.1], by linarith [hq1.1.2]⟩, hχt hq1.2⟩
    have hfd := fun q => fderiv_prod_apply ((moll_smooth a c b n).differentiable (by simp))
      (hχ.differentiable (by simp)) q
    have := hw _ hsm hcs hsub
    simp only [(hfd _).1] at this
    exact this

theorem height_tent {G Gd : ℝ × ℝ → ℂ} {lo hi zlo zhi : ℝ}
    (hG : IntegrableOn G (Icc lo hi ×ˢ Icc zlo zhi)) (hGd : IntegrableOn Gd (Icc lo hi ×ˢ Icc zlo zhi))
    (hw : WeakAlong G Gd (0, 1) (Ioo lo hi ×ˢ Ioo zlo zhi))
    {a c b : ℝ} (hac : a < c) (hcb : c < b) (ha : zlo < a) (hb : b < zhi)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχt : tsupport χ ⊆ Ioo lo hi) :
    ∫ p, ((χ p.1 * tentSlope a c b p.2 : ℝ) : ℂ) * G p
      = -∫ p, ((χ p.1 * tentFn a c b p.2 : ℝ) : ℂ) * Gd p := by
  obtain ⟨K, hK⟩ := tent_slope a c b
  obtain ⟨Cχ, hCχ⟩ := hχc.exists_bound_of_continuous hχ.continuous
  have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ 0)
  have hχz : ∀ r, r ∉ Icc lo hi → χ r = 0 := fun r hr =>
    image_eq_zero_of_notMem_tsupport fun hm => hr (Ioo_subset_Icc_self (hχt hm))
  have hε : 0 < min (a - zlo) (zhi - b) / 2 := by
    have := lt_min (show 0 < a - zlo by linarith) (show 0 < zhi - b by linarith); linarith
  have hε1 : min (a - zlo) (zhi - b) / 2 < a - zlo := by
    have := min_le_left (a - zlo) (zhi - b); linarith
  have hε2 : min (a - zlo) (zhi - b) / 2 < zhi - b := by
    have := min_le_right (a - zlo) (zhi - b); linarith
  have hev := small_eventually hε
  refine limit_core (measurableSet_Icc.prod measurableSet_Icc) hG hGd
    (fun n p => χ p.1 * deriv (mollTent a c b n) p.2) (fun n p => χ p.1 * mollTent a c b n p.2)
    (fun p => χ p.1 * tentSlope a c b p.2) (fun p => χ p.1 * tentFn a c b p.2)
    (Cχ * max (K : ℝ) (K * (b - a + 2))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro n
    exact (hχ.continuous.comp continuous_fst).mul
      (((moll_smooth a c b n).continuous_deriv (by simp)).comp continuous_snd)
  · intro n
    exact (hχ.continuous.comp continuous_fst).mul ((moll_smooth a c b n).continuous.comp continuous_snd)
  · filter_upwards [hev] with n hn p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc lo hi ∧ p.2 ∈ Icc zlo zhi) from hp) with h | h
    · simp [hχz _ h]
    · have hv := moll_vanish a c b hac hcb n p.2 fun hm => h ⟨by linarith [hm.1], by linarith [hm.2]⟩
      simp [hv.1, hv.2]
  · intro p hp
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc lo hi ∧ p.2 ∈ Icc zlo zhi) from hp) with h | h
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
    have hsub : tsupport (fun q : ℝ × ℝ => χ q.1 * mollTent a c b n q.2) ⊆ Ioo lo hi ×ˢ Ioo zlo zhi := by
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

theorem term_integrable {F Fr Fz Frz : ℝ × ℝ → ℂ} {R S : Set (ℝ × ℝ)} (hS : IsCompact S) (hSR : S ⊆ R)
    (iF : IntegrableOn F R) (iFr : IntegrableOn Fr R) (iFz : IntegrableOn Fz R) (iFrz : IntegrableOn Frz R)
    (cr orr cz oz : ℝ) : IntegrableOn (cornerTerm cr orr cz oz F Fr Fz Frz) S := by
  have h1 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p) S :=
    IntegrableOn.continuousOn_mul (by fun_prop) (iF.mono_set hSR) hS
  have h2 : IntegrableOn
      (fun p : ℝ × ℝ => (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p) S :=
    IntegrableOn.continuousOn_mul (by fun_prop) (iFz.mono_set hSR) hS
  have h3 : IntegrableOn
      (fun p : ℝ × ℝ => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * Fr p) S :=
    IntegrableOn.continuousOn_mul (by fun_prop) (iFr.mono_set hSR) hS
  have h4 : IntegrableOn
      (fun p : ℝ × ℝ => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p) S :=
    IntegrableOn.continuousOn_mul (by fun_prop) (iFrz.mono_set hSR) hS
  exact ((h1.add h2).add h3).add h4

theorem moment_eq_term (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) :
    cornerMoment cr orr cz oz F Fr Fz Frz = edgeSign cr orr * edgeSign cz oz *
      ∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc (min cz oz) (max cz oz),
        cornerTerm cr orr cz oz F Fr Fz Frz p := rfl


theorem radial_zero_local {F Fr Fz Frz : ℝ × ℝ → ℂ} {lo hi zlo zhi : ℝ}
    (iF : IntegrableOn F (Icc lo hi ×ˢ Icc zlo zhi)) (iFr : IntegrableOn Fr (Icc lo hi ×ˢ Icc zlo zhi))
    (iFz : IntegrableOn Fz (Icc lo hi ×ˢ Icc zlo zhi)) (iFrz : IntegrableOn Frz (Icc lo hi ×ˢ Icc zlo zhi))
    (w1 : WeakAlong F Fr (1, 0) (Ioo lo hi ×ˢ Ioo zlo zhi))
    (w4 : WeakAlong Fz Frz (1, 0) (Ioo lo hi ×ˢ Ioo zlo zhi))
    {cr a b cz oz : ℝ} (hac : a < cr) (hcb : cr < b) (ha : lo < a) (hb : b < hi)
    (hz1 : zlo ≤ min cz oz) (hz2 : max cz oz ≤ zhi) :
    ∫ p in Icc a b ×ˢ Icc (min cz oz) (max cz oz),
      cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p = 0 := by
  set zl := min cz oz
  set zh := max cz oz
  have hmeas : MeasurableSet (Icc a b ×ˢ Icc zl zh) := measurableSet_Icc.prod measurableSet_Icc
  set Φ : ℝ × ℝ → ℂ := fun p =>
    ((tentSlope a cr b p.1 : ℝ) : ℂ) * ((((1 / (cz - oz)) : ℝ) : ℂ) * F p + (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p)
    + ((tentFn a cr b p.1 : ℝ) : ℂ) *
      ((((1 / (cz - oz)) : ℝ) : ℂ) * Fr p + (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p) with hΦ
  have heq : EqOn (fun p => cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p) Φ
      (Icc a b ×ˢ Icc zl zh) := by
    intro p hp
    have hr := hp.1
    simp only [cornerTerm, hΦ]
    rw [tent_eq_on hac hcb hr]
    unfold tentSlope
    rw [if_pos hr]
    ring
  by_cases hI : IntegrableOn (fun p => cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p)
      (Icc a b ×ˢ Icc zl zh)
  swap
  · exact integral_undef hI
  rw [setIntegral_congr_fun hmeas heq]
  have hIp : Integrable Φ ((volume.restrict (Icc a b)).prod (volume.restrict (Icc zl zh))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hI.congr_fun heq hmeas
  have hsw : ∫ p in Icc a b ×ˢ Icc zl zh, Φ p = ∫ q in Icc zl zh ×ˢ Icc a b, Φ q.swap := by
    rw [Measure.volume_eq_prod]; exact (setIntegral_prod_swap _ _ Φ).symm
  rw [hsw]
  have hIs : IntegrableOn (fun q : ℝ × ℝ => Φ q.swap) (Icc zl zh ×ˢ Icc a b) := by
    have := hIp.swap
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at this
    exact this
  refine slice_zero hIs ?_
  intro χ hχs hχc hχt
  have hχt' : tsupport χ ⊆ Ioo zlo zhi := hχt.trans (Ioo_subset_Ioo hz1 hz2)
  have hχz : ∀ z, z ∉ Icc zlo zhi → χ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hm => hz (Ioo_subset_Icc_self (hχt' hm))
  set χ1 : ℝ → ℝ := fun z => χ z * (1 / (cz - oz)) with hχ1
  set χ2 : ℝ → ℝ := fun z => χ z * ((z - oz) / (cz - oz)) with hχ2
  have s1 : ContDiff ℝ ∞ χ1 := hχs.mul contDiff_const
  have s2 : ContDiff ℝ ∞ χ2 := hχs.mul ((contDiff_id.sub contDiff_const).div_const _)
  have c1 : HasCompactSupport χ1 := hχc.mul_right
  have c2 : HasCompactSupport χ2 := hχc.mul_right
  have t1 : tsupport χ1 ⊆ Ioo zlo zhi := tsupport_mul_subset_left.trans hχt'
  have t2 : tsupport χ2 ⊆ Ioo zlo zhi := tsupport_mul_subset_left.trans hχt'
  have z1 : ∀ z, z ∉ Icc zlo zhi → χ1 z = 0 := fun z hm => by simp [hχ1, hχz z hm]
  have z2 : ∀ z, z ∉ Icc zlo zhi → χ2 z = 0 := fun z hm => by simp [hχ2, hχz z hm]
  obtain ⟨B1, hB1⟩ := bdd_of_csupp s1.continuous c1
  obtain ⟨B2, hB2⟩ := bdd_of_csupp s2.continuous c2
  obtain ⟨Bt, hBt⟩ := tentFn_bound hac hcb
  have zs : ∀ r, r ∉ Icc a b → tentSlope a cr b r = 0 := fun r hm => (tent_out hac hcb hm).1
  have zt : ∀ r, r ∉ Icc a b → tentFn a cr b r = 0 := fun r hm => (tent_out hac hcb hm).2
  have hsub : Icc a b ×ˢ Icc zlo zhi ⊆ Icc lo hi ×ˢ Icc zlo zhi :=
    prod_mono (Icc_subset_Icc ha.le hb.le) le_rfl
  have i1 := int_region measurableSet_Icc measurableSet_Icc (iF.mono_set hsub) (tentSlope_meas a cr b)
    s1.continuous.measurable (tentSlope_bound a cr b) hB1 zs z1
  have i2 := int_region measurableSet_Icc measurableSet_Icc (iFr.mono_set hsub) (tent_cont a cr b).measurable
    s1.continuous.measurable hBt hB1 zt z1
  have i3 := int_region measurableSet_Icc measurableSet_Icc (iFz.mono_set hsub) (tentSlope_meas a cr b)
    s2.continuous.measurable (tentSlope_bound a cr b) hB2 zs z2
  have i4 := int_region measurableSet_Icc measurableSet_Icc (iFrz.mono_set hsub) (tent_cont a cr b).measurable
    s2.continuous.measurable hBt hB2 zt z2
  have k1 := radial_tent iF iFr w1 hac hcb ha hb s1 c1 t1
  have k2 := radial_tent iFz iFrz w4 hac hcb ha hb s2 c2 t2
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
    rcases not_and_or.1 (show ¬ (q.1 ∈ Icc zl zh ∧ q.2 ∈ Icc a b) from hq) with hh | hh
    · simp [image_eq_zero_of_notMem_tsupport (fun hm => hh (Ioo_subset_Icc_self (hχt hm)))]
    · have ho := tent_out hac hcb hh
      simp [hΦ, ho.1, ho.2]

theorem height_zero_local {F Fr Fz Frz : ℝ × ℝ → ℂ} {lo hi zlo zhi : ℝ}
    (iF : IntegrableOn F (Icc lo hi ×ˢ Icc zlo zhi)) (iFr : IntegrableOn Fr (Icc lo hi ×ˢ Icc zlo zhi))
    (iFz : IntegrableOn Fz (Icc lo hi ×ˢ Icc zlo zhi)) (iFrz : IntegrableOn Frz (Icc lo hi ×ˢ Icc zlo zhi))
    (w2 : WeakAlong F Fz (0, 1) (Ioo lo hi ×ˢ Ioo zlo zhi))
    (w3 : WeakAlong Fr Frz (0, 1) (Ioo lo hi ×ˢ Ioo zlo zhi))
    {cr orr cz a b : ℝ} (hac : a < cz) (hcb : cz < b) (ha : zlo < a) (hb : b < zhi)
    (hr1 : lo ≤ min cr orr) (hr2 : max cr orr ≤ hi) :
    ∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc a b,
      cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p = 0 := by
  set rl := min cr orr
  set rh := max cr orr
  have hmeas : MeasurableSet (Icc rl rh ×ˢ Icc a b) := measurableSet_Icc.prod measurableSet_Icc
  set Φ : ℝ × ℝ → ℂ := fun p =>
    (((1 / (cr - orr) : ℝ)) : ℂ) * (((tentSlope a cz b p.2 : ℝ) : ℂ) * F p + ((tentFn a cz b p.2 : ℝ) : ℂ) * Fz p)
    + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) *
      (((tentSlope a cz b p.2 : ℝ) : ℂ) * Fr p + ((tentFn a cz b p.2 : ℝ) : ℂ) * Frz p) with hΦ
  have heq : EqOn (fun p => cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p) Φ
      (Icc rl rh ×ˢ Icc a b) := by
    intro p hp
    have hz := hp.2
    simp only [cornerTerm, hΦ]
    rw [tent_eq_on hac hcb hz]
    unfold tentSlope
    rw [if_pos hz]
    ring
  by_cases hI : IntegrableOn (fun p => cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p)
      (Icc rl rh ×ˢ Icc a b)
  swap
  · exact integral_undef hI
  rw [setIntegral_congr_fun hmeas heq]
  refine slice_zero (hI.congr_fun heq hmeas) ?_
  intro χ hχs hχc hχt
  have hχt' : tsupport χ ⊆ Ioo lo hi := hχt.trans (Ioo_subset_Ioo hr1 hr2)
  have hχz : ∀ r, r ∉ Icc lo hi → χ r = 0 := fun r hr =>
    image_eq_zero_of_notMem_tsupport fun hm => hr (Ioo_subset_Icc_self (hχt' hm))
  set χ1 : ℝ → ℝ := fun r => χ r * (1 / (cr - orr)) with hχ1
  set χ2 : ℝ → ℝ := fun r => χ r * ((r - orr) / (cr - orr)) with hχ2
  have s1 : ContDiff ℝ ∞ χ1 := hχs.mul contDiff_const
  have s2 : ContDiff ℝ ∞ χ2 := hχs.mul ((contDiff_id.sub contDiff_const).div_const _)
  have c1 : HasCompactSupport χ1 := hχc.mul_right
  have c2 : HasCompactSupport χ2 := hχc.mul_right
  have t1 : tsupport χ1 ⊆ Ioo lo hi := tsupport_mul_subset_left.trans hχt'
  have t2 : tsupport χ2 ⊆ Ioo lo hi := tsupport_mul_subset_left.trans hχt'
  have z1 : ∀ r, r ∉ Icc lo hi → χ1 r = 0 := fun r hm => by simp [hχ1, hχz r hm]
  have z2 : ∀ r, r ∉ Icc lo hi → χ2 r = 0 := fun r hm => by simp [hχ2, hχz r hm]
  obtain ⟨B1, hB1⟩ := bdd_of_csupp s1.continuous c1
  obtain ⟨B2, hB2⟩ := bdd_of_csupp s2.continuous c2
  obtain ⟨Bt, hBt⟩ := tentFn_bound hac hcb
  have zs : ∀ z, z ∉ Icc a b → tentSlope a cz b z = 0 := fun z hz => (tent_out hac hcb hz).1
  have zt : ∀ z, z ∉ Icc a b → tentFn a cz b z = 0 := fun z hz => (tent_out hac hcb hz).2
  have hsub : Icc lo hi ×ˢ Icc a b ⊆ Icc lo hi ×ˢ Icc zlo zhi :=
    prod_mono le_rfl (Icc_subset_Icc ha.le hb.le)
  have i1 := int_region measurableSet_Icc measurableSet_Icc (iF.mono_set hsub) s1.continuous.measurable
    (tentSlope_meas a cz b) hB1 (tentSlope_bound a cz b) z1 zs
  have i2 := int_region measurableSet_Icc measurableSet_Icc (iFz.mono_set hsub) s1.continuous.measurable
    (tent_cont a cz b).measurable hB1 hBt z1 zt
  have i3 := int_region measurableSet_Icc measurableSet_Icc (iFr.mono_set hsub) s2.continuous.measurable
    (tentSlope_meas a cz b) hB2 (tentSlope_bound a cz b) z2 zs
  have i4 := int_region measurableSet_Icc measurableSet_Icc (iFrz.mono_set hsub) s2.continuous.measurable
    (tent_cont a cz b).measurable hB2 hBt z2 zt
  have k1 := height_tent iF iFz w2 hac hcb ha hb s1 c1 t1
  have k2 := height_tent iFr iFrz w3 hac hcb ha hb s2 c2 t2
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
    rcases not_and_or.1 (show ¬ (p.1 ∈ Icc rl rh ∧ p.2 ∈ Icc a b) from hp) with hh | hh
    · simp [image_eq_zero_of_notMem_tsupport (fun hm => hh (Ioo_subset_Icc_self (hχt hm)))]
    · have ho := tent_out hac hcb hh
      simp [hΦ, ho.1, ho.2]

theorem radial_move {F Fr Fz Frz : ℝ × ℝ → ℂ} {lo hi zlo zhi : ℝ}
    (iF : IntegrableOn F (Icc lo hi ×ˢ Icc zlo zhi)) (iFr : IntegrableOn Fr (Icc lo hi ×ˢ Icc zlo zhi))
    (iFz : IntegrableOn Fz (Icc lo hi ×ˢ Icc zlo zhi)) (iFrz : IntegrableOn Frz (Icc lo hi ×ˢ Icc zlo zhi))
    (w1 : WeakAlong F Fr (1, 0) (Ioo lo hi ×ˢ Ioo zlo zhi))
    (w4 : WeakAlong Fz Frz (1, 0) (Ioo lo hi ×ˢ Ioo zlo zhi))
    {cr a b cz oz : ℝ} (hac : a < cr) (hcb : cr < b) (ha : lo < a) (hb : b < hi)
    (hz1 : zlo ≤ min cz oz) (hz2 : max cz oz ≤ zhi) :
    cornerMoment cr a cz oz F Fr Fz Frz = cornerMoment cr b cz oz F Fr Fz Frz := by
  have hz0 := radial_zero_local iF iFr iFz iFrz w1 w4 hac hcb ha hb hz1 hz2
  set J := Icc (min cz oz) (max cz oz) with hJ
  have hJsub : J ⊆ Icc zlo zhi := Icc_subset_Icc hz1 hz2
  have hsplit : Icc a b ×ˢ J = (Icc a cr ×ˢ J) ∪ (Ioc cr b ×ˢ J) := by
    rw [← union_prod, Icc_union_Ioc_eq_Icc hac.le hcb.le]
  have hdisj : Disjoint (Icc a cr ×ˢ J) (Ioc cr b ×ˢ J) :=
    disjoint_left.2 fun p h1 h2 => (not_lt.2 h1.1.2) h2.1.1
  have hm1 : MeasurableSet (Icc a cr ×ˢ J) := measurableSet_Icc.prod measurableSet_Icc
  have hm2 : MeasurableSet (Ioc cr b ×ˢ J) := measurableSet_Ioc.prod measurableSet_Icc
  have eq1 : EqOn (fun p : ℝ × ℝ => cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p)
      (cornerTerm cr a cz oz F Fr Fz Frz) (Icc a cr ×ˢ J) := by
    intro p hp
    simp only [if_pos hp.1.2]
  have eq2 : EqOn (fun p : ℝ × ℝ => cornerTerm cr (if p.1 ≤ cr then a else b) cz oz F Fr Fz Frz p)
      (cornerTerm cr b cz oz F Fr Fz Frz) (Ioc cr b ×ˢ J) := by
    intro p hp
    simp only [if_neg (not_le.2 hp.1.1)]
  have i1 : IntegrableOn (cornerTerm cr a cz oz F Fr Fz Frz) (Icc a cr ×ˢ J) :=
    term_integrable (isCompact_Icc.prod isCompact_Icc)
      (prod_mono (Icc_subset_Icc ha.le (by linarith)) hJsub) iF iFr iFz iFrz _ _ _ _
  have i2' : IntegrableOn (cornerTerm cr b cz oz F Fr Fz Frz) (Icc cr b ×ˢ J) :=
    term_integrable (isCompact_Icc.prod isCompact_Icc)
      (prod_mono (Icc_subset_Icc (by linarith) hb.le) hJsub) iF iFr iFz iFrz _ _ _ _
  have i2 : IntegrableOn (cornerTerm cr b cz oz F Fr Fz Frz) (Ioc cr b ×ˢ J) :=
    i2'.mono_set (prod_mono Ioc_subset_Icc_self le_rfl)
  rw [hsplit, setIntegral_union hdisj hm2 (i1.congr_fun eq1.symm hm1) (i2.congr_fun eq2.symm hm2),
    setIntegral_congr_fun hm1 eq1, setIntegral_congr_fun hm2 eq2] at hz0
  have hset : (Ioc cr b ×ˢ J : Set (ℝ × ℝ)) =ᵐ[volume] (Icc cr b ×ˢ J : Set (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc (Filter.EventuallyEq.refl _ _)
  rw [setIntegral_congr_set hset] at hz0
  rw [moment_eq_term, moment_eq_term, min_eq_right hac.le, max_eq_left hac.le,
    min_eq_left hcb.le, max_eq_right hcb.le]
  have s1 : edgeSign cr a = 1 := if_pos hac
  have s2 : edgeSign cr b = -1 := if_neg (not_lt.2 hcb.le)
  rw [s1, s2]
  linear_combination edgeSign cz oz * hz0

theorem height_move {F Fr Fz Frz : ℝ × ℝ → ℂ} {lo hi zlo zhi : ℝ}
    (iF : IntegrableOn F (Icc lo hi ×ˢ Icc zlo zhi)) (iFr : IntegrableOn Fr (Icc lo hi ×ˢ Icc zlo zhi))
    (iFz : IntegrableOn Fz (Icc lo hi ×ˢ Icc zlo zhi)) (iFrz : IntegrableOn Frz (Icc lo hi ×ˢ Icc zlo zhi))
    (w2 : WeakAlong F Fz (0, 1) (Ioo lo hi ×ˢ Ioo zlo zhi))
    (w3 : WeakAlong Fr Frz (0, 1) (Ioo lo hi ×ˢ Ioo zlo zhi))
    {cr orr cz a b : ℝ} (hac : a < cz) (hcb : cz < b) (ha : zlo < a) (hb : b < zhi)
    (hr1 : lo ≤ min cr orr) (hr2 : max cr orr ≤ hi) :
    cornerMoment cr orr cz a F Fr Fz Frz = cornerMoment cr orr cz b F Fr Fz Frz := by
  have hz0 := height_zero_local iF iFr iFz iFrz w2 w3 hac hcb ha hb hr1 hr2
  set R := Icc (min cr orr) (max cr orr) with hR
  have hRsub : R ⊆ Icc lo hi := Icc_subset_Icc hr1 hr2
  have hsplit : R ×ˢ Icc a b = (R ×ˢ Icc a cz) ∪ (R ×ˢ Ioc cz b) := by
    rw [← prod_union, Icc_union_Ioc_eq_Icc hac.le hcb.le]
  have hdisj : Disjoint (R ×ˢ Icc a cz) (R ×ˢ Ioc cz b) :=
    disjoint_left.2 fun p h1 h2 => (not_lt.2 h1.2.2) h2.2.1
  have hm1 : MeasurableSet (R ×ˢ Icc a cz) := measurableSet_Icc.prod measurableSet_Icc
  have hm2 : MeasurableSet (R ×ˢ Ioc cz b) := measurableSet_Icc.prod measurableSet_Ioc
  have eq1 : EqOn (fun p : ℝ × ℝ => cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p)
      (cornerTerm cr orr cz a F Fr Fz Frz) (R ×ˢ Icc a cz) := by
    intro p hp
    simp only [if_pos hp.2.2]
  have eq2 : EqOn (fun p : ℝ × ℝ => cornerTerm cr orr cz (if p.2 ≤ cz then a else b) F Fr Fz Frz p)
      (cornerTerm cr orr cz b F Fr Fz Frz) (R ×ˢ Ioc cz b) := by
    intro p hp
    simp only [if_neg (not_le.2 hp.2.1)]
  have i1 : IntegrableOn (cornerTerm cr orr cz a F Fr Fz Frz) (R ×ˢ Icc a cz) :=
    term_integrable (isCompact_Icc.prod isCompact_Icc)
      (prod_mono hRsub (Icc_subset_Icc ha.le (by linarith))) iF iFr iFz iFrz _ _ _ _
  have i2' : IntegrableOn (cornerTerm cr orr cz b F Fr Fz Frz) (R ×ˢ Icc cz b) :=
    term_integrable (isCompact_Icc.prod isCompact_Icc)
      (prod_mono hRsub (Icc_subset_Icc (by linarith) hb.le)) iF iFr iFz iFrz _ _ _ _
  have i2 : IntegrableOn (cornerTerm cr orr cz b F Fr Fz Frz) (R ×ˢ Ioc cz b) :=
    i2'.mono_set (prod_mono le_rfl Ioc_subset_Icc_self)
  rw [hsplit, setIntegral_union hdisj hm2 (i1.congr_fun eq1.symm hm1) (i2.congr_fun eq2.symm hm2),
    setIntegral_congr_fun hm1 eq1, setIntegral_congr_fun hm2 eq2] at hz0
  have hset : (R ×ˢ Ioc cz b : Set (ℝ × ℝ)) =ᵐ[volume] (R ×ˢ Icc cz b : Set (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) Ioc_ae_eq_Icc
  rw [setIntegral_congr_set hset] at hz0
  rw [moment_eq_term, moment_eq_term, min_eq_right hac.le, max_eq_left hac.le,
    min_eq_left hcb.le, max_eq_right hcb.le]
  have s1 : edgeSign cz a = 1 := if_pos hac
  have s2 : edgeSign cz b = -1 := if_neg (not_lt.2 hcb.le)
  rw [s1, s2]
  linear_combination edgeSign cr orr * hz0

theorem corner_normal_local {F Fr Fz Frz : ℝ × ℝ → ℂ} {lo hi zlo zhi : ℝ}
    (iF : IntegrableOn F (Icc lo hi ×ˢ Icc zlo zhi)) (iFr : IntegrableOn Fr (Icc lo hi ×ˢ Icc zlo zhi))
    (iFz : IntegrableOn Fz (Icc lo hi ×ˢ Icc zlo zhi)) (iFrz : IntegrableOn Frz (Icc lo hi ×ˢ Icc zlo zhi))
    (w1 : WeakAlong F Fr (1, 0) (Ioo lo hi ×ˢ Ioo zlo zhi))
    (w2 : WeakAlong F Fz (0, 1) (Ioo lo hi ×ˢ Ioo zlo zhi))
    (w3 : WeakAlong Fr Frz (0, 1) (Ioo lo hi ×ˢ Ioo zlo zhi))
    (w4 : WeakAlong Fz Frz (1, 0) (Ioo lo hi ×ˢ Ioo zlo zhi))
    {cr cz o oz : ℝ} (hlo : lo < min cr o) (hhi : max cr o < hi) (hzlo : zlo < min cz oz)
    (hzhi : max cz oz < zhi) (hoc : o ≠ cr) (hoz : oz ≠ cz) :
    cornerMoment cr o cz oz F Fr Fz Frz
      = cornerMoment cr ((cr + hi) / 2) cz ((cz + zhi) / 2) F Fr Fz Frz := by
  have hcr1 : lo < cr := (lt_min_iff.1 hlo).1
  have ho1 : lo < o := (lt_min_iff.1 hlo).2
  have hcr2 : cr < hi := (max_lt_iff.1 hhi).1
  have ho2 : o < hi := (max_lt_iff.1 hhi).2
  have hcz1 : zlo < cz := (lt_min_iff.1 hzlo).1
  have hoz1 : zlo < oz := (lt_min_iff.1 hzlo).2
  have hcz2 : cz < zhi := (max_lt_iff.1 hzhi).1
  have hoz2 : oz < zhi := (max_lt_iff.1 hzhi).2
  have hr : cornerMoment cr o cz oz F Fr Fz Frz = cornerMoment cr ((cr + hi) / 2) cz oz F Fr Fz Frz := by
    rcases lt_or_gt_of_ne hoc with hlt | hgt
    · exact radial_move iF iFr iFz iFrz w1 w4 hlt (by linarith) ho1 (by linarith) hzlo.le hzhi.le
    · rw [← radial_move iF iFr iFz iFrz w1 w4 (a := (lo + cr) / 2) (b := o) (by linarith) hgt
        (by linarith) ho2 hzlo.le hzhi.le]
      exact radial_move iF iFr iFz iFrz w1 w4 (by linarith) (by linarith) (by linarith) (by linarith)
        hzlo.le hzhi.le
  rw [hr]
  have hm1 : lo ≤ min cr ((cr + hi) / 2) := le_min hcr1.le (by linarith)
  have hm2 : max cr ((cr + hi) / 2) ≤ hi := max_le hcr2.le (by linarith)
  rcases lt_or_gt_of_ne hoz with hlt | hgt
  · exact height_move iF iFr iFz iFrz w2 w3 hlt (by linarith) hoz1 (by linarith) hm1 hm2
  · rw [← height_move iF iFr iFz iFrz w2 w3 (a := (zlo + cz) / 2) (b := oz) (by linarith) hgt
      (by linarith) hoz2 hm1 hm2]
    exact height_move iF iFr iFz iFrz w2 w3 (by linarith) (by linarith) (by linarith) (by linarith) hm1 hm2

end Internal

open Internal in
theorem cornerPointTrace : CornerPointTraceHolds := by
  intro F Fr Fz Frz cr orr orr' cz oz oz' lo hi zlo zhi h1 h2 h3 h4 hlo hhi hzlo hzhi hW
  obtain ⟨iF, iFr, iFz, iFrz, hw⟩ := hW
  have hint : ∀ ψ : ℝ × ℝ → ℝ, tsupport ψ ⊆ Ioo lo hi ×ˢ Ioo zlo zhi →
      tsupport ψ ⊆ interior (Icc lo hi ×ˢ Icc zlo zhi) := by
    intro ψ hψ
    rwa [interior_prod_eq, interior_Icc, interior_Icc]
  have w1 : WeakAlong F Fr (1, 0) (Ioo lo hi ×ˢ Ioo zlo zhi) := fun ψ a b c =>
    whole_identity _ (hint ψ c) (hw ψ a b (hint ψ c)).1
  have w2 : WeakAlong F Fz (0, 1) (Ioo lo hi ×ˢ Ioo zlo zhi) := fun ψ a b c =>
    whole_identity _ (hint ψ c) (hw ψ a b (hint ψ c)).2.1
  have w3 : WeakAlong Fr Frz (0, 1) (Ioo lo hi ×ˢ Ioo zlo zhi) := fun ψ a b c =>
    whole_identity _ (hint ψ c) (hw ψ a b (hint ψ c)).2.2
  have w4 := mixed_of_three w1 w2 w3
  have a1 := lt_min_iff.1 hlo
  have a2 := lt_min_iff.1 a1.2
  have b1 := max_lt_iff.1 hhi
  have b2 := max_lt_iff.1 b1.2
  have c1 := lt_min_iff.1 hzlo
  have c2 := lt_min_iff.1 c1.2
  have d1 := max_lt_iff.1 hzhi
  have d2 := max_lt_iff.1 d1.2
  rw [corner_normal_local iF iFr iFz iFrz w1 w2 w3 w4 (lt_min a1.1 a2.1) (max_lt b1.1 b2.1)
      (lt_min c1.1 c2.1) (max_lt d1.1 d2.1) (Ne.symm h1) (Ne.symm h3),
    corner_normal_local iF iFr iFz iFrz w1 w2 w3 w4 (lt_min a1.1 a2.2) (max_lt b1.1 b2.2)
      (lt_min c1.1 c2.2) (max_lt d1.1 d2.2) (Ne.symm h2) (Ne.symm h4)]

end Breakdown.CertCell.SideTrace
