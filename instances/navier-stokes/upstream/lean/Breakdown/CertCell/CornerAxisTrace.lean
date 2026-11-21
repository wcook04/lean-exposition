import Breakdown.CertCell.BridgeTraceStatements

open MeasureTheory Filter Topology Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

open CellCert.CellFormula

namespace Internal

def cornerIntegrand (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p
    + (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Fz p
    + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * Fr p
    + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * Frz p

theorem cornerMoment_eq_integrand (cr orr cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) :
    cornerMoment cr orr cz oz F Fr Fz Frz = edgeSign cr orr * edgeSign cz oz *
      ∫ p in Icc (min cr orr) (max cr orr) ×ˢ Icc (min cz oz) (max cz oz),
        cornerIntegrand cr orr cz oz F Fr Fz Frz p := rfl

def axisCut (cr δ cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  indicator (Icc δ cr ×ˢ Icc (min cz oz) (max cz oz)) (cornerIntegrand cr δ cz oz F Fr Fz Frz)

def axisStep (cr : ℝ) (n : ℕ) : ℝ := cr / 2 * (1 / ((n : ℝ) + 1))

theorem axisStep_pos {cr : ℝ} (hcr : 0 < cr) (n : ℕ) : 0 < axisStep cr n := by
  unfold axisStep
  positivity

theorem axisStep_le {cr : ℝ} (hcr : 0 < cr) (n : ℕ) : axisStep cr n ≤ cr / 2 := by
  unfold axisStep
  have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : 0 ≤ cr / 2 := by positivity
  nlinarith

theorem axisStep_lt {cr : ℝ} (hcr : 0 < cr) (n : ℕ) : axisStep cr n < cr :=
  lt_of_le_of_lt (axisStep_le hcr n) (half_lt_self hcr)

theorem axisStep_tendsto (cr : ℝ) : Tendsto (axisStep cr) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (cr / 2)
  rw [mul_zero] at h
  exact h

theorem ae_fst_ne_zero : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 := by
  rw [ae_iff]
  have e : {a : ℝ × ℝ | ¬a.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (univ : Set ℝ) := by
    ext p
    simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem aesm_of_weighted {G : ℝ × ℝ → ℂ} {μ : Measure (ℝ × ℝ)} (hμ : ∀ᵐ p ∂μ, p.1 ≠ 0)
    (h : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 : ℂ) * G p) μ) : AEStronglyMeasurable G μ := by
  have hinv : AEStronglyMeasurable (fun p : ℝ × ℝ => ((p.1 : ℂ))⁻¹) μ :=
    ((Complex.measurable_ofReal.comp measurable_fst).inv).aestronglyMeasurable
  refine (hinv.mul h).congr ?_
  filter_upwards [hμ] with p hp
  have hne : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  show ((p.1 : ℂ))⁻¹ * ((p.1 : ℂ) * G p) = G p
  rw [inv_mul_cancel_left₀ hne]

theorem cornerIntegrand_aesm {μ : Measure (ℝ × ℝ)} (cr orr cz oz : ℝ) {F Fr Fz Frz : ℝ × ℝ → ℂ}
    (hF : AEStronglyMeasurable F μ) (hFr : AEStronglyMeasurable Fr μ) (hFz : AEStronglyMeasurable Fz μ)
    (hFrz : AEStronglyMeasurable Frz μ) :
    AEStronglyMeasurable (cornerIntegrand cr orr cz oz F Fr Fz Frz) μ := by
  unfold cornerIntegrand
  have c1 : Continuous fun p : ℝ × ℝ => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) := by fun_prop
  have c2 : Continuous fun p : ℝ × ℝ => (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) := by fun_prop
  have m1 := c1.aestronglyMeasurable (μ := μ)
  have m2 := c2.aestronglyMeasurable (μ := μ)
  fun_prop

theorem key_moment (cr δ cz oz : ℝ) (F Fr Fz Frz : ℝ × ℝ → ℂ) (h0 : 0 ≤ δ) (hlt : δ < cr) :
    cornerMoment cr δ cz oz F Fr Fz Frz
      = edgeSign cz oz * ∫ p in Icc 0 cr ×ˢ Icc (min cz oz) (max cz oz), axisCut cr δ cz oz F Fr Fz Frz p := by
  rw [cornerMoment_eq_integrand, min_eq_right hlt.le, max_eq_left hlt.le]
  have he : edgeSign cr δ = 1 := by
    unfold edgeSign
    rw [if_pos hlt]
  rw [he, one_mul]
  congr 1
  have hT : MeasurableSet (Icc δ cr ×ˢ Icc (min cz oz) (max cz oz)) := measurableSet_Icc.prod measurableSet_Icc
  have hTS : Icc δ cr ×ˢ Icc (min cz oz) (max cz oz) ⊆ Icc 0 cr ×ˢ Icc (min cz oz) (max cz oz) :=
    prod_mono (Icc_subset_Icc h0 le_rfl) subset_rfl
  unfold axisCut
  rw [integral_indicator hT, Measure.restrict_restrict hT, inter_eq_left.mpr hTS]

theorem axisCut_norm_le {cr δ cz oz : ℝ} {F Fr Fz Frz : ℝ × ℝ → ℂ} (hcr : 0 < cr) (h0 : 0 ≤ δ)
    (hδ : δ ≤ cr / 2) (p : ℝ × ℝ) :
    ‖axisCut cr δ cz oz F Fr Fz Frz p‖
      ≤ 2 / cr * (|1 / (cz - oz)| + 1) * (‖F p‖ + ‖Fz p‖ + ‖(p.1 : ℂ) * Fr p‖ + ‖(p.1 : ℂ) * Frz p‖) := by
  unfold axisCut
  by_cases hp : p ∈ Icc δ cr ×ˢ Icc (min cz oz) (max cz oz)
  · rw [indicator_of_mem hp]
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    have hcd : 0 < cr - δ := by linarith
    have a1 : |1 / (cr - δ)| ≤ 2 / cr := by
      rw [abs_of_pos (by positivity)]
      have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < cr / 2) (by linarith : cr / 2 ≤ cr - δ)
      rw [one_div_div] at this
      exact this
    have b1 : |(p.2 - oz) / (cz - oz)| ≤ 1 := by
      rw [abs_div]
      refine div_le_one_of_le₀ ?_ (abs_nonneg _)
      rcases le_total cz oz with h | h
      · rw [min_eq_left h] at h3
        rw [max_eq_right h] at h4
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
      · rw [min_eq_right h] at h3
        rw [max_eq_left h] at h4
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
    have c1 : |(p.1 - δ) / (cr - δ)| ≤ 2 / cr * |p.1| := by
      rw [abs_of_nonneg (div_nonneg (by linarith) hcd.le), abs_of_nonneg (by linarith)]
      rw [div_le_iff₀ hcd]
      have hu : 2 / cr * cr = 2 := by field_simp
      have hu0 : 0 < 2 / cr := by positivity
      have hu1 : 2 / cr * δ ≤ 1 := by nlinarith
      have hp1 : 0 ≤ p.1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hu1 hp1]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    refine le_trans (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have x1 := norm_nonneg (F p)
    have x2 := norm_nonneg (Fz p)
    have x3 := norm_nonneg (Fr p)
    have x4 := norm_nonneg (Frz p)
    have hA := abs_nonneg (1 / (cz - oz))
    have hr := abs_nonneg p.1
    have t1 : |1 / (cr - δ)| * |1 / (cz - oz)| * ‖F p‖ ≤ 2 / cr * |1 / (cz - oz)| * ‖F p‖ := by gcongr
    have t2 : |1 / (cr - δ)| * |(p.2 - oz) / (cz - oz)| * ‖Fz p‖ ≤ 2 / cr * 1 * ‖Fz p‖ := by gcongr
    have t3 : |(p.1 - δ) / (cr - δ)| * |1 / (cz - oz)| * ‖Fr p‖ ≤ 2 / cr * |p.1| * |1 / (cz - oz)| * ‖Fr p‖ := by
      gcongr
    have t4 : |(p.1 - δ) / (cr - δ)| * |(p.2 - oz) / (cz - oz)| * ‖Frz p‖ ≤ 2 / cr * |p.1| * 1 * ‖Frz p‖ := by
      gcongr
    have hu0 : 0 < 2 / cr := by positivity
    have extra : 0 ≤ 2 / cr * ‖F p‖ + 2 / cr * |1 / (cz - oz)| * ‖Fz p‖ + 2 / cr * |p.1| * ‖Fr p‖
        + 2 / cr * |1 / (cz - oz)| * |p.1| * ‖Frz p‖ := by positivity
    have e : 2 / cr * (|1 / (cz - oz)| + 1) * (‖F p‖ + ‖Fz p‖ + |p.1| * ‖Fr p‖ + |p.1| * ‖Frz p‖)
        = 2 / cr * |1 / (cz - oz)| * ‖F p‖ + 2 / cr * 1 * ‖Fz p‖ + 2 / cr * |p.1| * |1 / (cz - oz)| * ‖Fr p‖
          + 2 / cr * |p.1| * 1 * ‖Frz p‖
          + (2 / cr * ‖F p‖ + 2 / cr * |1 / (cz - oz)| * ‖Fz p‖ + 2 / cr * |p.1| * ‖Fr p‖
            + 2 / cr * |1 / (cz - oz)| * |p.1| * ‖Frz p‖) := by ring
    rw [e]
    linarith
  · rw [indicator_of_notMem hp, norm_zero]
    have : 0 < 2 / cr := by positivity
    positivity

theorem integrand_tendsto {cr cz oz : ℝ} (F Fr Fz Frz : ℝ × ℝ → ℂ) (hcr : 0 < cr) (p : ℝ × ℝ) :
    Tendsto (fun n => cornerIntegrand cr (axisStep cr n) cz oz F Fr Fz Frz p) atTop
      (𝓝 (cornerIntegrand cr 0 cz oz F Fr Fz Frz p)) := by
  have hne : cr - 0 ≠ 0 := by simpa using hcr.ne'
  have k1 : ContinuousAt (fun δ : ℝ => 1 / (cr - δ)) 0 :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_id) hne
  have k2 : ContinuousAt (fun δ : ℝ => (p.1 - δ) / (cr - δ)) 0 :=
    (continuousAt_const.sub continuousAt_id).div (continuousAt_const.sub continuousAt_id) hne
  have q1 : ContinuousAt (fun δ : ℝ => (((1 / (cr - δ) : ℝ)) : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp k1
  have q2 : ContinuousAt (fun δ : ℝ => (((p.1 - δ) / (cr - δ) : ℝ) : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp k2
  have hc : ContinuousAt (fun δ : ℝ => cornerIntegrand cr δ cz oz F Fr Fz Frz p) 0 := by
    unfold cornerIntegrand
    exact (((q1.mul continuousAt_const).mul continuousAt_const).add
      ((q1.mul continuousAt_const).mul continuousAt_const)).add
      ((q2.mul continuousAt_const).mul continuousAt_const) |>.add
      ((q2.mul continuousAt_const).mul continuousAt_const)
  exact hc.tendsto.comp (axisStep_tendsto cr)

theorem axis_limit (F Fr Fz Frz : ℝ × ℝ → ℂ) (cr cz oz hi zlo zhi : ℝ) (hcr : 0 < cr) (hhi : cr ≤ hi)
    (hzl : zlo ≤ min cz oz) (hzh : max cz oz ≤ zhi)
    (iF : IntegrableOn F (Icc 0 hi ×ˢ Icc zlo zhi)) (iFz : IntegrableOn Fz (Icc 0 hi ×ˢ Icc zlo zhi))
    (iFr : IntegrableOn (fun p => (p.1 : ℂ) * Fr p) (Icc 0 hi ×ˢ Icc zlo zhi))
    (iFrz : IntegrableOn (fun p => (p.1 : ℂ) * Frz p) (Icc 0 hi ×ˢ Icc zlo zhi)) :
    Tendsto (fun n => cornerMoment cr (axisStep cr n) cz oz F Fr Fz Frz) atTop
      (𝓝 (cornerMoment cr 0 cz oz F Fr Fz Frz)) := by
  have hSsub : Icc 0 cr ×ˢ Icc (min cz oz) (max cz oz) ⊆ Icc 0 hi ×ˢ Icc zlo zhi :=
    prod_mono (Icc_subset_Icc le_rfl hhi) (Icc_subset_Icc hzl hzh)
  have hSm : MeasurableSet (Icc 0 cr ×ˢ Icc (min cz oz) (max cz oz)) := measurableSet_Icc.prod measurableSet_Icc
  have jF := iF.mono_set hSsub
  have jFz := iFz.mono_set hSsub
  have jFr := iFr.mono_set hSsub
  have jFrz := iFrz.mono_set hSsub
  have hnz : ∀ᵐ p ∂(volume.restrict (Icc 0 cr ×ˢ Icc (min cz oz) (max cz oz))), p.1 ≠ 0 :=
    ae_restrict_of_ae ae_fst_ne_zero
  have mFr := aesm_of_weighted hnz jFr.aestronglyMeasurable
  have mFrz := aesm_of_weighted hnz jFrz.aestronglyMeasurable
  rw [key_moment cr 0 cz oz F Fr Fz Frz le_rfl hcr]
  refine Tendsto.congr (fun n => (key_moment cr (axisStep cr n) cz oz F Fr Fz Frz
    (axisStep_pos hcr n).le (axisStep_lt hcr n)).symm) ?_
  refine Tendsto.const_mul _ ?_
  refine tendsto_integral_of_dominated_convergence
    (fun p => 2 / cr * (|1 / (cz - oz)| + 1) * (‖F p‖ + ‖Fz p‖ + ‖(p.1 : ℂ) * Fr p‖ + ‖(p.1 : ℂ) * Frz p‖))
    (fun n => (cornerIntegrand_aesm cr (axisStep cr n) cz oz jF.aestronglyMeasurable mFr
      jFz.aestronglyMeasurable mFrz).indicator (measurableSet_Icc.prod measurableSet_Icc))
    ((((jF.norm.add jFz.norm).add jFr.norm).add jFrz.norm).const_mul (2 / cr * (|1 / (cz - oz)| + 1)))
    (fun n => Eventually.of_forall fun p => axisCut_norm_le hcr (axisStep_pos hcr n).le (axisStep_le hcr n) p) ?_
  filter_upwards [ae_restrict_mem hSm, hnz] with p hpS hp0
  obtain ⟨⟨h1, h2⟩, hz⟩ := hpS
  have hpos : 0 < p.1 := lt_of_le_of_ne h1 (Ne.symm hp0)
  have ev : ∀ᶠ n in atTop, axisStep cr n < p.1 := (axisStep_tendsto cr).eventually (eventually_lt_nhds hpos)
  have hm0 : p ∈ Icc 0 cr ×ˢ Icc (min cz oz) (max cz oz) := ⟨⟨h1, h2⟩, hz⟩
  have eq0 : axisCut cr 0 cz oz F Fr Fz Frz p = cornerIntegrand cr 0 cz oz F Fr Fz Frz p := by
    unfold axisCut
    exact indicator_of_mem hm0 _
  rw [eq0]
  refine Tendsto.congr' (ev.mono fun n hn => ?_) (integrand_tendsto F Fr Fz Frz hcr p)
  have hmn : p ∈ Icc (axisStep cr n) cr ×ˢ Icc (min cz oz) (max cz oz) := ⟨⟨hn.le, h2⟩, hz⟩
  show cornerIntegrand cr (axisStep cr n) cz oz F Fr Fz Frz p = axisCut cr (axisStep cr n) cz oz F Fr Fz Frz p
  unfold axisCut
  exact (indicator_of_mem hmn _).symm

end Internal

open Internal in
theorem cornerAxisTrace (hC : CornerPointTraceHolds) : CornerAxisTraceHolds := by
  intro F Fr Fz Frz cr orr' cz oz oz' hi zlo zhi hcr horr' hne hzo hzo' hhi hzlo hzhi hW iF iFz iFr iFrz
  have hcrhi : cr < hi := lt_of_le_of_lt (le_max_left _ _) hhi
  have horrhi : orr' < hi := lt_of_le_of_lt (le_max_right _ _) hhi
  have hz1 : zlo < cz := lt_of_lt_of_le hzlo (min_le_left _ _)
  have hz2 : zlo < oz := lt_of_lt_of_le hzlo ((min_le_right _ _).trans (min_le_left _ _))
  have hz3 : zlo < oz' := lt_of_lt_of_le hzlo ((min_le_right _ _).trans (min_le_right _ _))
  have hw1 : cz < zhi := lt_of_le_of_lt (le_max_left _ _) hzhi
  have hw2 : oz < zhi := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hzhi
  have hw3 : oz' < zhi := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hzhi
  have lim1 := axis_limit F Fr Fz Frz cr cz oz hi zlo zhi hcr hcrhi.le (le_min hz1.le hz2.le)
    (max_le hw1.le hw2.le) iF iFz iFr iFrz
  have step : ∀ n, ∀ o : ℝ, 0 < o → o < hi → o ≠ cr → axisStep cr n ≤ o →
      cornerMoment cr (axisStep cr n) cz oz F Fr Fz Frz = cornerMoment cr o cz oz' F Fr Fz Frz := by
    intro n o ho hoh hoc hno
    have hs := axisStep_pos hcr n
    have hsc := axisStep_lt hcr n
    refine hC F Fr Fz Frz cr (axisStep cr n) o cz oz oz' (axisStep cr n / 2) hi zlo zhi hsc.ne' hoc.symm
      hzo hzo' ?_ ?_ hzlo hzhi (hW _ (half_pos hs))
    · refine lt_min (by linarith) (lt_min (by linarith) (by linarith))
    · exact max_lt hcrhi (max_lt (by linarith) hoh)
  rcases horr'.eq_or_lt with h0 | hpos
  · subst h0
    have lim2 := axis_limit F Fr Fz Frz cr cz oz' hi zlo zhi hcr hcrhi.le (le_min hz1.le hz3.le)
      (max_le hw1.le hw3.le) iF iFz iFr iFrz
    refine tendsto_nhds_unique lim1 (lim2.congr fun n => ?_)
    exact (step n (axisStep cr n) (axisStep_pos hcr n) (lt_trans (axisStep_lt hcr n) hcrhi)
      (axisStep_lt hcr n).ne le_rfl).symm
  · refine tendsto_nhds_unique lim1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [(axisStep_tendsto cr).eventually (eventually_lt_nhds hpos)] with n hn
    exact (step n orr' hpos horrhi hne.symm hn.le).symm

end SideTrace

end CertCell

end Breakdown
