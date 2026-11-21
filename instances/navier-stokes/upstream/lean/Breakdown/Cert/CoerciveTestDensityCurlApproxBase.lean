import Breakdown.Cert.CoerciveTestDensityProof

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.Coercive

namespace Internal.CurlGraphMollify

open Internal.TestDensityProof

def bump (k : ℕ) : ContDiffBump (0 : Space) :=
  ⟨1 / ((k : ℝ) + 2), 1 / ((k : ℝ) + 1), by positivity,
    one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩

def kern (k : ℕ) : Space → ℝ := (bump k).normed volume

def moll (k : ℕ) (X : ℝ → Space → Space) (σ : ℝ) : Space → Space :=
  convolution (kern k) (X σ) (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem periodLIntegral_eq_lintegral {f : ℝ → Space → ℝ}
    (hf : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) periodMeasure) :
    periodLIntegral f = ∫⁻ z, ENNReal.ofReal (f z.1 z.2) ∂periodMeasure := by
  unfold periodLIntegral
  rw [lintegral_prod _ hf]

theorem periodLIntegral_congr_ae {f g : ℝ → Space → ℝ}
    (h : ∀ᵐ z ∂periodMeasure, f z.1 z.2 = g z.1 z.2) : periodLIntegral f = periodLIntegral g := by
  have h2 := Measure.ae_ae_of_ae_prod h
  unfold periodLIntegral
  refine lintegral_congr_ae ?_
  filter_upwards [h2] with σ hσ
  refine lintegral_congr_ae ?_
  filter_upwards [hσ] with y hy
  rw [hy]

theorem periodLIntegral_tri {u v w : ℝ → Space → Space}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) periodMeasure)
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) periodMeasure)
    (hw : AEStronglyMeasurable (fun z : ℝ × Space => w z.1 z.2) periodMeasure) :
    periodLIntegral (fun σ y => ‖u σ y - w σ y‖ ^ 2) ≤
      2 * periodLIntegral (fun σ y => ‖u σ y - v σ y‖ ^ 2) +
        2 * periodLIntegral (fun σ y => ‖v σ y - w σ y‖ ^ 2) := by
  have m : ∀ {a b : ℝ → Space → Space},
      AEStronglyMeasurable (fun z : ℝ × Space => a z.1 z.2) periodMeasure →
      AEStronglyMeasurable (fun z : ℝ × Space => b z.1 z.2) periodMeasure →
      AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖a z.1 z.2 - b z.1 z.2‖ ^ 2))
        periodMeasure := fun ha hb =>
    ((ha.sub hb).norm.aemeasurable.pow_const 2).ennreal_ofReal
  rw [periodLIntegral_eq_lintegral (m hu hw), periodLIntegral_eq_lintegral (m hu hv),
    periodLIntegral_eq_lintegral (m hv hw), ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
    ← lintegral_add_left' ((m hu hv).const_mul _)]
  refine lintegral_mono fun z => ?_
  have e : ‖u z.1 z.2 - w z.1 z.2‖ ^ 2 ≤
      2 * ‖u z.1 z.2 - v z.1 z.2‖ ^ 2 + 2 * ‖v z.1 z.2 - w z.1 z.2‖ ^ 2 := by
    have t := norm_sub_le_norm_sub_add_norm_sub (u z.1 z.2) (v z.1 z.2) (w z.1 z.2)
    nlinarith [norm_nonneg (u z.1 z.2 - w z.1 z.2), norm_nonneg (u z.1 z.2 - v z.1 z.2),
      norm_nonneg (v z.1 z.2 - w z.1 z.2), sq_nonneg (‖u z.1 z.2 - v z.1 z.2‖ - ‖v z.1 z.2 - w z.1 z.2‖)]
  calc ENNReal.ofReal (‖u z.1 z.2 - w z.1 z.2‖ ^ 2)
      ≤ ENNReal.ofReal (2 * ‖u z.1 z.2 - v z.1 z.2‖ ^ 2 + 2 * ‖v z.1 z.2 - w z.1 z.2‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal e
    _ = 2 * ENNReal.ofReal (‖u z.1 z.2 - v z.1 z.2‖ ^ 2) +
          2 * ENNReal.ofReal (‖v z.1 z.2 - w z.1 z.2‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp

theorem memLp_of_continuous {Y : ℝ → Space → Space}
    (hc : Continuous (fun z : ℝ × Space => Y z.1 z.2))
    (hR : ∃ R, ∀ σ y, R < ‖y‖ → Y σ y = 0) :
    MemLp (fun z : ℝ × Space => Y z.1 z.2) 2 periodMeasure := by
  obtain ⟨R, hR⟩ := hR
  set K : Set (ℝ × Space) := Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R with hK
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_closedBall
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hc.continuousOn
  have hfin : periodMeasure K ≠ ⊤ := by
    rw [hK, Measure.prod_prod]
    exact ENNReal.mul_ne_top (by rw [Measure.restrict_apply measurableSet_Icc]; exact
      (measure_mono inter_subset_left).trans_lt (by simp) |>.ne) measure_closedBall_lt_top.ne
  have : IsFiniteMeasure (periodMeasure.restrict K) := isFiniteMeasure_restrict.2 hfin
  have h1 : MemLp (fun z : ℝ × Space => Y z.1 z.2) 2 (periodMeasure.restrict K) :=
    MemLp.of_bound hc.aestronglyMeasurable C ((ae_restrict_iff' hKm).2 (ae_of_all _ fun z hz => hC z hz))
  have h2 := (memLp_indicator_iff_restrict hKm).2 h1
  refine h2.ae_eq ?_
  have hae : ∀ᵐ z ∂periodMeasure, z.1 ∈ Icc (0 : ℝ) 1 := by
    rw [periodMeasure_eq]
    exact (ae_restrict_iff' (measurableSet_Icc.prod MeasurableSet.univ)).2 (ae_of_all _ fun z hz => hz.1)
  filter_upwards [hae] with z hz
  by_cases hz2 : z ∈ K
  · rw [indicator_of_mem hz2]
  · rw [indicator_of_notMem hz2]
    have h3 : z.2 ∉ Metric.closedBall (0 : Space) R := fun h3 => hz2 ⟨hz, h3⟩
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at h3
    exact (hR _ _ h3).symm

theorem periodLIntegral_sub_comm (u v : ℝ → Space → Space) :
    periodLIntegral (fun σ y => ‖u σ y - v σ y‖ ^ 2) =
      periodLIntegral (fun σ y => ‖v σ y - u σ y‖ ^ 2) := by
  simp only [norm_sub_rev]

theorem tendsto_inv_succ : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop (nhds 0) :=
  ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)


end Internal.CurlGraphMollify

end Breakdown.Coercive
