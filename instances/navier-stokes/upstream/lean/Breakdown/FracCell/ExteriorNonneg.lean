import Breakdown.FracCell.StExterior
import Mathlib

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Exterior

open SteadyCert Assembly

private theorem entrySq_nonneg' (G : Space →L[ℝ] Space) : 0 ≤ entrySq G := by
  unfold entrySq
  positivity

private theorem pointwise_real {E a n LD gc cl W Mn ww wm : ℝ} (hE : 0 ≤ E) (ha : 0 ≤ a) (hn : 0 < n)
    (hwm : 0 ≤ wm) (h2 : gc * E - W * a ^ 2 - Mn * a * Real.sqrt E ≤ LD) (hcl : cl ≤ gc)
    (hW : n ^ 2 * W ≤ ww) (hM : n * Mn ≤ wm) :
    (cl - wm) * E - (ww + wm / 4) * (a ^ 2 / n ^ 2) ≤ LD := by
  have hn0 : n ≠ 0 := hn.ne'
  have hq : 0 ≤ a / n := div_nonneg ha hn.le
  have hs : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hs2 : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  have han : a = n * (a / n) := by field_simp
  have hq2 : a ^ 2 / n ^ 2 = (a / n) ^ 2 := (div_pow a n 2).symm
  have e1 : W * a ^ 2 = (n ^ 2 * W) * (a / n) ^ 2 := by
    conv_lhs => rw [han]
    ring
  have e2 : Mn * a * Real.sqrt E = (n * Mn) * (a / n) * Real.sqrt E := by
    conv_lhs => rw [han]
    ring
  have k1 : (n ^ 2 * W) * (a / n) ^ 2 ≤ ww * (a / n) ^ 2 := mul_le_mul_of_nonneg_right hW (sq_nonneg _)
  have k2 : (n * Mn) * (a / n) * Real.sqrt E ≤ wm * (a / n) * Real.sqrt E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hq) hs
  have k3 : (a / n) * Real.sqrt E ≤ (a / n) ^ 2 / 4 + E := by
    nlinarith [sq_nonneg (a / n / 2 - Real.sqrt E)]
  have k4 : wm * ((a / n) * Real.sqrt E) ≤ wm * ((a / n) ^ 2 / 4 + E) := mul_le_mul_of_nonneg_left k3 hwm
  have k5 : cl * E ≤ gc * E := mul_le_mul_of_nonneg_right hcl hE
  rw [hq2]
  rw [e1, e2] at h2
  nlinarith [k1, k2, k4, k5]

theorem exteriorNonneg_of (h1 : RayWeakStatement) (h2 : ExteriorPointwiseStatement) :
    ExteriorNonnegStatement := by
  intro α hα1 hα2 k N c hc e he x hx
  have hso : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1 := hx.1
  have hmeas : MeasurableSet (rayRegion e.radius) :=
    measurableSet_lt he.radius_measurable continuous_norm.measurable
  have hrestr : volume.restrict c.cellRegionᶜ = volume.restrict (rayRegion e.radius) :=
    Measure.restrict_congr_set he.exterior_eq
  rw [hrestr]
  obtain ⟨hQint, hQle⟩ := h1 e.radius e.radiusMin e.radiusMax he.radius_measurable he.radiusMin_pos
    he.radius_between he.radius_homogeneous x.1 x.2.1 hso.measurable_velocity hso.velocity_six
    hso.measurable_gradient hso.gradient_two hso.weak_gradient
  have hout : ∃ y, y ∉ c.cellRegion := by
    by_contra hno
    exact NormedSpace.unbounded_univ ℝ Space
      (hc.cellRegion_bounded.subset (fun y _ => by_contra fun h => hno ⟨y, h⟩))
  obtain ⟨y0, hy0⟩ := hout
  have htf : 0 ≤ traceFreeConst := Real.sqrt_nonneg _
  have hww : 0 ≤ e.weightedWave := by
    refine le_trans ?_ (he.wave_bound y0 hy0)
    exact mul_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg (div_nonneg htf (by norm_num))
      (he.waveCurlGradBound_nonneg y0)) (he.splitLength_pos y0 hy0).le)
  have hwm : 0 ≤ e.weightedMean := by
    refine le_trans ?_ (he.mean_bound y0 hy0)
    exact mul_nonneg (norm_nonneg _) (mul_nonneg htf (he.meanCurlGradBound_nonneg y0))
  have hEint : IntegrableOn (fun y => entrySq (x.2.1 y)) (rayRegion e.radius) :=
    hso.gradient_two.integrableOn
  have hA : 0 ≤ ∫ y in rayRegion e.radius, entrySq (x.2.1 y) :=
    setIntegral_nonneg hmeas (fun y _ => entrySq_nonneg' _)
  have hgint : IntegrableOn (fun y => (e.coefLower - e.weightedMean) * entrySq (x.2.1 y)
      - (e.weightedWave + e.weightedMean / 4) * (‖x.1 y‖ ^ 2 / ‖y‖ ^ 2)) (rayRegion e.radius) :=
    (hEint.const_mul _).sub (hQint.const_mul _)
  have hgval : ∫ y in rayRegion e.radius, ((e.coefLower - e.weightedMean) * entrySq (x.2.1 y)
      - (e.weightedWave + e.weightedMean / 4) * (‖x.1 y‖ ^ 2 / ‖y‖ ^ 2))
      = (e.coefLower - e.weightedMean) * (∫ y in rayRegion e.radius, entrySq (x.2.1 y))
        - (e.weightedWave + e.weightedMean / 4) * ∫ y in rayRegion e.radius, ‖x.1 y‖ ^ 2 / ‖y‖ ^ 2 := by
    rw [integral_sub (hEint.const_mul _) (hQint.const_mul _), integral_const_mul, integral_const_mul]
  have hg0 : 0 ≤ ∫ y in rayRegion e.radius, ((e.coefLower - e.weightedMean) * entrySq (x.2.1 y)
      - (e.weightedWave + e.weightedMean / 4) * (‖x.1 y‖ ^ 2 / ‖y‖ ^ 2)) := by
    rw [hgval]
    have hc4 : 0 ≤ e.weightedWave + e.weightedMean / 4 := by linarith
    have hB := mul_le_mul_of_nonneg_left hQle hc4
    have hT := mul_nonneg (sub_nonneg.mpr he.exterior_test) hA
    nlinarith [hB, hT]
  have hae : ∀ᵐ y ∂(volume.restrict (rayRegion e.radius)),
      (e.coefLower - e.weightedMean) * entrySq (x.2.1 y)
        - (e.weightedWave + e.weightedMean / 4) * (‖x.1 y‖ ^ 2 / ‖y‖ ^ 2)
        ≤ CellSplit.localDensity c α x y := by
    have hm1 : ∀ᵐ y ∂(volume.restrict (rayRegion e.radius)), y ∈ rayRegion e.radius :=
      ae_restrict_mem hmeas
    have hm2 : ∀ᵐ y ∂(volume.restrict (rayRegion e.radius)), y ∈ c.cellRegionᶜ := by
      rw [← hrestr]
      exact ae_restrict_mem₀ (hmeas.nullMeasurableSet.congr he.exterior_eq.symm)
    filter_upwards [hm1, hm2] with y hy hyc
    have hR : 0 ≤ e.radius y := le_trans he.radiusMin_pos.le (he.radius_between y).1
    have hn : 0 < ‖y‖ := lt_of_le_of_lt hR hy
    exact pointwise_real (entrySq_nonneg' _) (norm_nonneg _) hn hwm
      (h2 α hα1 hα2 c hc e he x hx y hyc) (he.coef_lower y hyc) (he.wave_bound y hyc)
      (he.mean_bound y hyc)
  by_cases hLD : IntegrableOn (fun y => CellSplit.localDensity c α x y) (rayRegion e.radius)
  · exact hg0.trans (integral_mono_ae hgint hLD hae)
  · exact le_of_eq (integral_undef hLD).symm

end Exterior

end CellCert

end Breakdown
