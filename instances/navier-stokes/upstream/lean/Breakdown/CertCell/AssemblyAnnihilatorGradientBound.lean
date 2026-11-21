import Breakdown.Defs

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

namespace Breakdown.CertCell.AnnihilatorGradient.Internal

theorem lintegral_affine (H : Space → ℝ≥0∞) (hH : Measurable H) (b : Space) {c : ℝ} (hc : c ≠ 0) :
    ∫⁻ y, H (b + c • y) = ENNReal.ofReal |(c ^ 3)⁻¹| * ∫⁻ y, H y := by
  have h1 : ∫⁻ y, H (b + c • y) = ∫⁻ y, H (b + y) ∂(Measure.map (c • ·) volume) := by
    exact (lintegral_map (f := fun y => H (b + y)) (hH.comp (measurable_const_add b))
      (measurable_const_smul c)).symm
  rw [h1, Measure.map_addHaar_smul volume hc, finrank_euclideanSpace_fin, lintegral_smul_measure,
    lintegral_add_left_eq_self, smul_eq_mul]

theorem lintegral_affine_le (H : Space → ℝ≥0∞) (hH : Measurable H) (b : Space) {c : ℝ} (hc1 : 1 / 2 ≤ c) : ∫⁻ y, H (b + c • y) ≤ 8 * ∫⁻ y, H y := by
  have hc : c ≠ 0 := by intro h; rw [h] at hc1; norm_num at hc1
  rw [lintegral_affine H hH b hc]
  gcongr
  have hc3 : (1 : ℝ) / 8 ≤ c ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) hc1 3]
  have hpos : 0 < c ^ 3 := by linarith
  rw [abs_of_pos (inv_pos.mpr hpos)]
  calc ENNReal.ofReal (c ^ 3)⁻¹ ≤ ENNReal.ofReal 8 := by
        apply ENNReal.ofReal_le_ofReal
        rw [inv_le_comm₀ hpos (by norm_num)]
        linarith
    _ = 8 := by norm_num

theorem key_bound (H : Space → ℝ≥0∞) (hH : Measurable H) (R : ℝ) (hR : 1 ≤ R) :
    ∫⁻ x in closedBall (0 : Space) R, ∫⁻ a in closedBall (0 : Space) 1, ∫⁻ s in Ioc (0 : ℝ) 1,
        H (a + s • (x - a))
      ≤ 8 * volume (closedBall (0 : Space) R) * ∫⁻ y, H y := by
  set BR := closedBall (0 : Space) R
  set B1 := closedBall (0 : Space) 1
  have hm : Measurable (fun p : (Space × ℝ) × Space => H (p.2 + p.1.2 • (p.1.1 - p.2))) :=
    hH.comp (by fun_prop)
  have step1 : ∀ x : Space, ∫⁻ a in B1, ∫⁻ s in Ioc (0 : ℝ) 1, H (a + s • (x - a))
      = ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ a in B1, H (a + s • (x - a)) := by
    intro x
    refine lintegral_lintegral_swap ?_
    exact (hH.comp (by fun_prop)).aemeasurable
  simp_rw [step1]
  have hm2 : Measurable (fun p : Space × ℝ => ∫⁻ a in B1, H (a + p.2 • (p.1 - a))) :=
    hm.lintegral_prod_right'
  rw [lintegral_lintegral_swap (f := fun x s => ∫⁻ a in B1, H (a + s • (x - a))) hm2.aemeasurable]
  have hJ : ∀ s ∈ Ioc (0 : ℝ) 1, ∫⁻ x in BR, ∫⁻ a in B1, H (a + s • (x - a))
      ≤ 8 * volume BR * ∫⁻ y, H y := by
    intro s hs
    by_cases hs2 : s ≤ 1 / 2
    · have hin : ∀ x, ∫⁻ a in B1, H (a + s • (x - a)) ≤ 8 * ∫⁻ y, H y := by
        intro x
        calc ∫⁻ a in B1, H (a + s • (x - a)) ≤ ∫⁻ a, H (a + s • (x - a)) := setLIntegral_le_lintegral _ _
          _ = ∫⁻ a, H (s • x + (1 - s) • a) := by
              congr 1
              funext a
              congr 1
              simp only [smul_sub, sub_smul, one_smul]
              abel
          _ ≤ 8 * ∫⁻ y, H y := lintegral_affine_le H hH _ (by linarith)
      calc ∫⁻ x in BR, ∫⁻ a in B1, H (a + s • (x - a)) ≤ ∫⁻ x in BR, 8 * ∫⁻ y, H y :=
            lintegral_mono fun x => hin x
        _ = 8 * volume BR * ∫⁻ y, H y := by
            rw [setLIntegral_const]
            ring
    · rw [not_le] at hs2
      have hmx : Measurable (fun p : Space × Space => H (p.2 + s • (p.1 - p.2))) := hH.comp (by fun_prop)
      rw [lintegral_lintegral_swap hmx.aemeasurable]
      have hin : ∀ a, ∫⁻ x in BR, H (a + s • (x - a)) ≤ 8 * ∫⁻ y, H y := by
        intro a
        calc ∫⁻ x in BR, H (a + s • (x - a)) ≤ ∫⁻ x, H (a + s • (x - a)) := setLIntegral_le_lintegral _ _
          _ = ∫⁻ x, H ((a - s • a) + s • x) := by
              congr 1
              funext x
              congr 1
              simp only [smul_sub]
              abel
          _ ≤ 8 * ∫⁻ y, H y := lintegral_affine_le H hH _ hs2.le
      calc ∫⁻ a in B1, ∫⁻ x in BR, H (a + s • (x - a)) ≤ ∫⁻ a in B1, 8 * ∫⁻ y, H y :=
            lintegral_mono fun a => hin a
        _ = 8 * volume B1 * ∫⁻ y, H y := by
            rw [setLIntegral_const]
            ring
        _ ≤ 8 * volume BR * ∫⁻ y, H y := by
            gcongr
            exact closedBall_subset_closedBall hR
  calc ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ x in BR, ∫⁻ a in B1, H (a + s • (x - a))
      ≤ ∫⁻ s in Ioc (0 : ℝ) 1, 8 * volume BR * ∫⁻ y, H y := setLIntegral_mono' measurableSet_Ioc hJ
    _ = 8 * volume BR * ∫⁻ y, H y := by
        rw [setLIntegral_const, Real.volume_Ioc]
        simp

end Breakdown.CertCell.AnnihilatorGradient.Internal
