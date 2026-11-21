import Breakdown.Frac.StOperator

open scoped ContDiff
open MeasureTheory Metric Set

noncomputable section

namespace Breakdown.FracInternal

theorem integrableOn_ball_norm_rpow {s : ℝ} (hs : -3 < s) :
    IntegrableOn (fun z : Space => ‖z‖ ^ s) (ball (0 : Space) 1) := by
  rw [integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => y ^ s)]
  have h : IntegrableOn (fun y : ℝ => y ^ (s + 2)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioo
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  rw [Real.rpow_add hy.1, Real.rpow_two, mul_comm]

theorem integrableOn_compl_ball_norm_rpow {s : ℝ} (hs : s < -3) :
    IntegrableOn (fun z : Space => ‖z‖ ^ s) (ball (0 : Space) 1)ᶜ := by
  have hint : Integrable (fun z : Space => (2 : ℝ) ^ (-s) * (1 + ‖z‖) ^ (-(-s))) :=
    (integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)).const_mul _
  refine hint.integrableOn.mono' (measurable_norm.pow_const s).aestronglyMeasurable.restrict
    (ae_restrict_of_forall_mem measurableSet_ball.compl fun z hz => ?_)
  have hz1 : 1 ≤ ‖z‖ := by simpa using hz
  have hle : ‖z‖ ^ s ≤ ((1 + ‖z‖) / 2) ^ s :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), neg_neg,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.div_rpow (by positivity) (by norm_num)] at hle
  rw [div_eq_mul_inv, mul_comm] at hle
  exact hle

end Breakdown.FracInternal

namespace Breakdown

open FracInternal

theorem remainderIntegrable_of (h1 : RemainderBoundStatement) : RemainderIntegrableStatement := by
  intro α hα1 hα2 v hv hv2 x
  have hv3 : ContDiff ℝ 3 v := hv.of_le (WithTop.coe_le_coe.mpr le_top)
  have hvc : Continuous v := hv.continuous
  have hsh : Continuous (fun z : Space => v (x + z)) := hvc.comp (continuous_const.add continuous_id)
  have hT : Continuous (fun z : Space => iteratedFDeriv ℝ 2 v x ![z, z]) := by fun_prop
  have hRc : Continuous (fun z => secondOrderRemainder v x z) := by
    unfold secondOrderRemainder
    exact ((hsh.sub continuous_const).sub (fderiv ℝ v x).continuous).sub (show Continuous fun z : Space => (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 v x ![z, z] from by fun_prop)
  have hKm : Measurable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α))) := measurable_norm.pow_const _
  have hFm : AEStronglyMeasurable
      (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v x z) volume :=
    hKm.aestronglyMeasurable.smul hRc.aestronglyMeasurable
  have hnormF : ∀ z : Space, ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v x z‖ =
      ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder v x z‖ := by
    intro z
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  obtain ⟨C, hC⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn
    (hv.continuous_iteratedFDeriv (m := 3) (WithTop.coe_le_coe.mpr le_top)).continuousOn
  have hnear : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v x z)
      (ball 0 1) := by
    refine ((integrableOn_ball_norm_rpow (s := -(2 * α)) (by linarith)).const_mul C).mono'
      hFm.restrict (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
    rw [hnormF]
    have hz1 : ‖z‖ < 1 := by simpa using hz
    have hR := h1 v hv3 x z C (fun y hy => hC y (closedBall_subset_closedBall hz1.le hy))
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [norm_zero, Real.zero_rpow (by linarith : -(3 + 2 * α) ≠ 0),
        Real.zero_rpow (by linarith : -(2 * α) ≠ 0)]
      simp
    · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
      calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder v x z‖
          ≤ ‖z‖ ^ (-(3 + 2 * α)) * (C * ‖z‖ ^ 3) :=
            mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hpos.le _)
        _ = C * ‖z‖ ^ (-(2 * α)) := by
            rw [show -(2 * α) = -(3 + 2 * α) + ((3 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_add hpos, Real.rpow_natCast]
            ring
  have hfar0 : ∀ z : Space, 1 ≤ ‖z‖ → ‖secondOrderRemainder v x z‖ ≤
      ‖v (x + z)‖ + (‖v x‖ + ‖fderiv ℝ v x‖ + ‖iteratedFDeriv ℝ 2 v x‖) * ‖z‖ ^ 2 := by
    intro z hz
    have h2 : ‖iteratedFDeriv ℝ 2 v x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 v x‖ * (‖z‖ * ‖z‖) := by
      have := (iteratedFDeriv ℝ 2 v x).le_opNorm ![z, z]
      simpa [Fin.prod_univ_two] using this
    have h1' : ‖fderiv ℝ v x z‖ ≤ ‖fderiv ℝ v x‖ * ‖z‖ := (fderiv ℝ v x).le_opNorm z
    have hs : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 v x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 v x ![z, z]‖ := by
      rw [norm_smul]
      have := norm_nonneg (iteratedFDeriv ℝ 2 v x ![z, z])
      norm_num
      linarith
    have e := norm_sub_le (v (x + z) - v x - fderiv ℝ v x z)
      ((1 / 2 : ℝ) • iteratedFDeriv ℝ 2 v x ![z, z])
    have e2 := norm_sub_le (v (x + z) - v x) (fderiv ℝ v x z)
    have e3 := norm_sub_le (v (x + z)) (v x)
    have hz2 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
    have hz3 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
    have t1 : ‖v x‖ ≤ ‖v x‖ * ‖z‖ ^ 2 := by nlinarith [norm_nonneg (v x)]
    have t2 : ‖fderiv ℝ v x‖ * ‖z‖ ≤ ‖fderiv ℝ v x‖ * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hz2 (norm_nonneg _)
    have t3 : ‖z‖ * ‖z‖ = ‖z‖ ^ 2 := by ring
    rw [t3] at h2
    unfold secondOrderRemainder
    nlinarith
  have hW : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * ‖v (x + z)‖)
      (ball (0 : Space) 1)ᶜ := by
    have hwm : AEStronglyMeasurable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * ‖v (x + z)‖) volume :=
      hKm.aestronglyMeasurable.mul hsh.norm.aestronglyMeasurable
    rcases hv2 with hL | ⟨B, hB⟩
    · have hw : MemLp (fun z : Space => v (x + z)) 2 volume :=
        hL.comp_measurePreserving (measurePreserving_add_left volume x)
      have hw2 : Integrable (fun z : Space => ‖v (x + z)‖ ^ 2) volume :=
        (memLp_two_iff_integrable_sq_norm hsh.aestronglyMeasurable).1 hw
      have hK2 : IntegrableOn (fun z : Space => ‖z‖ ^ (-(6 + 4 * α))) (ball (0 : Space) 1)ᶜ :=
        integrableOn_compl_ball_norm_rpow (by linarith)
      refine (hK2.add hw2.integrableOn).mono' hwm.restrict
        (ae_restrict_of_forall_mem measurableSet_ball.compl fun z hz => ?_)
      have hsq : ‖z‖ ^ (-(6 + 4 * α)) = (‖z‖ ^ (-(3 + 2 * α))) ^ 2 := by
        rw [← Real.rpow_mul_natCast (norm_nonneg _)]
        congr 1
        push_cast
        ring
      have hk0 := Real.rpow_nonneg (norm_nonneg z) (-(3 + 2 * α))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk0 (norm_nonneg _))]
      simp only [Pi.add_apply]
      rw [hsq]
      nlinarith [sq_nonneg (‖z‖ ^ (-(3 + 2 * α)) - ‖v (x + z)‖), norm_nonneg (v (x + z))]
    · refine ((integrableOn_compl_ball_norm_rpow (s := -(3 + 2 * α)) (by linarith)).const_mul B).mono'
        hwm.restrict (ae_restrict_of_forall_mem measurableSet_ball.compl fun z hz => ?_)
      have hk0 := Real.rpow_nonneg (norm_nonneg z) (-(3 + 2 * α))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk0 (norm_nonneg _))]
      nlinarith [hB (x + z)]
  have hfar : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder v x z)
      (ball (0 : Space) 1)ᶜ := by
    have hP := (integrableOn_compl_ball_norm_rpow (s := -(1 + 2 * α)) (by linarith)).const_mul
      (‖v x‖ + ‖fderiv ℝ v x‖ + ‖iteratedFDeriv ℝ 2 v x‖)
    refine (hW.add hP).mono' hFm.restrict
      (ae_restrict_of_forall_mem measurableSet_ball.compl fun z hz => ?_)
    have hz1 : 1 ≤ ‖z‖ := by simpa using hz
    have hpos : 0 < ‖z‖ := by linarith
    rw [hnormF]
    have hb := hfar0 z hz1
    have hk : ‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 2 = ‖z‖ ^ (-(1 + 2 * α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
      congr 1
      push_cast
      ring
    simp only [Pi.add_apply]
    calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder v x z‖
        ≤ ‖z‖ ^ (-(3 + 2 * α)) *
          (‖v (x + z)‖ + (‖v x‖ + ‖fderiv ℝ v x‖ + ‖iteratedFDeriv ℝ 2 v x‖) * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hpos.le _)
      _ = _ := by rw [← hk]; ring
  have h := hnear.union hfar
  rwa [union_compl_self, integrableOn_univ] at h

end Breakdown
