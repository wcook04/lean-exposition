import Breakdown.Frac.StSymbol
import Breakdown.Frac.OpRemainder
import Breakdown.Frac.OpIntegrable

open scoped ContDiff
open MeasureTheory Metric Set

noncomputable section

namespace Breakdown.FracInternal

theorem rapidDecay_three (φ : SchwartzMap Space Space) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n ≤ 3, ∀ x : Space, (1 + ‖x‖) ^ 4 * ‖iteratedFDeriv ℝ n φ x‖ ≤ C := by
  refine ⟨2 ^ (4, 3).1 * (Finset.Iic ((4 : ℕ), (3 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ, ?_, fun n hn x => ?_⟩
  · exact ((SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (4, 3)) le_rfl (Nat.zero_le _) φ 0).trans'
      (by positivity))
  · exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (4, 3)) le_rfl hn φ x

theorem le_mul_weight {a B : ℝ} (x : Space) (h : (1 + ‖x‖) ^ 4 * a ≤ B) :
    a ≤ B * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have hp : 0 < (1 + ‖x‖) ^ 4 := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_ofNat, ← div_eq_mul_inv, le_div_iff₀ hp]
  linarith

theorem integrable_weight : Integrable (fun x : Space => (1 + ‖x‖) ^ (-(4 : ℝ))) :=
  integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)

end Breakdown.FracInternal

namespace Breakdown

open FracInternal

theorem remainderProductIntegrable : RemainderProductIntegrableStatement := by
  intro α hα1 hα2 φ
  have hφ : ContDiff ℝ ∞ φ := φ.smooth ⊤
  have hφ3 : ContDiff ℝ 3 φ := φ.smooth 3
  obtain ⟨C, hC0, hC⟩ := rapidDecay_three φ
  have hD1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hD2 : Continuous (iteratedFDeriv ℝ 2 φ) :=
    hφ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
  have hRc : Continuous (fun p : Space × Space => secondOrderRemainder φ p.1 p.2) := by
    unfold secondOrderRemainder
    have h1 : Continuous (fun p : Space × Space => φ (p.1 + p.2)) :=
      φ.continuous.comp (continuous_fst.add continuous_snd)
    have h2 : Continuous (fun p : Space × Space => fderiv ℝ φ p.1 p.2) :=
      (hD1.comp continuous_fst).clm_apply continuous_snd
    have h3 : Continuous (fun p : Space × Space => iteratedFDeriv ℝ 2 φ p.1 ![p.2, p.2]) := by
      fun_prop
    have h4 : Continuous (fun p : Space × Space =>
        (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 φ p.1 ![p.2, p.2]) := by fun_prop
    exact ((h1.sub (φ.continuous.comp continuous_fst)).sub h2).sub h4
  have hKm : Measurable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α))) := measurable_norm.pow_const _
  have hFm : AEStronglyMeasurable
      (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder φ p.1 p.2‖)
      (volume.prod volume) :=
    (hKm.comp measurable_snd).aestronglyMeasurable.mul hRc.norm.aestronglyMeasurable
  have hnear : IntegrableOn
      (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder φ p.1 p.2‖)
      (univ ×ˢ ball (0 : Space) 1) (volume.prod volume) := by
    have hg : IntegrableOn (fun p : Space × Space =>
        (16 * C * (1 + ‖p.1‖) ^ (-(4 : ℝ))) * ‖p.2‖ ^ (-(2 * α)))
        (univ ×ˢ ball (0 : Space) 1) (volume.prod volume) := by
      rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
      exact Integrable.mul_prod (integrable_weight.const_mul _)
        (integrableOn_ball_norm_rpow (by linarith))
    refine hg.mono' hFm.restrict
      (ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_ball) ?_)
    rintro ⟨x, z⟩ ⟨-, hz⟩
    have hz1 : ‖z‖ < 1 := by simpa using hz
    have hb : ∀ y ∈ closedBall x ‖z‖, ‖iteratedFDeriv ℝ 3 φ y‖ ≤
        16 * C * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
      intro y hy
      refine le_mul_weight x ?_
      have hxy : ‖x‖ ≤ ‖y‖ + 1 := by
        have := norm_le_norm_add_norm_sub' x y
        rw [mem_closedBall, dist_eq_norm] at hy
        rw [norm_sub_rev] at hy
        linarith
      have h4 : (1 + ‖x‖) ^ 4 ≤ 16 * (1 + ‖y‖) ^ 4 := by
        have : (1 + ‖x‖) ≤ 2 * (1 + ‖y‖) := by linarith [norm_nonneg y]
        calc (1 + ‖x‖) ^ 4 ≤ (2 * (1 + ‖y‖)) ^ 4 :=
              pow_le_pow_left₀ (by positivity) this 4
          _ = 16 * (1 + ‖y‖) ^ 4 := by ring
      calc (1 + ‖x‖) ^ 4 * ‖iteratedFDeriv ℝ 3 φ y‖
          ≤ 16 * (1 + ‖y‖) ^ 4 * ‖iteratedFDeriv ℝ 3 φ y‖ :=
            mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
        _ = 16 * ((1 + ‖y‖) ^ 4 * ‖iteratedFDeriv ℝ 3 φ y‖) := by ring
        _ ≤ 16 * C := by linarith [hC 3 le_rfl y]
    have hR := remainderBound φ hφ3 x z _ hb
    have hk0 := Real.rpow_nonneg (norm_nonneg z) (-(3 + 2 * α))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk0 (norm_nonneg _))]
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [norm_zero, Real.zero_rpow (by linarith : -(3 + 2 * α) ≠ 0),
        Real.zero_rpow (by linarith : -(2 * α) ≠ 0)]
      simp
    · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
      calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder φ x z‖
          ≤ ‖z‖ ^ (-(3 + 2 * α)) * (16 * C * (1 + ‖x‖) ^ (-(4 : ℝ)) * ‖z‖ ^ 3) :=
            mul_le_mul_of_nonneg_left hR hk0
        _ = 16 * C * (1 + ‖x‖) ^ (-(4 : ℝ)) * ‖z‖ ^ (-(2 * α)) := by
            rw [show -(2 * α) = -(3 + 2 * α) + ((3 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_add hpos, Real.rpow_natCast]
            ring
  have hfar0 : ∀ x z : Space, 1 ≤ ‖z‖ → ‖secondOrderRemainder φ x z‖ ≤
      ‖φ (x + z)‖ + 3 * C * (1 + ‖x‖) ^ (-(4 : ℝ)) * ‖z‖ ^ 2 := by
    intro x z hz
    have hw0 : ∀ n ≤ 3, ‖iteratedFDeriv ℝ n φ x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ)) :=
      fun n hn => le_mul_weight x (hC n hn x)
    have a0 := hw0 0 (by norm_num)
    have a1 := hw0 1 (by norm_num)
    have a2 := hw0 2 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at a0
    rw [norm_iteratedFDeriv_one] at a1
    have h2 : ‖iteratedFDeriv ℝ 2 φ x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 φ x‖ * (‖z‖ * ‖z‖) := by
      have := (iteratedFDeriv ℝ 2 φ x).le_opNorm ![z, z]
      simpa [Fin.prod_univ_two] using this
    have h1' : ‖fderiv ℝ φ x z‖ ≤ ‖fderiv ℝ φ x‖ * ‖z‖ := (fderiv ℝ φ x).le_opNorm z
    have hs : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 φ x ![z, z]‖ ≤
        ‖iteratedFDeriv ℝ 2 φ x ![z, z]‖ := by
      rw [norm_smul]
      have := norm_nonneg (iteratedFDeriv ℝ 2 φ x ![z, z])
      norm_num
      linarith
    have e := norm_sub_le (φ (x + z) - φ x - fderiv ℝ φ x z)
      ((1 / 2 : ℝ) • iteratedFDeriv ℝ 2 φ x ![z, z])
    have e2 := norm_sub_le (φ (x + z) - φ x) (fderiv ℝ φ x z)
    have e3 := norm_sub_le (φ (x + z)) (φ x)
    set W := C * (1 + ‖x‖) ^ (-(4 : ℝ)) with hW
    have hW0 : 0 ≤ W := (norm_nonneg _).trans a0
    have hz2 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
    have hz3 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
    have t1 : ‖φ x‖ ≤ W * ‖z‖ ^ 2 := by nlinarith [norm_nonneg (φ x)]
    have t2 : ‖fderiv ℝ φ x‖ * ‖z‖ ≤ W * ‖z‖ ^ 2 := by
      have := mul_le_mul a1 hz2 (norm_nonneg _) hW0
      linarith
    have t3 : ‖iteratedFDeriv ℝ 2 φ x‖ * (‖z‖ * ‖z‖) ≤ W * ‖z‖ ^ 2 := by
      rw [show ‖z‖ * ‖z‖ = ‖z‖ ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right a2 (by positivity)
    unfold secondOrderRemainder
    have : 3 * C * (1 + ‖x‖) ^ (-(4 : ℝ)) * ‖z‖ ^ 2 = 3 * (W * ‖z‖ ^ 2) := by rw [hW]; ring
    rw [this]
    linarith
  have hfar : IntegrableOn
      (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder φ p.1 p.2‖)
      (univ ×ˢ (ball (0 : Space) 1)ᶜ) (volume.prod volume) := by
    have hA : IntegrableOn (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α)) * ‖φ (p.1 + p.2)‖)
        (univ ×ˢ (ball (0 : Space) 1)ᶜ) (volume.prod volume) := by
      rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
      have hm : AEStronglyMeasurable
          (fun p : Space × Space => ‖p.2‖ ^ (-(3 + 2 * α)) * ‖φ (p.1 + p.2)‖)
          (volume.prod (volume.restrict (ball (0 : Space) 1)ᶜ)) :=
        (hKm.comp measurable_snd).aestronglyMeasurable.mul
          (φ.continuous.comp (continuous_fst.add continuous_snd)).norm.aestronglyMeasurable
      refine (integrable_prod_iff' hm).2 ⟨ae_of_all _ fun z => ?_, ?_⟩
      · show Integrable (fun x : Space => ‖z‖ ^ (-(3 + 2 * α)) * ‖φ (x + z)‖) volume
        exact ((φ.integrable.comp_add_right z).norm).const_mul _
      · show Integrable (fun z : Space => ∫ x : Space, ‖‖z‖ ^ (-(3 + 2 * α)) * ‖φ (x + z)‖‖) _
        have he : (fun z : Space => ∫ x : Space, ‖‖z‖ ^ (-(3 + 2 * α)) * ‖φ (x + z)‖‖) =
            fun z => ‖z‖ ^ (-(3 + 2 * α)) * ∫ x : Space, ‖φ x‖ := by
          funext z
          have hk0 := Real.rpow_nonneg (norm_nonneg z) (-(3 + 2 * α))
          simp_rw [norm_mul, norm_norm, Real.norm_eq_abs, abs_of_nonneg hk0]
          rw [integral_const_mul, integral_add_right_eq_self (fun x => ‖φ x‖) z]
        rw [he]
        exact (integrableOn_compl_ball_norm_rpow (by linarith)).mul_const _
    have hB : IntegrableOn (fun p : Space × Space =>
        (3 * C * (1 + ‖p.1‖) ^ (-(4 : ℝ))) * ‖p.2‖ ^ (-(1 + 2 * α)))
        (univ ×ˢ (ball (0 : Space) 1)ᶜ) (volume.prod volume) := by
      rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
      exact Integrable.mul_prod (integrable_weight.const_mul _)
        (integrableOn_compl_ball_norm_rpow (by linarith))
    refine (hA.add hB).mono' hFm.restrict
      (ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_ball.compl) ?_)
    rintro ⟨x, z⟩ ⟨-, hz⟩
    have hz1 : 1 ≤ ‖z‖ := by simpa using hz
    have hpos : 0 < ‖z‖ := by linarith
    have hk0 := Real.rpow_nonneg (norm_nonneg z) (-(3 + 2 * α))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk0 (norm_nonneg _))]
    have hk : ‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 2 = ‖z‖ ^ (-(1 + 2 * α)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
      congr 1
      push_cast
      ring
    simp only [Pi.add_apply]
    calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder φ x z‖
        ≤ ‖z‖ ^ (-(3 + 2 * α)) * (‖φ (x + z)‖ + 3 * C * (1 + ‖x‖) ^ (-(4 : ℝ)) * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hfar0 x z hz1) hk0
      _ = _ := by rw [← hk]; ring
  have h := hnear.union hfar
  rwa [← Set.prod_union, Set.union_compl_self, Set.univ_prod_univ, integrableOn_univ] at h

end Breakdown
