import Breakdown.Uniqueness.StressSplit

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem abs_double_sum_le (v : Space) (H : Fin 3 → Fin 3 → ℝ) :
    |∑ i, ∑ j, v i * v j * H i j| ≤ ‖v‖ ^ 2 * Real.sqrt (∑ i, ∑ j, H i j ^ 2) := by
  have hcs : (∑ i, ∑ j, v i * v j * H i j) ^ 2 ≤
      (∑ i, ∑ j, (v i * v j) ^ 2) * ∑ i, ∑ j, H i j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
      (fun p => v p.1 * v p.2) (fun p => H p.1 p.2)
    simpa only [Fintype.sum_prod_type] using h
  have hv : ∑ i, ∑ j, (v i * v j) ^ 2 = (‖v‖ ^ 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, sq (∑ i, v i ^ 2), Finset.sum_mul_sum]
    simp only [mul_pow]
  rw [hv] at hcs
  have hH : 0 ≤ ∑ i, ∑ j, H i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  calc _ ≤ Real.sqrt ((‖v‖ ^ 2) ^ 2 * ∑ i, ∑ j, H i j ^ 2) := Real.abs_le_sqrt hcs
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

private theorem hasCompactSupport_of_cutoff {r : ℝ} (hr : 0 < r) {φ : Space → ℝ}
    (h : ∀ x, radialCutoff r x = 0 → φ x = 0) : HasCompactSupport φ :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * r)) fun x hx => by
    have : 2 * r ≤ ‖x‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      exact hx.le
    exact h x (radialCutoff_eq_zero hr this)

private theorem final_bound {a b G X A c r L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hbA : b ≤ A ^ 2)
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hr : 0 < r) (hG0 : 0 ≤ G) (hG : G ≤ (c / r) ^ 2 * b)
    (hX0 : 0 ≤ X) (hX : X ≤ a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ))
    (hL : L ≤ 4 * (X ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ))) :
    L ≤ 4 * c * (a ^ (1 / 6 : ℝ)) ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by
  have h1 : X ^ (1 / 2 : ℝ) ≤ a ^ (1 / 4 : ℝ) * A ^ (1 / 2 : ℝ) := by
    calc X ^ (1 / 2 : ℝ) ≤ (a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hX0 hX (by norm_num)
      _ = a ^ (1 / 4 : ℝ) * b ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha,
            ← Real.rpow_mul hb]
          norm_num
      _ ≤ a ^ (1 / 4 : ℝ) * A ^ (1 / 2 : ℝ) := by
          gcongr
          calc b ^ (1 / 4 : ℝ) ≤ (A ^ 2) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hb hbA (by norm_num)
            _ = A ^ (1 / 2 : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
                norm_num
  have h2 : G ^ (1 / 2 : ℝ) ≤ c / r * A := by
    have hcr : 0 ≤ c / r * A := by positivity
    calc G ^ (1 / 2 : ℝ) ≤ ((c / r * A) ^ 2) ^ (1 / 2 : ℝ) := by
          apply Real.rpow_le_rpow hG0 _ (by norm_num)
          calc G ≤ (c / r) ^ 2 * b := hG
            _ ≤ (c / r) ^ 2 * A ^ 2 := by gcongr
            _ = (c / r * A) ^ 2 := by ring
      _ = c / r * A := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hcr]
          norm_num
  have h3 : (a ^ (1 / 6 : ℝ)) ^ (3 / 2 : ℝ) = a ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_mul ha]
    norm_num
  have h4 : A ^ (3 / 2 : ℝ) = A ^ (1 / 2 : ℝ) * A := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add' hA (by norm_num), Real.rpow_one]
  have hX' : 0 ≤ X ^ (1 / 2 : ℝ) := Real.rpow_nonneg hX0 _
  have hG' : 0 ≤ G ^ (1 / 2 : ℝ) := Real.rpow_nonneg hG0 _
  calc L ≤ 4 * (X ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ)) := hL
    _ ≤ 4 * ((a ^ (1 / 4 : ℝ) * A ^ (1 / 2 : ℝ)) * (c / r * A)) := by gcongr
    _ = 4 * c * (a ^ (1 / 6 : ℝ)) ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by
        rw [h3, h4]
        field_simp

theorem near_stress_le : ∃ c : ℝ, ∀ (A : ℝ) (w : Space → Space),
    IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
      |∫ x, ∑ i, ∑ j, w x i * w x j *
          (4 * radialCutoff r x ^ 3 * FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x)| ≤
        c * cutoffSixthNorm r w ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by
  obtain ⟨c₁, hc₁⟩ := norm_fderiv_radialCutoff_le
  have hc₁0 : 0 ≤ c₁ := by
    have h := hc₁ 1 one_pos 0
    rw [div_one] at h
    exact (norm_nonneg _).trans h
  refine ⟨4 * c₁, fun A w hw r hr1 => ?_⟩
  have hr : 0 < r := lt_of_lt_of_le one_pos hr1
  have hwc : Continuous w := hw.smooth.continuous
  have hηc : Continuous (radialCutoff r) := (contDiff_radialCutoff hr).continuous
  have hγs : ContDiff ℝ ∞ (cutoffFlux r w) := contDiff_cutoffFlux hr hw.smooth
  have hγc : HasCompactSupport (cutoffFlux r w) := hasCompactSupport_cutoffFlux hr w
  have hnm : AEStronglyMeasurable (fun x => ‖w x‖ ^ 2) volume :=
    ((continuous_norm.comp hwc).pow 2).aestronglyMeasurable
  have hn0 : 0 ≤ᵐ[volume] fun x => ‖w x‖ ^ 2 :=
    Filter.Eventually.of_forall fun x => (by positivity : (0 : ℝ) ≤ ‖w x‖ ^ 2)
  have hWi : Integrable (fun x => ‖w x‖ ^ 2) volume :=
    ⟨hnm, (hasFiniteIntegral_iff_ofReal hn0).2 (lt_of_le_of_lt hw.energy ENNReal.ofReal_lt_top)⟩
  have hWA : ∫ x, ‖w x‖ ^ 2 ≤ A ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae hn0 hnm]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hw.energy
  have hW0 : 0 ≤ ∫ x, ‖w x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hQi := FundSol.integrable_sum_sq_secondPartial hγs hγc
  have hQe := FundSol.integral_sum_sq_secondPartial hγs hγc
  have hQ0 : ∀ x, 0 ≤ ∑ i, ∑ j, FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x ^ 2 :=
    fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hFm : AEStronglyMeasurable (fun x => Real.sqrt
      (∑ i, ∑ j, FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x ^ 2)) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hQi.aestronglyMeasurable
  have hFL : MemLp (fun x => Real.sqrt
      (∑ i, ∑ j, FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x ^ 2)) 2 volume := by
    refine (memLp_two_iff_integrable_sq hFm).2 (hQi.congr ?_)
    exact Filter.Eventually.of_forall fun x => (Real.sq_sqrt (hQ0 x)).symm
  have hfc : Continuous (fun x => radialCutoff r x ^ 3 * ‖w x‖ ^ 2) :=
    (hηc.pow 3).mul ((continuous_norm.comp hwc).pow 2)
  have hfL : MemLp (fun x => radialCutoff r x ^ 3 * ‖w x‖ ^ 2) 2 volume :=
    hfc.memLp_of_hasCompactSupport (hasCompactSupport_of_cutoff hr fun x hx => by simp [hx])
  have hkc : Continuous (fun x => (radialCutoff r x ^ 2 * ‖w x‖) ^ 3) :=
    ((hηc.pow 2).mul (continuous_norm.comp hwc)).pow 3
  have hkL : MemLp (fun x => (radialCutoff r x ^ 2 * ‖w x‖) ^ 3) 2 volume :=
    hkc.memLp_of_hasCompactSupport (hasCompactSupport_of_cutoff hr fun x hx => by simp [hx])
  have hnL : MemLp (fun x => ‖w x‖) 2 volume :=
    (memLp_two_iff_integrable_sq (continuous_norm.comp hwc).aestronglyMeasurable).2 hWi
  have hprod : Integrable (fun x => 4 * ((radialCutoff r x ^ 3 * ‖w x‖ ^ 2) * Real.sqrt
      (∑ i, ∑ j, FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x ^ 2))) volume :=
    (hfL.integrable_mul hFL).const_mul 4
  have hpt : ∀ x, |∑ i, ∑ j, w x i * w x j *
      (4 * radialCutoff r x ^ 3 * FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x)| ≤
      4 * ((radialCutoff r x ^ 3 * ‖w x‖ ^ 2) * Real.sqrt
        (∑ i, ∑ j, FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x ^ 2)) := by
    intro x
    have he : ∑ i, ∑ j, w x i * w x j *
        (4 * radialCutoff r x ^ 3 * FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x) =
        (4 * radialCutoff r x ^ 3) * ∑ i, ∑ j, w x i * w x j *
          FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h4 : 0 ≤ 4 * radialCutoff r x ^ 3 := by
      have := radialCutoff_nonneg r x
      positivity
    rw [he, abs_mul, abs_of_nonneg h4]
    calc 4 * radialCutoff r x ^ 3 * |∑ i, ∑ j, w x i * w x j *
          FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x|
        ≤ 4 * radialCutoff r x ^ 3 * (‖w x‖ ^ 2 * Real.sqrt
          (∑ i, ∑ j, FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x ^ 2)) :=
          mul_le_mul_of_nonneg_left (abs_double_sum_le (w x) _) h4
      _ = _ := by ring
  have hstep1 : |∫ x, ∑ i, ∑ j, w x i * w x j *
      (4 * radialCutoff r x ^ 3 * FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x)| ≤
      ∫ x, 4 * ((radialCutoff r x ^ 3 * ‖w x‖ ^ 2) * Real.sqrt
        (∑ i, ∑ j, FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x ^ 2)) := by
    refine (abs_integral_le_integral_abs).trans ?_
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hprod
      (Filter.Eventually.of_forall hpt)
  have hprod1 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (f := fun x => radialCutoff r x ^ 3 * ‖w x‖ ^ 2)
    (g := fun x => Real.sqrt
      (∑ i, ∑ j, FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x ^ 2))
    (Filter.Eventually.of_forall fun x => by
      have := radialCutoff_nonneg r x
      show (0 : ℝ) ≤ radialCutoff r x ^ 3 * ‖w x‖ ^ 2
      positivity)
    (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (by rw [ENNReal.ofReal_ofNat]; exact hfL) (by rw [ENNReal.ofReal_ofNat]; exact hFL)
  have hprod2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (f := fun x => (radialCutoff r x ^ 2 * ‖w x‖) ^ 3)
    (g := fun x => ‖w x‖)
    (Filter.Eventually.of_forall fun x => by
      have := radialCutoff_nonneg r x
      show (0 : ℝ) ≤ (radialCutoff r x ^ 2 * ‖w x‖) ^ 3
      positivity)
    (Filter.Eventually.of_forall fun x => norm_nonneg _)
    (by rw [ENNReal.ofReal_ofNat]; exact hkL) (by rw [ENNReal.ofReal_ofNat]; exact hnL)
  simp only [Real.rpow_two] at hprod1 hprod2
  have hsq1 : ∀ x, (radialCutoff r x ^ 3 * ‖w x‖ ^ 2) ^ 2 =
      (radialCutoff r x ^ 2 * ‖w x‖) ^ 3 * ‖w x‖ := fun x => by ring
  have hsq2 : ∀ x, ((radialCutoff r x ^ 2 * ‖w x‖) ^ 3) ^ 2 =
      (radialCutoff r x ^ 2 * ‖w x‖) ^ 6 := fun x => by ring
  have hsq3 : ∀ x, Real.sqrt
      (∑ i, ∑ j, FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x ^ 2) ^ 2 =
      ∑ i, ∑ j, FundSol.secondPartial (FundSol.potential (cutoffFlux r w)) i j x ^ 2 :=
    fun x => Real.sq_sqrt (hQ0 x)
  simp only [hsq1, hsq3] at hprod1
  simp only [hsq2] at hprod2
  rw [hQe] at hprod1
  have hγ : ∫ x, cutoffFlux r w x ^ 2 ≤ (c₁ / r) ^ 2 * ∫ x, ‖w x‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (hWi.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    have h1 : |cutoffFlux r w x| ≤ c₁ / r * ‖w x‖ := by
      rw [cutoffFlux, ← Real.norm_eq_abs]
      exact ((fderiv ℝ (radialCutoff r) x).le_opNorm (w x)).trans
        (mul_le_mul_of_nonneg_right (hc₁ r hr x) (norm_nonneg _))
    calc cutoffFlux r w x ^ 2 = |cutoffFlux r w x| ^ 2 := (sq_abs _).symm
      _ ≤ (c₁ / r * ‖w x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (c₁ / r) ^ 2 * ‖w x‖ ^ 2 := by ring
  have hS0 : 0 ≤ ∫ x, (radialCutoff r x ^ 2 * ‖w x‖) ^ 6 :=
    integral_nonneg fun x => by
      have := radialCutoff_nonneg r x
      positivity
  have hX0 : 0 ≤ ∫ x, (radialCutoff r x ^ 2 * ‖w x‖) ^ 3 * ‖w x‖ :=
    integral_nonneg fun x => by
      have := radialCutoff_nonneg r x
      positivity
  have hG0 : 0 ≤ ∫ x, cutoffFlux r w x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have key := final_bound hS0 hW0 hWA hw.nonneg hc₁0 hr hG0 hγ hX0 hprod2
    (hstep1.trans (by rw [integral_const_mul]; gcongr))
  unfold cutoffSixthNorm
  calc _ ≤ _ := key
    _ = _ := by ring

end Breakdown
