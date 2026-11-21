import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.FarField

private lemma weight_le_one_of_pos {a γ : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (z : Space) :
    (1 + ‖z‖ / a) ^ (-γ) ≤ 1 := by
  have h0 : 0 ≤ ‖z‖ / a := div_nonneg (norm_nonneg z) ha.le
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

private lemma weight_nonneg_of_pos {a : ℝ} (ha : 0 < a) (γ : ℝ) (z : Space) :
    0 ≤ (1 + ‖z‖ / a) ^ (-γ) := by
  have h0 : 0 ≤ ‖z‖ / a := div_nonneg (norm_nonneg z) ha.le
  exact Real.rpow_nonneg (by linarith) _

private lemma weight_le_far_of_norm {a γ R : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hR : 0 < R)
    (z : Space) (hz : R / 2 ≤ ‖z‖) :
    (1 + ‖z‖ / a) ^ (-γ) ≤ 2 ^ γ * min 1 ((a / R) ^ γ) := by
  have h2 : (1 : ℝ) ≤ 2 ^ γ := Real.one_le_rpow (by norm_num) hγ
  have hpos : 0 < R / 2 / a := by positivity
  have hle : R / 2 / a ≤ 1 + ‖z‖ / a := by
    have h1 : R / 2 / a ≤ ‖z‖ / a := by gcongr
    linarith
  have hfar : (1 + ‖z‖ / a) ^ (-γ) ≤ 2 ^ γ * (a / R) ^ γ := by
    calc (1 + ‖z‖ / a) ^ (-γ) ≤ (R / 2 / a) ^ (-γ) :=
          Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
      _ = (2 * (a / R)) ^ γ := by
          rw [Real.rpow_neg hpos.le, ← Real.inv_rpow hpos.le]
          congr 1
          field_simp
      _ = 2 ^ γ * (a / R) ^ γ := Real.mul_rpow (by norm_num) (by positivity)
  rcases le_total 1 ((a / R) ^ γ) with h | h
  · rw [min_eq_left h, mul_one]
    exact (weight_le_one_of_pos ha hγ z).trans h2
  · rw [min_eq_right h]
    exact hfar

private lemma kernel_le_of_norm_lt {y z : Space} {t : ℝ} (ht : 0 ≤ t)
    (hz : ‖z‖ < ‖y‖ / 2) :
    ((‖y - z‖ + t) ^ 4)⁻¹ ≤ 16 / (‖y‖ + t) ^ 4 := by
  have hR : 0 < ‖y‖ := by linarith [norm_nonneg z]
  have hb : 0 < (‖y‖ + t) / 2 := by positivity
  have hle : (‖y‖ + t) / 2 ≤ ‖y - z‖ + t := by linarith [norm_sub_norm_le y z]
  calc ((‖y - z‖ + t) ^ 4)⁻¹ ≤ (((‖y‖ + t) / 2) ^ 4)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hb.le hle 4)
    _ = 16 / (‖y‖ + t) ^ 4 := by
        rw [div_pow, inv_div]
        norm_num

private lemma half_radius_factor {a m R : ℝ} (ha : 0 < a) (hm : m ≤ 3)
    (hR : 0 < R) :
    (R / 2) ^ 3 * min 1 ((a / (R / 2)) ^ m) ≤ R ^ 3 * min 1 ((a / R) ^ m) := by
  have e : (a / (R / 2)) ^ m = 2 ^ m * (a / R) ^ m := by
    rw [div_div_eq_mul_div, show a * 2 / R = 2 * (a / R) by ring]
    exact Real.mul_rpow (by norm_num) (by positivity)
  have h8 : (2 : ℝ) ^ m ≤ 8 := by
    calc (2 : ℝ) ^ m ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hm
      _ = 8 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
  have hx : 0 ≤ (a / R) ^ m := Real.rpow_nonneg (by positivity) _
  have hmin : min 1 ((a / (R / 2)) ^ m) ≤ 8 * min 1 ((a / R) ^ m) := by
    rw [e]
    rcases le_total 1 ((a / R) ^ m) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by norm_num)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right h8 hx)
  calc (R / 2) ^ 3 * min 1 ((a / (R / 2)) ^ m)
      ≤ (R / 2) ^ 3 * (8 * min 1 ((a / R) ^ m)) :=
        mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = R ^ 3 * min 1 ((a / R) ^ m) := by ring

theorem innerSplitBound_of_mass : KernelMassBound → RadialWeightBound → InnerSplitBound := by
  intro hMass hRad γ hγ hγ3
  obtain ⟨C2, hC2⟩ := hRad γ hγ hγ3
  refine ⟨5 * 2 ^ γ + 16 * max C2 0, fun τ hτ y => ?_⟩
  have ht : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have ha : 0 < Real.sqrt (1 + τ) := Real.sqrt_pos.2 (by linarith)
  have h2γ : (1 : ℝ) ≤ 2 ^ γ := Real.one_le_rpow (by norm_num) hγ
  have hc0 : (0 : ℝ) ≤ max C2 0 := le_max_right _ _
  obtain ⟨hkI, hkM⟩ := hMass τ hτ y
  have hk0 : ∀ z : Space, 0 ≤ ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ := fun z => by positivity
  have hwm : Measurable (fun z : Space => (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)) := by
    fun_prop
  have hkm : Measurable (fun z : Space => ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹) := by
    fun_prop
  have hkw : ∀ z : Space, ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)
      ≤ ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ := fun z =>
    mul_le_of_le_one_right (hk0 z) (weight_le_one_of_pos ha hγ z)
  have hkwI : Integrable (fun z : Space =>
      ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)) := by
    refine hkI.mono' (hkm.mul hwm).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk0 z) (weight_nonneg_of_pos ha γ z))]
    exact hkw z
  refine ⟨hkwI, ?_, fun hy => ?_⟩
  · unfold kernelWeightIntegral
    calc _ ≤ ∫ z, ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ := integral_mono hkwI hkI hkw
      _ ≤ 5 * (Real.sqrt τ)⁻¹ := hkM
      _ ≤ (5 * 2 ^ γ + 16 * max C2 0) * (Real.sqrt τ)⁻¹ :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hR : 0 < ‖y‖ := by linarith
    have hB : MeasurableSet (Metric.ball (0 : Space) (‖y‖ / 2)) := measurableSet_ball
    have hwB : IntegrableOn (fun z : Space => (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ))
        (Metric.ball (0 : Space) (‖y‖ / 2)) := by
      have h1 : IntegrableOn (fun _ : Space => (1 : ℝ)) (Metric.ball (0 : Space) (‖y‖ / 2)) :=
        integrableOn_const measure_ball_lt_top.ne
      refine Integrable.mono' h1 hwm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg_of_pos ha γ z)]
      exact weight_le_one_of_pos ha hγ z
    have hin : ∫ z in Metric.ball (0 : Space) (‖y‖ / 2),
        ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)
        ≤ 16 * max C2 0 * nearMajorant γ τ ‖y‖ := by
      calc _ ≤ ∫ z in Metric.ball (0 : Space) (‖y‖ / 2),
            16 / (‖y‖ + Real.sqrt τ) ^ 4 * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ) :=
            setIntegral_mono_on hkwI.integrableOn (hwB.const_mul _) hB (fun z hz =>
              mul_le_mul_of_nonneg_right
                (kernel_le_of_norm_lt ht.le (mem_ball_zero_iff.1 hz))
                (weight_nonneg_of_pos ha γ z))
        _ = 16 / (‖y‖ + Real.sqrt τ) ^ 4 * ∫ z in Metric.ball (0 : Space) (‖y‖ / 2),
            (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ) := integral_const_mul _ _
        _ ≤ 16 / (‖y‖ + Real.sqrt τ) ^ 4 * (C2 * (‖y‖ / 2) ^ 3 *
            min 1 ((Real.sqrt (1 + τ) / (‖y‖ / 2)) ^ min γ 3)) :=
            mul_le_mul_of_nonneg_left (hC2 _ _ ha (by positivity)) (by positivity)
        _ ≤ 16 / (‖y‖ + Real.sqrt τ) ^ 4 * (max C2 0 * (‖y‖ ^ 3 *
            min 1 ((Real.sqrt (1 + τ) / ‖y‖) ^ min γ 3))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [mul_assoc]
            exact (mul_le_mul_of_nonneg_right (le_max_left C2 0) (by positivity)).trans
              (mul_le_mul_of_nonneg_left
                (half_radius_factor ha (min_le_right _ _) hR) hc0)
        _ = 16 * max C2 0 * nearMajorant γ τ ‖y‖ := by
            unfold nearMajorant
            ring
    have hout : ∫ z in (Metric.ball (0 : Space) (‖y‖ / 2))ᶜ,
        ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (1 + ‖z‖ / Real.sqrt (1 + τ)) ^ (-γ)
        ≤ 5 * 2 ^ γ * farMajorant γ τ ‖y‖ := by
      calc _ ≤ ∫ z in (Metric.ball (0 : Space) (‖y‖ / 2))ᶜ,
            ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹ * (2 ^ γ * min 1 ((Real.sqrt (1 + τ) / ‖y‖) ^ γ)) :=
            setIntegral_mono_on hkwI.integrableOn (hkI.mul_const _).integrableOn hB.compl
              (fun z hz => mul_le_mul_of_nonneg_left
                (weight_le_far_of_norm ha hγ hR z
                  (not_lt.1 fun h => hz (mem_ball_zero_iff.2 h))) (hk0 z))
        _ = (∫ z in (Metric.ball (0 : Space) (‖y‖ / 2))ᶜ, ((‖y - z‖ + Real.sqrt τ) ^ 4)⁻¹) *
            (2 ^ γ * min 1 ((Real.sqrt (1 + τ) / ‖y‖) ^ γ)) := integral_mul_const _ _
        _ ≤ (5 * (Real.sqrt τ)⁻¹) * (2 ^ γ * min 1 ((Real.sqrt (1 + τ) / ‖y‖) ^ γ)) :=
            mul_le_mul_of_nonneg_right
              ((setIntegral_le_integral hkI (Eventually.of_forall fun z => hk0 z)).trans hkM)
              (by positivity)
        _ = 5 * 2 ^ γ * farMajorant γ τ ‖y‖ := by
            unfold farMajorant
            ring
    have hfar : 0 ≤ farMajorant γ τ ‖y‖ := by
      unfold farMajorant
      positivity
    have hnear : 0 ≤ nearMajorant γ τ ‖y‖ := by
      unfold nearMajorant
      positivity
    have hsplit := integral_add_compl hB hkwI
    unfold kernelWeightIntegral
    rw [← hsplit]
    have e1 : 0 ≤ 5 * 2 ^ γ * nearMajorant γ τ ‖y‖ := mul_nonneg (by positivity) hnear
    have e2 : 0 ≤ 16 * max C2 0 * farMajorant γ τ ‖y‖ := mul_nonneg (by positivity) hfar
    calc _ ≤ 16 * max C2 0 * nearMajorant γ τ ‖y‖ + 5 * 2 ^ γ * farMajorant γ τ ‖y‖ :=
          add_le_add hin hout
      _ ≤ (5 * 2 ^ γ + 16 * max C2 0) * (farMajorant γ τ ‖y‖ + nearMajorant γ τ ‖y‖) := by
          nlinarith

end Breakdown.FarField
