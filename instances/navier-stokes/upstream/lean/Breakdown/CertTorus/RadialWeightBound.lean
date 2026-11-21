import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

namespace RadialWeightInternal

lemma finrank_space : Module.finrank ℝ Space = 3 := by
  simp [Space, finrank_euclideanSpace]

lemma weight_nonneg {a : ℝ} (ha : 0 < a) (γ : ℝ) (z : Space) :
    0 ≤ (1 + ‖z‖ / a) ^ (-γ) :=
  Real.rpow_nonneg (by positivity) _

lemma weight_le_one {a γ : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (z : Space) :
    (1 + ‖z‖ / a) ^ (-γ) ≤ 1 := by
  have h0 : 0 ≤ ‖z‖ / a := div_nonneg (norm_nonneg z) ha.le
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

lemma volume_bound {a γ r : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hr : 0 < r) :
    ∫ z in Metric.ball (0 : Space) r, (1 + ‖z‖ / a) ^ (-γ)
      ≤ volume.real (Metric.ball (0 : Space) 1) * r ^ 3 := by
  have hvol : volume.real (Metric.ball (0 : Space) r)
      = volume.real (Metric.ball (0 : Space) 1) * r ^ 3 := by
    rw [Measure.real, Measure.addHaar_ball volume 0 hr.le, finrank_space, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), mul_comm]
    rfl
  have h1 : ∫ z in Metric.ball (0 : Space) r, (1 + ‖z‖ / a) ^ (-γ)
      ≤ ∫ z in Metric.ball (0 : Space) r, (1 : ℝ) := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun z => weight_nonneg ha γ z)
    · exact (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Space) r)
        continuousOn_const).mono_set
        Metric.ball_subset_closedBall
    · exact Filter.Eventually.of_forall (fun z => weight_le_one ha hγ z)
  rw [setIntegral_const, smul_eq_mul, mul_one, hvol] at h1
  exact h1

lemma pointwise_bound {a γ y : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hy0 : 0 < y) :
    y ^ 2 * (1 + y / a) ^ (-γ) ≤ a ^ γ * y ^ (2 - γ) := by
  have h1 : (1 + y / a) ^ (-γ) ≤ (y / a) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hy0 ha) (by linarith) (by linarith)
  have h2 : (y / a) ^ (-γ) = a ^ γ * y ^ (-γ) := by
    rw [Real.div_rpow hy0.le ha.le, Real.rpow_neg ha.le, div_inv_eq_mul, mul_comm]
  have h3 : y ^ (2 - γ) = y ^ 2 * y ^ (-γ) := by
    rw [sub_eq_add_neg, Real.rpow_add hy0, Real.rpow_two]
  calc y ^ 2 * (1 + y / a) ^ (-γ) ≤ y ^ 2 * (a ^ γ * y ^ (-γ)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2.le) (sq_nonneg y)
    _ = a ^ γ * y ^ (2 - γ) := by rw [h3]; ring

lemma radial_bound {a γ r : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ) (hγ3 : γ < 3) (hr : 0 < r) :
    ∫ z in Metric.ball (0 : Space) r, (1 + ‖z‖ / a) ^ (-γ)
      ≤ 3 * volume.real (Metric.ball (0 : Space) 1) * (a ^ γ * (r ^ (3 - γ) / (3 - γ))) := by
  set h : ℝ → ℝ := fun ρ => (1 + ρ / a) ^ (-γ) with hh
  have e1 : ∫ z in Metric.ball (0 : Space) r, (1 + ‖z‖ / a) ^ (-γ)
      = ∫ z : Space, (Iio r).indicator h ‖z‖ := by
    rw [← integral_indicator Metric.isOpen_ball.measurableSet]
    congr 1
    funext z
    by_cases hz : ‖z‖ < r
    · have hz' : z ∈ Metric.ball (0 : Space) r := by simpa using hz
      simp [hz, hz', hh]
    · have hz' : z ∉ Metric.ball (0 : Space) r := by simpa using hz
      simp [hz, hz']
  have e2 : ∫ y in Ioi (0 : ℝ), y ^ (3 - 1) • (Iio r).indicator h y
      = ∫ y in Ioc (0 : ℝ) r, y ^ 2 * h y := by
    have hfun : (fun y : ℝ => y ^ (3 - 1) • (Iio r).indicator h y)
        = (Iio r).indicator (fun y => y ^ 2 * h y) := by
      funext y
      by_cases hy : y < r
      · simp [hy]
      · simp [hy]
    rw [hfun, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, integral_Ioc_eq_integral_Ioo]
  have hint : ∫ y in Ioc (0 : ℝ) r, y ^ 2 * h y ≤ ∫ y in Ioc (0 : ℝ) r, a ^ γ * y ^ (2 - γ) := by
    apply setIntegral_mono_on
    · have hc : ContinuousOn (fun y : ℝ => y ^ 2 * h y) (Icc 0 r) := by
        apply ContinuousOn.mul (continuousOn_pow 2)
        apply ContinuousOn.rpow_const
        · fun_prop
        · intro y hy
          left
          have : 0 ≤ y := hy.1
          positivity
      exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · have hii : IntervalIntegrable (fun y : ℝ => y ^ (2 - γ)) volume 0 r :=
        intervalIntegral.intervalIntegrable_rpow' (by linarith)
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).1 hii).const_mul _
    · exact measurableSet_Ioc
    · intro y hy
      exact pointwise_bound ha hγ hy.1
  have e3 : ∫ y in Ioc (0 : ℝ) r, a ^ γ * y ^ (2 - γ) = a ^ γ * (r ^ (3 - γ) / (3 - γ)) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hr.le,
      integral_rpow (Or.inl (by linarith))]
    have h3 : 2 - γ + 1 = 3 - γ := by ring
    rw [h3, Real.zero_rpow (by linarith), sub_zero]
  have hV : 0 ≤ volume.real (Metric.ball (0 : Space) 1) := measureReal_nonneg
  rw [e1, integral_fun_norm_addHaar volume, finrank_space, e2, nsmul_eq_mul, smul_eq_mul]
  have := hint.trans e3.le
  push_cast
  calc 3 * (volume.real (Metric.ball (0 : Space) 1) * ∫ y in Ioc (0 : ℝ) r, y ^ 2 * h y)
      ≤ 3 * (volume.real (Metric.ball (0 : Space) 1) * (a ^ γ * (r ^ (3 - γ) / (3 - γ)))) := by
        gcongr
    _ = _ := by ring

lemma whole_bound {a γ r : ℝ} (ha : 0 < a) (hγ3 : 3 < γ) :
    ∫ z in Metric.ball (0 : Space) r, (1 + ‖z‖ / a) ^ (-γ)
      ≤ (∫ u : Space, (1 + ‖u‖) ^ (-γ)) * a ^ 3 := by
  have hdim : ((Module.finrank ℝ Space : ℕ) : ℝ) < γ := by
    rw [finrank_space]
    exact_mod_cast hγ3
  have hg : Integrable (fun u : Space => (1 + ‖u‖) ^ (-γ)) := integrable_one_add_norm hdim
  have hfun : (fun z : Space => (1 + ‖z‖ / a) ^ (-γ))
      = fun z => (fun u : Space => (1 + ‖u‖) ^ (-γ)) (a⁻¹ • z) := by
    funext z
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
    rw [inv_mul_eq_div]
  have hint : Integrable (fun z : Space => (1 + ‖z‖ / a) ^ (-γ)) := by
    rw [hfun]
    exact hg.comp_smul (inv_ne_zero ha.ne')
  calc ∫ z in Metric.ball (0 : Space) r, (1 + ‖z‖ / a) ^ (-γ)
      ≤ ∫ z : Space, (1 + ‖z‖ / a) ^ (-γ) :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun z => weight_nonneg ha γ z)
    _ = a ^ 3 * ∫ u : Space, (1 + ‖u‖) ^ (-γ) := by
        rw [hfun, Measure.integral_comp_inv_smul_of_nonneg volume
          (fun u : Space => (1 + ‖u‖) ^ (-γ)) ha.le, finrank_space, smul_eq_mul]
    _ = _ := mul_comm _ _

lemma combine {X A B r m : ℝ} (hr : 0 < r) (hm : 0 ≤ m) (h1 : X ≤ A * r ^ 3)
    (h2 : X ≤ B * r ^ 3 * m) : X ≤ max A B * r ^ 3 * min 1 m := by
  have hr3 : 0 ≤ r ^ 3 := by positivity
  rcases le_total 1 m with h | h
  · rw [min_eq_left h, mul_one]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr3)
  · rw [min_eq_right h]
    exact h2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hr3) hm)

end RadialWeightInternal

open RadialWeightInternal in
theorem radialWeightBound_holds : RadialWeightBound := by
  intro γ hγ hγ3
  rcases lt_or_gt_of_ne hγ3 with hlt | hgt
  · refine ⟨max (volume.real (Metric.ball (0 : Space) 1))
      (3 * volume.real (Metric.ball (0 : Space) 1) / (3 - γ)), fun a r ha hr => ?_⟩
    rw [min_eq_left hlt.le]
    apply combine hr (by positivity) (volume_bound ha hγ hr)
    have h3 : r ^ (3 : ℝ) = r ^ 3 := by exact_mod_cast Real.rpow_natCast r 3
    have hne : (3 - γ) ≠ 0 := by linarith
    have hrg : r ^ γ ≠ 0 := (Real.rpow_pos_of_pos hr γ).ne'
    calc _ ≤ 3 * volume.real (Metric.ball (0 : Space) 1) * (a ^ γ * (r ^ (3 - γ) / (3 - γ))) :=
          radial_bound ha hγ hlt hr
      _ = 3 * volume.real (Metric.ball (0 : Space) 1) / (3 - γ) * r ^ 3 * (a / r) ^ γ := by
          rw [Real.div_rpow ha.le hr.le, Real.rpow_sub hr, h3]
          field_simp
  · refine ⟨max (volume.real (Metric.ball (0 : Space) 1)) (∫ u : Space, (1 + ‖u‖) ^ (-γ)),
      fun a r ha hr => ?_⟩
    have h3 : (a / r) ^ (3 : ℝ) = (a / r) ^ 3 := by exact_mod_cast Real.rpow_natCast (a / r) 3
    rw [min_eq_right hgt.le, h3]
    apply combine hr (by positivity) (volume_bound ha hγ hr)
    calc _ ≤ (∫ u : Space, (1 + ‖u‖) ^ (-γ)) * a ^ 3 := whole_bound ha hgt
      _ = _ := by
          field_simp
