import Breakdown.Frac.StSpace
import Breakdown.Frac.OpRemainder
import Breakdown.Frac.OpIntegrable
import Breakdown.Uniqueness.PressureAverageAuxField
import Breakdown.Uniqueness.PressureAverageAuxStress2
import Breakdown.Uniqueness.PressureAverageAuxBound

open scoped ContDiff ENNReal
open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown.FracInternal

private theorem mollifyPairing_third_bound {ϕ : Space → Space}
    (hϕ : ContDiff ℝ ∞ ϕ) (hc : HasCompactSupport ϕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ, 0 < ρ → ∀ y,
      ‖iteratedFDeriv ℝ 3 (FundSol.mollify ρ ϕ) y‖ ≤ C * ρ⁻¹ ^ 6 := by
  obtain ⟨C, hC0, hC⟩ := Internal.norm_iteratedFDeriv_mollifier_aux 3
  refine ⟨‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space)‖ * C * ∫ y, ‖ϕ y‖,
    mul_nonneg (mul_nonneg (norm_nonneg _) hC0) (integral_nonneg fun _ => norm_nonneg _),
    fun ρ hρ y => ?_⟩
  have h := Internal.norm_iteratedFDeriv_convolution_field_le hϕ.continuous hc 3
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space) (FundSol.mollifier ρ)
    (Internal.contDiff_mollifier_aux ρ) (Internal.hasCompactSupport_mollifier_aux hρ)
    (C * ρ⁻¹ ^ 6) (fun x => hC ρ hρ x) y
  calc ‖iteratedFDeriv ℝ 3 (FundSol.mollify ρ ϕ) y‖ ≤ _ := h
    _ = _ := by ring

private theorem mollifyPairing_norm_kernel_smul (α : ℝ) (z v : Space) :
    ‖‖z‖ ^ (-(3 + 2 * α)) • v‖ = ‖z‖ ^ (-(3 + 2 * α)) * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

private theorem mollifyPairing_remainder_far (f : Space → Space) (x z : Space) (hz : 1 ≤ ‖z‖) :
    ‖secondOrderRemainder f x z‖ ≤
      ‖f (x + z)‖ + (‖f x‖ + ‖fderiv ℝ f x‖ + ‖iteratedFDeriv ℝ 2 f x‖) * ‖z‖ ^ 2 := by
  have h2 : ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ * (‖z‖ * ‖z‖) := by
    have := (iteratedFDeriv ℝ 2 f x).le_opNorm ![z, z]
    simpa [Fin.prod_univ_two] using this
  have h1' : ‖fderiv ℝ f x z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ := (fderiv ℝ f x).le_opNorm z
  have hs : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ ‖iteratedFDeriv ℝ 2 f x ![z, z]‖ := by
    rw [norm_smul]
    have := norm_nonneg (iteratedFDeriv ℝ 2 f x ![z, z])
    norm_num
    linarith
  have e := norm_sub_le (f (x + z) - f x - fderiv ℝ f x z)
    ((1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z])
  have e2 := norm_sub_le (f (x + z) - f x) (fderiv ℝ f x z)
  have e3 := norm_sub_le (f (x + z)) (f x)
  have hz2 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
  have hz3 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
  have t1 : ‖f x‖ ≤ ‖f x‖ * ‖z‖ ^ 2 := by nlinarith [norm_nonneg (f x)]
  have t2 : ‖fderiv ℝ f x‖ * ‖z‖ ≤ ‖fderiv ℝ f x‖ * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hz2 (norm_nonneg _)
  have t3 : ‖z‖ * ‖z‖ = ‖z‖ ^ 2 := by ring
  rw [t3] at h2
  unfold secondOrderRemainder
  nlinarith

private theorem mollifyPairing_uniform {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2)
    {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ) (hc : HasCompactSupport ϕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ, 1 ≤ ρ → ∀ x,
      ‖fractionalPowerAt α (FundSol.mollify ρ ϕ) x‖ ≤ K * ρ⁻¹ ^ 3 := by
  obtain ⟨R, C, hR0, hC0, hb⟩ := Internal.mollify_field_bounds hϕ hc
  obtain ⟨C3, hC30, hC3⟩ := mollifyPairing_third_bound hϕ hc
  obtain ⟨G, hG⟩ : ∃ G : Space → ℝ, G = fun z =>
      (ball (0 : Space) 1).indicator (fun z => C3 * ‖z‖ ^ (-(2 * α))) z +
        (ball (0 : Space) 1)ᶜ.indicator (fun z => 4 * C * ‖z‖ ^ (-(1 + 2 * α))) z := ⟨_, rfl⟩
  have hGi : Integrable G := by
    rw [hG]
    exact (IntegrableOn.integrable_indicator
      ((integrableOn_ball_norm_rpow (s := -(2 * α)) (by linarith)).const_mul C3)
      measurableSet_ball).add
      (IntegrableOn.integrable_indicator
        ((integrableOn_compl_ball_norm_rpow (s := -(1 + 2 * α)) (by linarith)).const_mul (4 * C))
        measurableSet_ball.compl)
  have hG0 : ∀ z, 0 ≤ G z := by
    intro z
    rw [hG]
    exact add_nonneg (indicator_nonneg (fun y _ => by positivity) z)
      (indicator_nonneg (fun y _ => by positivity) z)
  refine ⟨|(fractionalNormalizer α)⁻¹| * ∫ z, G z,
    mul_nonneg (abs_nonneg _) (integral_nonneg hG0), fun ρ hρ x => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  have hΦs : ContDiff ℝ ∞ (FundSol.mollify ρ ϕ) := Internal.contDiff_mollify_field hϕ hc hρ0
  have hbx := hb ρ hρ x
  have hbz : ∀ z, ‖FundSol.mollify ρ ϕ (x + z)‖ ≤ C * ρ⁻¹ ^ 3 := fun z => (hb ρ hρ (x + z)).2.1
  have h3 := hC3 ρ hρ0
  generalize FundSol.mollify ρ ϕ = Φ at hΦs hbx hbz h3 ⊢
  have hr1 : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ
  have hr0 : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ0.le
  have hp4 : ρ⁻¹ ^ 4 ≤ ρ⁻¹ ^ 3 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hp5 : ρ⁻¹ ^ 5 ≤ ρ⁻¹ ^ 3 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hp6 : ρ⁻¹ ^ 6 ≤ ρ⁻¹ ^ 3 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hpt : ∀ z, ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder Φ x z‖ ≤ ρ⁻¹ ^ 3 * G z := by
    intro z
    rw [mollifyPairing_norm_kernel_smul, hG]
    by_cases hz : ‖z‖ < 1
    · have hzm : z ∈ ball (0 : Space) 1 := mem_ball_zero_iff.2 hz
      have hzc : z ∉ (ball (0 : Space) 1)ᶜ := fun h => h hzm
      simp only [indicator_of_mem hzm, indicator_of_notMem hzc, add_zero]
      have hR := remainderBound Φ (hΦs.of_le (WithTop.coe_le_coe.mpr le_top)) x z
        (C3 * ρ⁻¹ ^ 6) (fun y _ => h3 y)
      rcases eq_or_ne z 0 with rfl | hz0
      · rw [norm_zero, Real.zero_rpow (by linarith : -(3 + 2 * α) ≠ 0),
          Real.zero_rpow (by linarith : -(2 * α) ≠ 0)]
        simp
      · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
        have hk := Real.rpow_nonneg hpos.le (-(3 + 2 * α))
        have hc6 : C3 * ρ⁻¹ ^ 6 * ‖z‖ ^ 3 ≤ C3 * ρ⁻¹ ^ 3 * ‖z‖ ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp6 hC30) (by positivity)
        calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder Φ x z‖
            ≤ ‖z‖ ^ (-(3 + 2 * α)) * (C3 * ρ⁻¹ ^ 3 * ‖z‖ ^ 3) :=
              mul_le_mul_of_nonneg_left (hR.trans hc6) hk
          _ = ρ⁻¹ ^ 3 * (C3 * ‖z‖ ^ (-(2 * α))) := by
              rw [show -(2 * α) = -(3 + 2 * α) + ((3 : ℕ) : ℝ) by push_cast; ring,
                Real.rpow_add hpos, Real.rpow_natCast]
              ring
    · have hz1 : 1 ≤ ‖z‖ := not_lt.1 hz
      have hzm : z ∉ ball (0 : Space) 1 := fun h => hz (mem_ball_zero_iff.1 h)
      have hzc : z ∈ (ball (0 : Space) 1)ᶜ := hzm
      simp only [indicator_of_mem hzc, indicator_of_notMem hzm, zero_add]
      have hf := mollifyPairing_remainder_far Φ x z hz1
      obtain ⟨-, h0, h1, h2⟩ := hbx
      have h0' := hbz z
      have hpos : 0 < ‖z‖ := by linarith
      have hz2 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
      have hk := Real.rpow_nonneg hpos.le (-(3 + 2 * α))
      have hc3 : 0 ≤ C * ρ⁻¹ ^ 3 := by positivity
      have q1 : C * ρ⁻¹ ^ 4 ≤ C * ρ⁻¹ ^ 3 := mul_le_mul_of_nonneg_left hp4 hC0
      have q2 : C * ρ⁻¹ ^ 5 ≤ C * ρ⁻¹ ^ 3 := mul_le_mul_of_nonneg_left hp5 hC0
      have q3 : (‖Φ x‖ + ‖fderiv ℝ Φ x‖ + ‖iteratedFDeriv ℝ 2 Φ x‖) * ‖z‖ ^ 2 ≤
          (3 * (C * ρ⁻¹ ^ 3)) * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have q4 : C * ρ⁻¹ ^ 3 ≤ C * ρ⁻¹ ^ 3 * ‖z‖ ^ 2 := le_mul_of_one_le_right hc3 hz2
      have hsum : ‖secondOrderRemainder Φ x z‖ ≤ 4 * C * ρ⁻¹ ^ 3 * ‖z‖ ^ 2 := by
        nlinarith
      calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder Φ x z‖
          ≤ ‖z‖ ^ (-(3 + 2 * α)) * (4 * C * ρ⁻¹ ^ 3 * ‖z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsum hk
        _ = ρ⁻¹ ^ 3 * (4 * C * ‖z‖ ^ (-(1 + 2 * α))) := by
            rw [show -(1 + 2 * α) = -(3 + 2 * α) + ((2 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_add hpos, Real.rpow_natCast]
            ring
  have hI := norm_integral_le_of_norm_le (hGi.const_mul (ρ⁻¹ ^ 3)) (ae_of_all _ hpt)
  rw [integral_const_mul] at hI
  unfold fractionalPowerAt
  rw [norm_smul, Real.norm_eq_abs]
  calc |(fractionalNormalizer α)⁻¹| * ‖∫ z, ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder Φ x z‖
      ≤ |(fractionalNormalizer α)⁻¹| * (ρ⁻¹ ^ 3 * ∫ z, G z) :=
        mul_le_mul_of_nonneg_left hI (abs_nonneg _)
    _ = _ := by ring

private theorem mollifyPairing_far {α : ℝ} (hα1 : 1 < α)
    {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ) (hc : HasCompactSupport ϕ) :
    ∃ R b : ℝ, 0 ≤ R ∧ 0 ≤ b ∧ ∀ ρ, 1 ≤ ρ → R ≤ ρ → ∀ x, 2 * (R + ρ) < ‖x‖ →
      ‖fractionalPowerAt α (FundSol.mollify ρ ϕ) x‖ ≤ b * ‖x‖ ^ (-(3 + 2 * α)) := by
  obtain ⟨R, C, hR0, hC0, hb⟩ := Internal.mollify_field_bounds hϕ hc
  obtain ⟨V, hVpos, hV⟩ := Internal.exists_volume_closedBall_eq
  refine ⟨R, |(fractionalNormalizer α)⁻¹| * (C * (8 * V) * 2 ^ (3 + 2 * α)), hR0,
    mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg hC0 (by linarith)) (by positivity)),
    fun ρ hρ hRρ x hx => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  have hs : ∀ y, R + ρ < ‖y‖ → FundSol.mollify ρ ϕ y = 0 := fun y hy => (hb ρ hρ y).1 hy
  have hbz : ∀ y, ‖FundSol.mollify ρ ϕ y‖ ≤ C * ρ⁻¹ ^ 3 := fun y => (hb ρ hρ y).2.1
  generalize FundSol.mollify ρ ϕ = Φ at hs hbz ⊢
  obtain ⟨r, hr⟩ : ∃ r, r = R + ρ := ⟨_, rfl⟩
  rw [← hr] at hs hx
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < ‖x‖ := by linarith
  have hts : tsupport Φ ⊆ closedBall (0 : Space) r := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [mem_closedBall_zero_iff]
    by_contra h
    exact hy (hs y (not_le.1 h))
  have hxt : x ∉ tsupport Φ := fun h => by
    have := hts h
    rw [mem_closedBall_zero_iff] at this
    linarith
  have hx0' : Φ x = 0 := image_eq_zero_of_notMem_tsupport hxt
  have hx1 : fderiv ℝ Φ x = 0 := fderiv_of_notMem_tsupport ℝ hxt
  have hx2 : iteratedFDeriv ℝ 2 Φ x = 0 := by
    by_contra h
    exact hxt (support_iteratedFDeriv_subset 2 h)
  have hrem : ∀ z, secondOrderRemainder Φ x z = Φ (x + z) := by
    intro z
    simp [secondOrderRemainder, hx0', hx1, hx2]
  obtain ⟨c, hcdef⟩ : ∃ c, c = (‖x‖ / 2) ^ (-(3 + 2 * α)) * (C * ρ⁻¹ ^ 3) := ⟨_, rfl⟩
  have hpt : ∀ z, ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder Φ x z‖ ≤
      (closedBall (-x) r).indicator (fun _ => c) z := by
    intro z
    rw [mollifyPairing_norm_kernel_smul, hrem]
    by_cases hz : z ∈ closedBall (-x) r
    · rw [indicator_of_mem hz, hcdef]
      have hz' : ‖x + z‖ ≤ r := by
        rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add, add_comm] at hz
        exact hz
      have hzn : ‖x‖ / 2 ≤ ‖z‖ := by
        have h1 := norm_sub_le (x + z) z
        rw [add_sub_cancel_right] at h1
        linarith
      have hk : ‖z‖ ^ (-(3 + 2 * α)) ≤ (‖x‖ / 2) ^ (-(3 + 2 * α)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hzn (by linarith)
      exact mul_le_mul hk (hbz (x + z)) (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
    · rw [indicator_of_notMem hz]
      have hz' : r < ‖x + z‖ := by
        rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add, add_comm, not_le] at hz
        exact hz
      rw [hs _ hz', norm_zero, mul_zero]
  have hind : Integrable ((closedBall (-x) r).indicator (fun _ => c)) :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hI := norm_integral_le_of_norm_le hind (ae_of_all _ hpt)
  have hvx : volume.real (closedBall (-x) r) = V * r ^ 3 := by
    rw [← hV r hr0.le, Measure.addHaar_real_closedBall volume (-x) hr0.le,
      Measure.addHaar_real_closedBall volume 0 hr0.le]
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, hvx] at hI
  have h8 : (r * ρ⁻¹) ^ 3 ≤ 8 := by
    have h2 : r * ρ⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hρ0]
      linarith
    have := pow_le_pow_left₀ (mul_nonneg hr0.le (inv_nonneg.2 hρ0.le)) h2 3
    norm_num at this
    linarith
  have hc2 : (‖x‖ / 2) ^ (-(3 + 2 * α)) = ‖x‖ ^ (-(3 + 2 * α)) * 2 ^ (3 + 2 * α) := by
    rw [Real.div_rpow hx0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul]
  unfold fractionalPowerAt
  rw [norm_smul, Real.norm_eq_abs]
  have hnn : 0 ≤ |(fractionalNormalizer α)⁻¹| * C * V * 2 ^ (3 + 2 * α) * ‖x‖ ^ (-(3 + 2 * α)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hC0) hVpos) (by positivity))
      (Real.rpow_nonneg hx0.le _)
  calc |(fractionalNormalizer α)⁻¹| * ‖∫ z, ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder Φ x z‖
      ≤ |(fractionalNormalizer α)⁻¹| * (V * r ^ 3 * c) :=
        mul_le_mul_of_nonneg_left hI (abs_nonneg _)
    _ = (|(fractionalNormalizer α)⁻¹| * C * V * 2 ^ (3 + 2 * α) * ‖x‖ ^ (-(3 + 2 * α))) *
          (r * ρ⁻¹) ^ 3 := by
        rw [hcdef, hc2]
        ring
    _ ≤ (|(fractionalNormalizer α)⁻¹| * C * V * 2 ^ (3 + 2 * α) * ‖x‖ ^ (-(3 + 2 * α))) * 8 :=
        mul_le_mul_of_nonneg_left h8 hnn
    _ = _ := by ring

private theorem mollifyPairing_abs_le {w g : Space → Space} {H : Space → ℝ}
    (hwi : Integrable (fun x => ‖w x‖ ^ 2)) (hH : Integrable H) (hg : ∀ x, ‖g x‖ ^ 2 ≤ H x)
    {t : ℝ} (ht : 0 < t) :
    |∫ x, inner ℝ (w x) (g x)| ≤ t * (∫ x, ‖w x‖ ^ 2) + t⁻¹ * ∫ x, H x := by
  have ht' : 0 < t⁻¹ := inv_pos.2 ht
  have hpt : ∀ x, ‖inner ℝ (w x) (g x)‖ ≤ t * ‖w x‖ ^ 2 + t⁻¹ * H x := by
    intro x
    rw [Real.norm_eq_abs]
    have h1 := abs_real_inner_le_norm (w x) (g x)
    have e : t⁻¹ * (t * ‖w x‖ - ‖g x‖) ^ 2 =
        t * ‖w x‖ ^ 2 - 2 * (‖w x‖ * ‖g x‖) + t⁻¹ * ‖g x‖ ^ 2 := by
      field_simp
      ring
    have h2 : t⁻¹ * ‖g x‖ ^ 2 ≤ t⁻¹ * H x := mul_le_mul_of_nonneg_left (hg x) ht'.le
    nlinarith [mul_nonneg ht'.le (sq_nonneg (t * ‖w x‖ - ‖g x‖)),
      mul_nonneg (norm_nonneg (w x)) (norm_nonneg (g x)),
      mul_nonneg ht.le (sq_nonneg ‖w x‖), mul_nonneg ht'.le (sq_nonneg ‖g x‖)]
  calc |∫ x, inner ℝ (w x) (g x)| = ‖∫ x, inner ℝ (w x) (g x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, (t * ‖w x‖ ^ 2 + t⁻¹ * H x) :=
        norm_integral_le_of_norm_le ((hwi.const_mul t).add (hH.const_mul t⁻¹)) (ae_of_all _ hpt)
    _ = _ := by
        rw [integral_add (hwi.const_mul t) (hH.const_mul t⁻¹), integral_const_mul,
          integral_const_mul]

private theorem mollifyPairing_sq_bound {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2)
    {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ) (hc : HasCompactSupport ϕ) :
    ∃ R E : ℝ, 0 ≤ R ∧ 0 ≤ E ∧ ∀ ρ, 1 ≤ ρ → R ≤ ρ → ∃ H : Space → ℝ, Integrable H ∧
      (∀ x, ‖fractionalPowerAt α (FundSol.mollify ρ ϕ) x‖ ^ 2 ≤ H x) ∧ ∫ x, H x ≤ E * ρ⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := mollifyPairing_uniform hα1 hα2 hϕ hc
  obtain ⟨R, b, hR0, hb0, hb⟩ := mollifyPairing_far hα1 hϕ hc
  obtain ⟨V, hVpos, hV⟩ := Internal.exists_volume_closedBall_eq
  have hJ := integrableOn_compl_ball_norm_rpow (s := -(5 + 4 * α)) (by linarith)
  obtain ⟨J, hJdef⟩ : ∃ J, J = ∫ x in (ball (0 : Space) 1)ᶜ, ‖x‖ ^ (-(5 + 4 * α)) := ⟨_, rfl⟩
  have hJ0 : 0 ≤ J := by
    rw [hJdef]
    exact setIntegral_nonneg measurableSet_ball.compl fun x _ => Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨R, K ^ 2 * V * 64 + b ^ 2 * J, hR0,
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hVpos) (by norm_num)) (mul_nonneg (sq_nonneg _) hJ0),
    fun ρ hρ hRρ => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  obtain ⟨r, hr⟩ : ∃ r, r = 2 * (R + ρ) := ⟨_, rfl⟩
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hi1 : Integrable ((closedBall (0 : Space) r).indicator (fun _ => (K * ρ⁻¹ ^ 3) ^ 2)) :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hi2 : Integrable ((ball (0 : Space) 1)ᶜ.indicator
      (fun x : Space => b ^ 2 * r⁻¹ * ‖x‖ ^ (-(5 + 4 * α)))) :=
    IntegrableOn.integrable_indicator (hJ.const_mul (b ^ 2 * r⁻¹)) measurableSet_ball.compl
  refine ⟨fun x => (closedBall (0 : Space) r).indicator (fun _ => (K * ρ⁻¹ ^ 3) ^ 2) x +
    (ball (0 : Space) 1)ᶜ.indicator (fun x : Space => b ^ 2 * r⁻¹ * ‖x‖ ^ (-(5 + 4 * α))) x,
    hi1.add hi2, fun x => ?_, ?_⟩
  · have n1 : 0 ≤ (closedBall (0 : Space) r).indicator (fun _ => (K * ρ⁻¹ ^ 3) ^ 2) x :=
      indicator_nonneg (fun _ _ => sq_nonneg _) x
    have n2 : 0 ≤ (ball (0 : Space) 1)ᶜ.indicator
        (fun x : Space => b ^ 2 * r⁻¹ * ‖x‖ ^ (-(5 + 4 * α))) x :=
      indicator_nonneg (fun y _ => mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 hr0.le))
        (Real.rpow_nonneg (norm_nonneg _) _)) x
    beta_reduce
    by_cases hx : ‖x‖ ≤ r
    · have hxm : x ∈ closedBall (0 : Space) r := mem_closedBall_zero_iff.2 hx
      rw [indicator_of_mem hxm]
      have h1 := hK ρ hρ x
      have : ‖fractionalPowerAt α (FundSol.mollify ρ ϕ) x‖ ^ 2 ≤ (K * ρ⁻¹ ^ 3) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      linarith
    · have hxr : r < ‖x‖ := not_le.1 hx
      have hxm : x ∈ (ball (0 : Space) 1)ᶜ := fun h => by
        have := mem_ball_zero_iff.1 h
        linarith
      rw [indicator_of_mem hxm]
      have hx0 : 0 < ‖x‖ := by linarith
      have h1 := hb ρ hρ hRρ x (by rw [← hr]; exact hxr)
      have h2 : ‖fractionalPowerAt α (FundSol.mollify ρ ϕ) x‖ ^ 2 ≤
          (b * ‖x‖ ^ (-(3 + 2 * α))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      have e2 : ‖x‖ ^ (-(5 + 4 * α)) = ‖x‖ ^ (-(3 + 2 * α) + -(3 + 2 * α) + 1) := by
        congr 1
        ring
      have e : (b * ‖x‖ ^ (-(3 + 2 * α))) ^ 2 = b ^ 2 * ‖x‖⁻¹ * ‖x‖ ^ (-(5 + 4 * α)) := by
        rw [e2, Real.rpow_add_one hx0.ne', Real.rpow_add hx0]
        field_simp
      have h3 : b ^ 2 * ‖x‖⁻¹ * ‖x‖ ^ (-(5 + 4 * α)) ≤ b ^ 2 * r⁻¹ * ‖x‖ ^ (-(5 + 4 * α)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (inv_anti₀ hr0 hxr.le) (sq_nonneg _))
          (Real.rpow_nonneg hx0.le _)
      linarith
  · have hint : ∫ x, ((closedBall (0 : Space) r).indicator (fun _ => (K * ρ⁻¹ ^ 3) ^ 2) x +
        (ball (0 : Space) 1)ᶜ.indicator (fun x : Space => b ^ 2 * r⁻¹ * ‖x‖ ^ (-(5 + 4 * α))) x) =
        (K * ρ⁻¹ ^ 3) ^ 2 * (V * r ^ 3) + b ^ 2 * r⁻¹ * J := by
      rw [integral_add hi1 hi2, integral_indicator_const _ measurableSet_closedBall, smul_eq_mul,
        hV r hr0.le, integral_indicator measurableSet_ball.compl, integral_const_mul, ← hJdef]
      ring
    rw [hint]
    have hi0 : 0 ≤ ρ⁻¹ := inv_nonneg.2 hρ0.le
    have h4 : r * ρ⁻¹ ≤ 4 := by
      rw [mul_inv_le_iff₀ hρ0]
      linarith
    have h64 : (r * ρ⁻¹) ^ 3 ≤ 64 := by
      have := pow_le_pow_left₀ (mul_nonneg hr0.le hi0) h4 3
      norm_num at this
      linarith
    have hp3 : ρ⁻¹ ^ 3 ≤ ρ⁻¹ := pow_le_of_le_one hi0 (inv_le_one_of_one_le₀ hρ) (by norm_num)
    have t1 : (K * ρ⁻¹ ^ 3) ^ 2 * (V * r ^ 3) ≤ K ^ 2 * V * 64 * ρ⁻¹ := by
      have e : (K * ρ⁻¹ ^ 3) ^ 2 * (V * r ^ 3) = (K ^ 2 * V) * ((r * ρ⁻¹) ^ 3 * ρ⁻¹ ^ 3) := by ring
      rw [e]
      have hp : (r * ρ⁻¹) ^ 3 * ρ⁻¹ ^ 3 ≤ 64 * ρ⁻¹ :=
        mul_le_mul h64 hp3 (by positivity) (by norm_num)
      calc (K ^ 2 * V) * ((r * ρ⁻¹) ^ 3 * ρ⁻¹ ^ 3) ≤ (K ^ 2 * V) * (64 * ρ⁻¹) :=
            mul_le_mul_of_nonneg_left hp (mul_nonneg (sq_nonneg K) hVpos)
        _ = _ := by ring
    have t2 : b ^ 2 * r⁻¹ * J ≤ b ^ 2 * ρ⁻¹ * J :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (inv_anti₀ hρ0 (by linarith)) (sq_nonneg b)) hJ0
    calc (K * ρ⁻¹ ^ 3) ^ 2 * (V * r ^ 3) + b ^ 2 * r⁻¹ * J
        ≤ K ^ 2 * V * 64 * ρ⁻¹ + b ^ 2 * ρ⁻¹ * J := add_le_add t1 t2
      _ = _ := by ring

end Breakdown.FracInternal

namespace Breakdown

open FracInternal

theorem fracMollifyPairing : FracMollifyPairingStatement := by
  intro α hα1 hα2 ϕ hϕ hc A ε hε
  obtain ⟨R, E, hR0, hE0, hH⟩ := mollifyPairing_sq_bound hα1 hα2 hϕ hc
  obtain ⟨A', hA'⟩ : ∃ A', A' = max A 0 := ⟨_, rfl⟩
  have hA'0 : 0 ≤ A' := hA' ▸ le_max_right _ _
  obtain ⟨t, ht⟩ : ∃ t, t = ε / (2 * (A' + 1)) := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact div_pos hε (by linarith)
  refine ⟨max (max 1 R) (2 * (E + 1) / (t * ε)), fun ρ hρ w hw hwA => ?_⟩
  have hρ1 : 1 ≤ ρ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hρ
  have hRρ : R ≤ ρ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hρ
  have hρE : 2 * (E + 1) / (t * ε) ≤ ρ := le_trans (le_max_right _ _) hρ
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨H, hHi, hHpt, hHint⟩ := hH ρ hρ1 hRρ
  have hwi := Internal.PressureMollify.integrable_norm_sq hw hwA
  have hwb : ∫ x, ‖w x‖ ^ 2 ≤ A' := by
    have h1 : ENNReal.ofReal (∫ x, ‖w x‖ ^ 2) ≤ ENNReal.ofReal A := by
      rw [ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ fun x => sq_nonneg _)]
      exact hwA
    rw [hA']
    rcases le_total A 0 with h | h
    · rw [ENNReal.ofReal_eq_zero.2 h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
      exact h1.trans (le_max_right _ _)
    · exact ((ENNReal.ofReal_le_ofReal_iff h).1 h1).trans (le_max_left _ _)
  have h := mollifyPairing_abs_le hwi hHi hHpt ht0
  refine h.trans ?_
  have hA1 : A' + 1 ≠ 0 := by linarith
  have h1 : t * ∫ x, ‖w x‖ ^ 2 ≤ ε / 2 := by
    calc t * ∫ x, ‖w x‖ ^ 2 ≤ t * (A' + 1) := mul_le_mul_of_nonneg_left (by linarith) ht0.le
      _ = ε / 2 := by
          rw [ht]
          field_simp
  have h2 : t⁻¹ * ∫ x, H x ≤ ε / 2 := by
    have hI : ∫ x, H x ≤ (E + 1) * ρ⁻¹ :=
      hHint.trans (mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hρ0.le))
    have hρinv : (E + 1) * ρ⁻¹ ≤ t * ε / 2 := by
      rw [div_le_iff₀ (mul_pos ht0 hε)] at hρE
      rw [← div_eq_mul_inv, div_le_iff₀ hρ0]
      nlinarith
    calc t⁻¹ * ∫ x, H x ≤ t⁻¹ * (t * ε / 2) :=
          mul_le_mul_of_nonneg_left (hI.trans hρinv) (inv_nonneg.2 ht0.le)
      _ = ε / 2 := by
          field_simp
  linarith

end Breakdown
