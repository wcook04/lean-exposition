import Breakdown.Frac.StSpace
import Breakdown.Frac.OpRemainder
import Breakdown.Frac.OpIntegrable

open scoped ContDiff
open MeasureTheory Metric Set

noncomputable section

namespace Breakdown.FracInternal

private theorem decayRemainderFar (f : Space → Space) (x z : Space) (hz : 1 ≤ ‖z‖) :
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

private theorem decayRemainderOff {f : Space → Space} {R : ℝ} (hR : tsupport f ⊆ closedBall 0 R)
    (x z : Space) (hx : R < ‖x‖) : secondOrderRemainder f x z = f (x + z) := by
  have hx' : x ∉ tsupport f := fun h => by
    have := hR h
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx'
  have h1 : fderiv ℝ f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx' (tsupport_fderiv_subset ℝ h))
  have h2 : iteratedFDeriv ℝ 2 f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx' (tsupport_iteratedFDeriv_subset 2 h))
  simp [secondOrderRemainder, h0, h1, h2]

end Breakdown.FracInternal

namespace Breakdown

open FracInternal

theorem fracCompactDecay : FracCompactDecayStatement := by
  intro α hα1 hα2 ϕ hϕ hc
  have hϕ3 : ContDiff ℝ 3 ϕ := hϕ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hc0 : Continuous ϕ := hϕ.continuous
  have hc1 : Continuous (fderiv ℝ ϕ) := hϕ.continuous_fderiv (by simp)
  have hc2 : Continuous (iteratedFDeriv ℝ 2 ϕ) :=
    hϕ.continuous_iteratedFDeriv (m := 2) (WithTop.coe_le_coe.mpr le_top)
  have hc3 : Continuous (iteratedFDeriv ℝ 3 ϕ) :=
    hϕ.continuous_iteratedFDeriv (m := 3) (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨B0, hB0⟩ := hc0.bounded_above_of_compact_support hc
  obtain ⟨B1, hB1⟩ := hc1.bounded_above_of_compact_support (hc.fderiv ℝ)
  obtain ⟨B2, hB2⟩ := hc2.bounded_above_of_compact_support (hc.iteratedFDeriv 2)
  obtain ⟨B3, hB3⟩ := hc3.bounded_above_of_compact_support (hc.iteratedFDeriv 3)
  have hB0n : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0)
  have hB1n : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB2n : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hB3n : 0 ≤ B3 := (norm_nonneg _).trans (hB3 0)
  have hKm : Measurable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α))) := measurable_norm.pow_const _
  have hK0 : ∀ z : Space, 0 ≤ ‖z‖ ^ (-(3 + 2 * α)) := fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hnormF : ∀ x z : Space, ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder ϕ x z‖ =
      ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder ϕ x z‖ := by
    intro x z
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hK0 z)]
  have hRc : ∀ x, Continuous (fun z => secondOrderRemainder ϕ x z) := by
    intro x
    have hsh : Continuous (fun z : Space => ϕ (x + z)) := hc0.comp (continuous_const.add continuous_id)
    unfold secondOrderRemainder
    exact ((hsh.sub continuous_const).sub (fderiv ℝ ϕ x).continuous).sub
      (show Continuous fun z : Space => (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 ϕ x ![z, z] from by fun_prop)
  have hRx : ∀ z, Continuous (fun x => ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder ϕ x z) := by
    intro z
    have hsh : Continuous (fun x : Space => ϕ (x + z)) := hc0.comp (continuous_id.add continuous_const)
    have ha : Continuous (fun x : Space => fderiv ℝ ϕ x z) := hc1.clm_apply continuous_const
    have hb : Continuous (fun x : Space => iteratedFDeriv ℝ 2 ϕ x ![z, z]) := by fun_prop
    unfold secondOrderRemainder
    have hh := ((hsh.sub hc0).sub ha).sub (hb.const_smul (1 / 2 : ℝ))
    fun_prop
  set D : ℝ := 2 * B0 + B1 + B2 with hD
  set bound : Space → ℝ := fun z =>
    (ball (0 : Space) 1).indicator (fun z => B3 * ‖z‖ ^ (-(2 * α))) z +
      (ball (0 : Space) 1)ᶜ.indicator (fun z => D * ‖z‖ ^ (-(1 + 2 * α))) z with hbound_def
  have hbint : Integrable bound := by
    have i1 : IntegrableOn (fun z : Space => B3 * ‖z‖ ^ (-(2 * α))) (ball (0 : Space) 1) :=
      (integrableOn_ball_norm_rpow (s := -(2 * α)) (by linarith)).const_mul B3
    have i2 : IntegrableOn (fun z : Space => D * ‖z‖ ^ (-(1 + 2 * α))) (ball (0 : Space) 1)ᶜ :=
      (integrableOn_compl_ball_norm_rpow (s := -(1 + 2 * α)) (by linarith)).const_mul D
    exact (i1.integrable_indicator measurableSet_ball).add (i2.integrable_indicator measurableSet_ball.compl)
  have hbound : ∀ x z, ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder ϕ x z‖ ≤ bound z := by
    intro x z
    rw [hnormF]
    by_cases hz : ‖z‖ < 1
    · have hzb : z ∈ ball (0 : Space) 1 := by simpa using hz
      have hzc : z ∉ (ball (0 : Space) 1)ᶜ := fun h => h hzb
      simp only [hbound_def, indicator_of_mem hzb, indicator_of_notMem hzc, add_zero]
      have hR := remainderBound ϕ hϕ3 x z B3 (fun y _ => hB3 y)
      rcases eq_or_ne z 0 with rfl | hz0
      · rw [norm_zero, Real.zero_rpow (by linarith : -(3 + 2 * α) ≠ 0),
          Real.zero_rpow (by linarith : -(2 * α) ≠ 0)]
        simp
      · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
        calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder ϕ x z‖
            ≤ ‖z‖ ^ (-(3 + 2 * α)) * (B3 * ‖z‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hpos.le _)
          _ = B3 * ‖z‖ ^ (-(2 * α)) := by
              rw [show -(2 * α) = -(3 + 2 * α) + ((3 : ℕ) : ℝ) by push_cast; ring,
                Real.rpow_add hpos, Real.rpow_natCast]
              ring
    · have hz1 : 1 ≤ ‖z‖ := not_lt.1 hz
      have hzc : z ∈ (ball (0 : Space) 1)ᶜ := by simpa using hz1
      have hzb : z ∉ ball (0 : Space) 1 := hzc
      simp only [hbound_def, indicator_of_mem hzc, indicator_of_notMem hzb, zero_add]
      have hpos : 0 < ‖z‖ := by linarith
      have hb := decayRemainderFar ϕ x z hz1
      have hz3 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
      have hb' : ‖secondOrderRemainder ϕ x z‖ ≤ D * ‖z‖ ^ 2 := by
        have := hB0 (x + z)
        have := hB0 x
        have := hB1 x
        have := hB2 x
        have : (‖ϕ x‖ + ‖fderiv ℝ ϕ x‖ + ‖iteratedFDeriv ℝ 2 ϕ x‖) * ‖z‖ ^ 2 ≤
            (B0 + B1 + B2) * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have : B0 ≤ B0 * ‖z‖ ^ 2 := by nlinarith
        rw [hD]
        nlinarith
      have hk : ‖z‖ ^ (-(3 + 2 * α)) * ‖z‖ ^ 2 = ‖z‖ ^ (-(1 + 2 * α)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
        congr 1
        push_cast
        ring
      calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder ϕ x z‖
          ≤ ‖z‖ ^ (-(3 + 2 * α)) * (D * ‖z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hb' (Real.rpow_nonneg hpos.le _)
        _ = D * ‖z‖ ^ (-(1 + 2 * α)) := by rw [← hk]; ring
  have hcont : Continuous (fun x => ∫ z : Space, ‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder ϕ x z) :=
    continuous_of_dominated
      (fun x => hKm.aestronglyMeasurable.smul (hRc x).aestronglyMeasurable)
      (fun x => ae_of_all _ (hbound x)) hbint (ae_of_all _ hRx)
  have hunif : ∀ x, ‖fractionalPowerAt α ϕ x‖ ≤
      |(fractionalNormalizer α)⁻¹| * ∫ z, bound z := by
    intro x
    unfold fractionalPowerAt
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hbint (ae_of_all _ (hbound x)))
      (abs_nonneg _)
  refine ⟨?_, ?_⟩
  · unfold fractionalPowerAt
    fun_prop
  · obtain ⟨R0, hR0⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Space)
    set R : ℝ := max R0 1 with hRdef
    have hR1 : 1 ≤ R := le_max_right _ _
    have hsupp : tsupport ϕ ⊆ closedBall 0 R :=
      hR0.trans (closedBall_subset_closedBall (le_max_left _ _))
    have hLint : Integrable (fun y : Space => ‖ϕ y‖) := hc0.norm.integrable_of_hasCompactSupport hc.norm
    set L : ℝ := ∫ y, ‖ϕ y‖ with hLdef
    set A : ℝ := |(fractionalNormalizer α)⁻¹| * ∫ z, bound z with hAdef
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hunif 0)
    have hfarx : ∀ x : Space, 2 * R ≤ ‖x‖ → ‖fractionalPowerAt α ϕ x‖ ≤
        |(fractionalNormalizer α)⁻¹| * ((‖x‖ / 2) ^ (-(3 + 2 * α)) * L) := by
      intro x hx
      have hxR : R < ‖x‖ := by linarith
      have hx2 : 0 < ‖x‖ / 2 := by linarith
      have hgi : Integrable (fun z : Space => (‖x‖ / 2) ^ (-(3 + 2 * α)) * ‖ϕ (x + z)‖) :=
        (hLint.comp_add_left x).const_mul _
      have hpt : ∀ z : Space, ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder ϕ x z‖ ≤
          (‖x‖ / 2) ^ (-(3 + 2 * α)) * ‖ϕ (x + z)‖ := by
        intro z
        rw [hnormF, decayRemainderOff hsupp x z hxR]
        by_cases h0 : ϕ (x + z) = 0
        · simp [h0]
        · have hmem : x + z ∈ tsupport ϕ := subset_tsupport _ h0
          have hb := hsupp hmem
          rw [mem_closedBall, dist_zero_right] at hb
          have htri := norm_sub_le (x + z) z
          rw [add_sub_cancel_right] at htri
          have hzx : ‖x‖ / 2 ≤ ‖z‖ := by linarith
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos hx2 hzx (by linarith)) (norm_nonneg _)
      unfold fractionalPowerAt
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (norm_integral_le_of_norm_le hgi (ae_of_all _ hpt)).trans (le_of_eq ?_)
      rw [integral_const_mul, integral_add_left_eq_self (f := fun y : Space => ‖ϕ y‖) x]
    have hpow0 : ∀ x : Space, 0 ≤ (1 + ‖x‖) ^ (-(3 + 2 * α)) := fun x =>
      Real.rpow_nonneg (by positivity) _
    set C1 : ℝ := A / (1 + 2 * R) ^ (-(3 + 2 * α)) with hC1
    set C2 : ℝ := |(fractionalNormalizer α)⁻¹| * L * (1 / 4 : ℝ) ^ (-(3 + 2 * α)) with hC2
    refine ⟨max C1 C2, fun x => ?_⟩
    by_cases hx : 2 * R ≤ ‖x‖
    · refine (hfarx x hx).trans ?_
      refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right C1 C2) (hpow0 x))
      have hL0 : 0 ≤ L := integral_nonneg fun y => norm_nonneg _
      have hx1 : 1 ≤ ‖x‖ := by linarith
      have hq : (‖x‖ / 2) ^ (-(3 + 2 * α)) ≤ ((1 + ‖x‖) * (1 / 4)) ^ (-(3 + 2 * α)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      rw [Real.mul_rpow (by positivity) (by norm_num)] at hq
      rw [hC2]
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hL0)
        (abs_nonneg (fractionalNormalizer α)⁻¹)
      linarith
    · have hx' : ‖x‖ < 2 * R := not_le.1 hx
      have hp : 0 < (1 + 2 * R) ^ (-(3 + 2 * α)) := Real.rpow_pos_of_pos (by linarith) _
      have hle : (1 + 2 * R) ^ (-(3 + 2 * α)) ≤ (1 + ‖x‖) ^ (-(3 + 2 * α)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have hC10 : 0 ≤ C1 := div_nonneg hA0 hp.le
      calc ‖fractionalPowerAt α ϕ x‖ ≤ A := hunif x
        _ = C1 * (1 + 2 * R) ^ (-(3 + 2 * α)) := by rw [hC1, div_mul_cancel₀ _ hp.ne']
        _ ≤ C1 * (1 + ‖x‖) ^ (-(3 + 2 * α)) := mul_le_mul_of_nonneg_left hle hC10
        _ ≤ max C1 C2 * (1 + ‖x‖) ^ (-(3 + 2 * α)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (hpow0 x)

end Breakdown
