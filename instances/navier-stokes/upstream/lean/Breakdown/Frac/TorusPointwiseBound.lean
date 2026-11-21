import Breakdown.Frac.StTorusApprox
import Breakdown.Frac.StOperator

open MeasureTheory Set Real Metric
open scoped ContDiff

noncomputable section

namespace Breakdown.FracInternal

private def radialConst : ℝ := 3 * volume.real (ball (0 : Space) 1)

private lemma radialConst_pos : 0 < radialConst := by
  unfold radialConst
  have : 0 < volume.real (ball (0 : Space) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : Space) one_pos).ne' measure_ball_lt_top.ne
  positivity

private lemma radial_aux (g : ℝ → ℝ) (hg : IntegrableOn (fun y => y ^ 2 * g y) (Ioi 0)) :
    Integrable (fun z : Space => g ‖z‖) ∧
      ∫ z : Space, g ‖z‖ = radialConst * ∫ y in Ioi (0 : ℝ), y ^ 2 * g y := by
  have hd : Module.finrank ℝ Space - 1 = 2 := by simp
  constructor
  · rw [integrable_fun_norm_addHaar volume (f := g), hd]
    simpa [smul_eq_mul] using hg
  · rw [integral_fun_norm_addHaar volume g, hd]
    simp only [smul_eq_mul, nsmul_eq_mul, finrank_euclideanSpace_fin, radialConst]
    push_cast
    ring

private lemma near_radial {s r : ℝ} (hs : -3 < s) (hr : 0 < r) :
    IntegrableOn (fun z : Space => ‖z‖ ^ s) {z | ‖z‖ ≤ r} ∧
      ∫ z in {z : Space | ‖z‖ ≤ r}, ‖z‖ ^ s = radialConst * (r ^ (s + 3) / (s + 3)) := by
  have hm : MeasurableSet {z : Space | ‖z‖ ≤ r} := measurableSet_le measurable_norm measurable_const
  have hpt : ∀ z : Space, {z : Space | ‖z‖ ≤ r}.indicator (fun z => ‖z‖ ^ s) z =
      (Iic r).indicator (fun y => y ^ s) ‖z‖ := by
    intro z
    simp only [Set.indicator_apply, mem_ofPred_eq, mem_Iic]
  have hcongr : ∀ y ∈ Ioc (0 : ℝ) r, y ^ 2 * y ^ s = y ^ (s + 2) := by
    intro y hy
    rw [rpow_add hy.1, mul_comm, ← rpow_natCast]
    norm_num
  have hIoc : IntegrableOn (fun y : ℝ => y ^ 2 * y ^ s) (Ioc 0 r) := by
    have h1 : IntegrableOn (fun y : ℝ => y ^ (s + 2)) (Ioc 0 r) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    exact h1.congr_fun (fun y hy => (hcongr y hy).symm) measurableSet_Ioc
  have hind : (fun y : ℝ => y ^ 2 * (Iic r).indicator (fun y => y ^ s) y) =
      (Iic r).indicator (fun y => y ^ 2 * y ^ s) := by
    funext y
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  have hg : IntegrableOn (fun y : ℝ => y ^ 2 * (Iic r).indicator (fun y => y ^ s) y) (Ioi 0) := by
    rw [hind, IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic, inter_comm, Ioi_inter_Iic]
    exact hIoc
  obtain ⟨hi, he⟩ := radial_aux _ hg
  constructor
  · rw [← integrable_indicator_iff hm]
    exact hi.congr (Filter.Eventually.of_forall fun z => (hpt z).symm)
  · rw [← integral_indicator hm]
    simp_rw [hpt]
    rw [he, hind, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
      setIntegral_congr_fun measurableSet_Ioc hcongr, ← intervalIntegral.integral_of_le hr.le,
      integral_rpow (Or.inl (by linarith)), zero_rpow (by linarith)]
    congr 1
    ring_nf

private lemma far_radial {s r : ℝ} (hs : s < -3) (hr : 0 < r) :
    IntegrableOn (fun z : Space => ‖z‖ ^ s) {z | r < ‖z‖} ∧
      ∫ z in {z : Space | r < ‖z‖}, ‖z‖ ^ s = radialConst * (r ^ (s + 3) / (-(s + 3))) := by
  have hm : MeasurableSet {z : Space | r < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hpt : ∀ z : Space, {z : Space | r < ‖z‖}.indicator (fun z => ‖z‖ ^ s) z =
      (Ioi r).indicator (fun y => y ^ s) ‖z‖ := by
    intro z
    simp only [Set.indicator_apply, mem_ofPred_eq, mem_Ioi]
  have hcongr : ∀ y ∈ Ioi r, y ^ 2 * y ^ s = y ^ (s + 2) := by
    intro y hy
    rw [rpow_add (hr.trans hy), mul_comm, ← rpow_natCast]
    norm_num
  have hIoi : IntegrableOn (fun y : ℝ => y ^ 2 * y ^ s) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hr).congr_fun (fun y hy => (hcongr y hy).symm)
      measurableSet_Ioi
  have hind : (fun y : ℝ => y ^ 2 * (Ioi r).indicator (fun y => y ^ s) y) =
      (Ioi r).indicator (fun y => y ^ 2 * y ^ s) := by
    funext y
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  have hset : Ioi r ∩ Ioi (0 : ℝ) = Ioi r := by
    rw [Ioi_inter_Ioi, max_eq_left hr.le]
  have hg : IntegrableOn (fun y : ℝ => y ^ 2 * (Ioi r).indicator (fun y => y ^ s) y) (Ioi 0) := by
    rw [hind, IntegrableOn, integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioi, hset]
    exact hIoi
  obtain ⟨hi, he⟩ := radial_aux _ hg
  constructor
  · rw [← integrable_indicator_iff hm]
    exact hi.congr (Filter.Eventually.of_forall fun z => (hpt z).symm)
  · rw [← integral_indicator hm]
    simp_rw [hpt]
    rw [he, hind, setIntegral_indicator measurableSet_Ioi, inter_comm, hset,
      setIntegral_congr_fun measurableSet_Ioi hcongr, integral_Ioi_rpow_of_lt (by linarith) hr]
    have : s + 2 + 1 = s + 3 := by ring
    rw [this, neg_div, div_neg]

end Breakdown.FracInternal

namespace Breakdown.FracInternal

private lemma far_le {α s r : ℝ} (h1 : 1 < α) (hs1 : -(3 + 2 * α) ≤ s) (hs2 : s ≤ -(3 + 2 * α) + 2)
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IntegrableOn (fun z : Space => ‖z‖ ^ s) {z | r < ‖z‖} ∧
      ∫ z in {z : Space | r < ‖z‖}, ‖z‖ ^ s ≤ radialConst * (r ^ (-(2 * α)) / (2 * α - 2)) := by
  obtain ⟨hi, he⟩ := far_radial (s := s) (by linarith) hr0
  refine ⟨hi, ?_⟩
  rw [he]
  have hc := radialConst_pos
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply div_le_div₀ (rpow_nonneg hr0.le _)
  · exact rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
  · linarith
  · linarith

private lemma remainder_far_le (f : Space → Space) (x z : Space) (A : ℝ) (hA : 0 ≤ A)
    (hA0 : ‖f x‖ ≤ A) (hA1 : ‖fderiv ℝ f x‖ ≤ A) (hA2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ A) :
    ‖secondOrderRemainder f x z‖ ≤ ‖f (x + z)‖ + A + A * ‖z‖ + A * ‖z‖ ^ 2 := by
  unfold secondOrderRemainder
  have e1 := norm_sub_le (f (x + z) - f x - fderiv ℝ f x z)
    ((1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z])
  have e2 := norm_sub_le (f (x + z) - f x) (fderiv ℝ f x z)
  have e3 := norm_sub_le (f (x + z)) (f x)
  have e4 : ‖fderiv ℝ f x z‖ ≤ A * ‖z‖ :=
    ((fderiv ℝ f x).le_opNorm z).trans (mul_le_mul_of_nonneg_right hA1 (norm_nonneg _))
  have e5 : ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ 2 f x ![z, z]‖ ≤ A * ‖z‖ ^ 2 := by
    rw [norm_smul]
    have h := (iteratedFDeriv ℝ 2 f x).le_opNorm ![z, z]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hn : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [hn]
    have hzz : 0 ≤ ‖z‖ * ‖z‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h' : ‖iteratedFDeriv ℝ 2 f x‖ * (‖z‖ * ‖z‖) ≤ A * (‖z‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_right hA2 hzz
    have h'' : 0 ≤ A * (‖z‖ * ‖z‖) := mul_nonneg hA hzz
    nlinarith
  linarith

end Breakdown.FracInternal

namespace Breakdown.Periodic

open Breakdown.FracInternal

theorem fracPointwiseBound_of (α : ℝ) (h1 : 1 < α) (h2 : α < 3 / 2) (hR : RemainderBoundStatement)
    (hN : NormalizerStatement) : FracPointwiseBound α := by
  obtain ⟨-, hM⟩ := hN α h1 (by linarith)
  have hc := radialConst_pos
  have hd1 : 0 < 3 - 2 * α := by linarith
  have hd2 : 0 < 2 * α - 2 := by linarith
  refine ⟨(fractionalNormalizer α)⁻¹ * (radialConst / (3 - 2 * α) + 3 * radialConst / (2 * α - 2) + 1),
    by positivity, ?_⟩
  intro f hf x r A B L hr0 hr1 hI hB hA0 hA1 hA2 hLi hL
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x (mem_closedBall_self hr0.le))
  have hA : 0 ≤ A := (norm_nonneg _).trans hA0
  have hL0 : 0 ≤ L := (integral_nonneg fun z =>
    mul_nonneg (rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)).trans hL
  have hFeq : (fun z : Space => ‖‖z‖ ^ (-(3 + 2 * α)) • secondOrderRemainder f x z‖) =
      fun z => ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖ := by
    funext z
    rw [norm_smul, norm_of_nonneg (rpow_nonneg (norm_nonneg _) _)]
  have hFi : Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖) := by
    rw [← hFeq]
    exact hI.norm
  have hmfar : MeasurableSet {z : Space | r < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hmnear : MeasurableSet {z : Space | ‖z‖ ≤ r} :=
    measurableSet_le measurable_norm measurable_const
  have hcompl : {z : Space | r < ‖z‖}ᶜ = {z : Space | ‖z‖ ≤ r} := by
    ext z
    simp [not_lt]
  have hne : -(3 + 2 * α) ≠ 0 := by linarith
  have hnear : ∫ z in {z : Space | ‖z‖ ≤ r}, ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖ ≤
      B * (radialConst * (r ^ (3 - 2 * α) / (3 - 2 * α))) := by
    obtain ⟨hi, he⟩ := near_radial (s := -(3 + 2 * α) + 3) (by linarith) hr0
    have hex : -(3 + 2 * α) + 3 + 3 = 3 - 2 * α := by ring
    rw [hex] at he
    rw [← he, ← integral_const_mul]
    refine setIntegral_mono_on hFi.integrableOn (hi.const_mul B) hmnear fun z hz => ?_
    have hz' : ‖z‖ ≤ r := hz
    have hRemz := hR f hf x z B fun y hy => hB y (closedBall_subset_closedBall hz' hy)
    rcases eq_or_ne z 0 with rfl | hz0
    · rw [norm_zero, zero_rpow hne, zero_rpow (by linarith), zero_mul, mul_zero]
    · have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
      have h3 : ‖z‖ ^ (3 : ℝ) = ‖z‖ ^ (3 : ℕ) := by exact_mod_cast rpow_natCast ‖z‖ 3
      calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖
          ≤ ‖z‖ ^ (-(3 + 2 * α)) * (B * ‖z‖ ^ 3) :=
            mul_le_mul_of_nonneg_left hRemz (rpow_nonneg (norm_nonneg _) _)
        _ = B * ‖z‖ ^ (-(3 + 2 * α) + 3) := by rw [rpow_add hpos, h3]; ring
  have hfar : ∫ z in {z : Space | r < ‖z‖}, ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖ ≤
      L + A * (3 * (radialConst * (r ^ (-(2 * α)) / (2 * α - 2)))) := by
    obtain ⟨i0, b0⟩ := far_le (s := -(3 + 2 * α)) h1 le_rfl (by linarith) hr0 hr1
    obtain ⟨i1, b1⟩ := far_le (s := -(3 + 2 * α) + 1) h1 (by linarith) (by linarith) hr0 hr1
    obtain ⟨i2, b2⟩ := far_le (s := -(3 + 2 * α) + 2) h1 (by linarith) le_rfl hr0 hr1
    have i01 : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) + ‖z‖ ^ (-(3 + 2 * α) + 1))
        {z | r < ‖z‖} := i0.add i1
    have i012 : IntegrableOn (fun z : Space => ‖z‖ ^ (-(3 + 2 * α)) + ‖z‖ ^ (-(3 + 2 * α) + 1) +
        ‖z‖ ^ (-(3 + 2 * α) + 2)) {z | r < ‖z‖} := i01.add i2
    have hsum : IntegrableOn (fun z : Space => A * (‖z‖ ^ (-(3 + 2 * α)) +
        ‖z‖ ^ (-(3 + 2 * α) + 1) + ‖z‖ ^ (-(3 + 2 * α) + 2))) {z | r < ‖z‖} := i012.const_mul A
    calc ∫ z in {z : Space | r < ‖z‖}, ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖
        ≤ ∫ z in {z : Space | r < ‖z‖}, (‖z‖ ^ (-(3 + 2 * α)) * ‖f (x + z)‖ +
            A * (‖z‖ ^ (-(3 + 2 * α)) + ‖z‖ ^ (-(3 + 2 * α) + 1) + ‖z‖ ^ (-(3 + 2 * α) + 2))) := by
          refine setIntegral_mono_on hFi.integrableOn (hLi.add hsum) hmfar fun z hz => ?_
          have hz' : r < ‖z‖ := hz
          have hpos : 0 < ‖z‖ := hr0.trans hz'
          have hRemz := remainder_far_le f x z A hA hA0 hA1 hA2
          have h2' : ‖z‖ ^ (2 : ℝ) = ‖z‖ ^ (2 : ℕ) := by exact_mod_cast rpow_natCast ‖z‖ 2
          rw [rpow_add hpos, rpow_add hpos, rpow_one, h2']
          have hK := rpow_nonneg (norm_nonneg z) (-(3 + 2 * α))
          calc ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖
              ≤ ‖z‖ ^ (-(3 + 2 * α)) * (‖f (x + z)‖ + A + A * ‖z‖ + A * ‖z‖ ^ 2) :=
                mul_le_mul_of_nonneg_left hRemz hK
            _ = _ := by ring
      _ = (∫ z in {z : Space | r < ‖z‖}, ‖z‖ ^ (-(3 + 2 * α)) * ‖f (x + z)‖) +
            A * ((∫ z in {z : Space | r < ‖z‖}, ‖z‖ ^ (-(3 + 2 * α))) +
              (∫ z in {z : Space | r < ‖z‖}, ‖z‖ ^ (-(3 + 2 * α) + 1)) +
              ∫ z in {z : Space | r < ‖z‖}, ‖z‖ ^ (-(3 + 2 * α) + 2)) := by
          rw [integral_add hLi hsum, integral_const_mul, integral_add i01 i2,
            integral_add i0 i1]
      _ ≤ L + A * (3 * (radialConst * (r ^ (-(2 * α)) / (2 * α - 2)))) := by
          have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add b0 b1) b2) hA
          linarith
  have htot : ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖ ≤
      B * (radialConst * (r ^ (3 - 2 * α) / (3 - 2 * α))) +
        (L + A * (3 * (radialConst * (r ^ (-(2 * α)) / (2 * α - 2))))) := by
    rw [← integral_add_compl hmfar hFi, hcompl]
    linarith
  have hnorm : ‖fractionalPowerAt α f x‖ ≤ (fractionalNormalizer α)⁻¹ *
      ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖ := by
    unfold fractionalPowerAt
    rw [norm_smul, norm_of_nonneg (inv_nonneg.2 hM.le), ← hFeq]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.2 hM.le)
  set X := r ^ (3 - 2 * α)
  set Y := r ^ (-(2 * α))
  have hX : 0 ≤ X := rpow_nonneg hr0.le _
  have hY : 0 ≤ Y := rpow_nonneg hr0.le _
  set p := radialConst / (3 - 2 * α)
  set q := 3 * radialConst / (2 * α - 2)
  have hp : 0 ≤ p := by positivity
  have hq : 0 ≤ q := by positivity
  have hbound : B * (radialConst * (X / (3 - 2 * α))) +
      (L + A * (3 * (radialConst * (Y / (2 * α - 2))))) = p * (B * X) + q * (A * Y) + L := by
    simp only [p, q]
    ring
  have key : p * (B * X) + q * (A * Y) + L ≤ (p + q + 1) * (B * X + A * Y + L) := by
    have a1 : 0 ≤ p * (A * Y + L) := mul_nonneg hp (by positivity)
    have a2 : 0 ≤ q * (B * X + L) := mul_nonneg hq (by positivity)
    have a3 : 0 ≤ B * X := mul_nonneg hB0 hX
    have a4 : 0 ≤ A * Y := mul_nonneg hA hY
    nlinarith
  calc ‖fractionalPowerAt α f x‖ ≤ (fractionalNormalizer α)⁻¹ *
      ∫ z, ‖z‖ ^ (-(3 + 2 * α)) * ‖secondOrderRemainder f x z‖ := hnorm
    _ ≤ (fractionalNormalizer α)⁻¹ * (p * (B * X) + q * (A * Y) + L) := by
        rw [← hbound]
        exact mul_le_mul_of_nonneg_left htot (inv_nonneg.2 hM.le)
    _ ≤ (fractionalNormalizer α)⁻¹ * ((p + q + 1) * (B * X + A * Y + L)) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.2 hM.le)
    _ = (fractionalNormalizer α)⁻¹ * (p + q + 1) * (B * X + A * Y + L) := by ring

end Breakdown.Periodic
