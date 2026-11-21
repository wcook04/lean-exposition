import Breakdown.Cert.CoerciveSmoothPiecePairingSplitWeight
import Breakdown.Cert.CoerciveTestDensityCurl

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothWeightSplit

open ModeL2Internal (IsSquareField slab slab_ac periodLIntegral_eq_slab)

def unitBump : ContDiffBump (0 : Space) := ⟨1, 2, by norm_num, by norm_num⟩

def cut (n : ℕ) (y : Space) : ℝ := unitBump (((n : ℝ) + 1)⁻¹ • y)

def cutField (n : ℕ) (F : ℝ → Space → Space) : ℝ → Space → Space := fun σ y => cut n y • F σ y

theorem cut_contDiff (n : ℕ) : ContDiff ℝ ∞ (cut n) :=
  unitBump.contDiff.comp (contDiff_id.const_smul _)

theorem cut_nonneg (n : ℕ) (y : Space) : 0 ≤ cut n y := unitBump.nonneg

theorem cut_le_one (n : ℕ) (y : Space) : cut n y ≤ 1 := unitBump.le_one

theorem cut_far (n : ℕ) (y : Space) (hy : 2 * ((n : ℝ) + 1) < ‖y‖) : cut n y = 0 := by
  unfold cut
  apply unitBump.zero_of_le_dist
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
  show (2 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ * ‖y‖
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith

theorem cut_eventually_one (y : Space) : ∀ᶠ n : ℕ in atTop, cut n =ᶠ[𝓝 y] fun _ => 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (‖y‖ + 1)
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  filter_upwards [Metric.ball_mem_nhds y one_pos] with x hx
  unfold cut
  apply unitBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos),
    inv_mul_eq_div]
  show ‖x‖ / ((n : ℝ) + 1) ≤ 1
  rw [div_le_one hpos]
  have h1 : ‖x‖ < ‖y‖ + 1 := by
    have := norm_le_norm_add_norm_sub' x y
    rw [Metric.mem_ball, dist_eq_norm] at hx
    linarith
  linarith

theorem cut_fderiv_bound : ∃ K, 0 ≤ K ∧ ∀ n y, ‖fderiv ℝ (cut n) y‖ ≤ K := by
  have hc : Continuous (fderiv ℝ (unitBump : Space → ℝ)) :=
    (unitBump.contDiff (n := 1)).continuous_fderiv (by norm_num)
  obtain ⟨K, hK⟩ := hc.bounded_above_of_compact_support (unitBump.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨max K 0, le_max_right _ _, fun n y => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set c : ℝ := ((n : ℝ) + 1)⁻¹ with hcdef
  have hd : HasFDerivAt (cut n) ((fderiv ℝ (unitBump : Space → ℝ) (c • y)).comp (c • ContinuousLinearMap.id ℝ Space)) y := by
    have h1 : HasFDerivAt (fun x : Space => c • x) (c • ContinuousLinearMap.id ℝ Space) y :=
      (hasFDerivAt_id y).const_smul c
    have h2 : HasFDerivAt (unitBump : Space → ℝ) (fderiv ℝ (unitBump : Space → ℝ) (c • y)) (c • y) :=
      ((unitBump.contDiff (n := 1)).differentiable (by norm_num) _).hasFDerivAt
    exact h2.comp y h1
  rw [hd.fderiv]
  have hc1 : ‖c • ContinuousLinearMap.id ℝ Space‖ ≤ 1 := by
    refine (norm_smul_le _ _).trans ?_
    have hc0 : ‖c‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
      exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    calc ‖c‖ * ‖ContinuousLinearMap.id ℝ Space‖ ≤ 1 * 1 :=
          mul_le_mul hc0 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc ‖(fderiv ℝ (unitBump : Space → ℝ) (c • y)).comp (c • ContinuousLinearMap.id ℝ Space)‖
      ≤ ‖fderiv ℝ (unitBump : Space → ℝ) (c • y)‖ * ‖c • ContinuousLinearMap.id ℝ Space‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ max K 0 * 1 := mul_le_mul ((hK _).trans (le_max_left _ _)) hc1 (norm_nonneg _) (le_max_right _ _)
    _ = max K 0 := mul_one _

theorem cutField_contDiff (n : ℕ) {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) :
    ContDiff ℝ 1 (fun z : ℝ × Space => cutField n F z.1 z.2) :=
  (((cut_contDiff n).of_le (by simp)).comp contDiff_snd).smul hF

theorem cutField_periodic (n : ℕ) {F : ℝ → Space → Space} (hp : IsTimePeriodic F) :
    IsTimePeriodic (cutField n F) := fun σ y => by
  unfold cutField
  rw [hp σ y]

theorem cutField_far (n : ℕ) (F : ℝ → Space → Space) :
    ∃ R, ∀ σ y, R < ‖y‖ → cutField n F σ y = 0 :=
  ⟨2 * ((n : ℝ) + 1), fun σ y hy => by
    unfold cutField
    rw [cut_far n y hy, zero_smul]⟩

theorem curlVec_sub (G K : Space →L[ℝ] Space) : curlVec G - curlVec K = curlVec (G - K) := by
  unfold curlVec
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_smul]
  congr 1
  simp only [sub_apply, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]

theorem norm_sub_sq_le (a b c : Space) : ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
  have h : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := norm_sub_le_norm_sub_add_norm_sub a b c
  have h2 : ‖a - c‖ ^ 2 ≤ (‖a - b‖ + ‖b - c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_add_le_two ‖a - b‖ ‖b - c‖]

theorem periodLIntegral_triangle {X Y Z : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume)
    (hZ : AEStronglyMeasurable (fun z : ℝ × Space => Z z.1 z.2) volume) :
    periodLIntegral (fun σ y => ‖X σ y - Z σ y‖ ^ 2) ≤
      2 * periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2) + 2 * periodLIntegral (fun σ y => ‖Y σ y - Z σ y‖ ^ 2) := by
  have mXZ := ((hX.sub hZ).norm.pow 2).mono_ac slab_ac
  have mXY := ((hX.sub hY).norm.pow 2).mono_ac slab_ac
  have mYZ := ((hY.sub hZ).norm.pow 2).mono_ac slab_ac
  rw [periodLIntegral_eq_slab (fun σ y => ‖X σ y - Z σ y‖ ^ 2) mXZ,
    periodLIntegral_eq_slab (fun σ y => ‖X σ y - Y σ y‖ ^ 2) mXY,
    periodLIntegral_eq_slab (fun σ y => ‖Y σ y - Z σ y‖ ^ 2) mYZ,
    ← lintegral_const_mul' _ _ (by norm_num), ← lintegral_const_mul' _ _ (by norm_num)]
  have hm : AEMeasurable (fun z : ℝ × Space => 2 * ENNReal.ofReal (‖X z.1 z.2 - Y z.1 z.2‖ ^ 2)) slab :=
    (mXY.aemeasurable.ennreal_ofReal).const_mul 2
  rw [← lintegral_add_left' hm]
  refine lintegral_mono fun z => ?_
  have h := norm_sub_sq_le (X z.1 z.2) (Y z.1 z.2) (Z z.1 z.2)
  calc ENNReal.ofReal (‖X z.1 z.2 - Z z.1 z.2‖ ^ 2)
      ≤ ENNReal.ofReal (2 * ‖X z.1 z.2 - Y z.1 z.2‖ ^ 2 + 2 * ‖Y z.1 z.2 - Z z.1 z.2‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = 2 * ENNReal.ofReal (‖X z.1 z.2 - Y z.1 z.2‖ ^ 2) + 2 * ENNReal.ofReal (‖Y z.1 z.2 - Z z.1 z.2‖ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

theorem cutField_tendsto {F : ℝ → Space → Space} (hF : Continuous (fun z : ℝ × Space => F z.1 z.2))
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) :
    Tendsto (fun n => periodLIntegral (fun σ y => ‖cutField n F σ y - F σ y‖ ^ 2)) atTop (𝓝 0) := by
  have hc : ∀ n, Continuous (fun z : ℝ × Space => cutField n F z.1 z.2 - F z.1 z.2) := fun n =>
    ((((cut_contDiff n).continuous.comp continuous_snd)).smul hF).sub hF
  have e : ∀ n, periodLIntegral (fun σ y => ‖cutField n F σ y - F σ y‖ ^ 2)
      = ∫⁻ z, ENNReal.ofReal (‖cutField n F z.1 z.2 - F z.1 z.2‖ ^ 2) ∂slab := fun n =>
    periodLIntegral_eq_slab _ ((hc n).norm.pow 2).aestronglyMeasurable
  simp_rw [e]
  rw [periodLIntegral_eq_slab _ (hF.norm.pow 2).aestronglyMeasurable] at hF2
  have h0 : (0 : ℝ≥0∞) = ∫⁻ _z, (0 : ℝ≥0∞) ∂slab := lintegral_zero.symm
  rw [h0]
  refine tendsto_lintegral_of_dominated_convergence' (fun z => ENNReal.ofReal (‖F z.1 z.2‖ ^ 2))
    (fun n => ((hc n).norm.pow 2).aestronglyMeasurable.aemeasurable.ennreal_ofReal) (fun n => ae_of_all _ fun z => ?_)
    hF2.ne (ae_of_all _ fun z => ?_)
  · refine ENNReal.ofReal_le_ofReal ?_
    have e1 : cutField n F z.1 z.2 - F z.1 z.2 = (cut n z.2 - 1) • F z.1 z.2 := by
      unfold cutField
      rw [sub_smul, one_smul]
    rw [e1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h1 := cut_nonneg n z.2
    have h2 := cut_le_one n z.2
    have h3 : (cut n z.2 - 1) ^ 2 ≤ 1 := by nlinarith
    exact mul_le_of_le_one_left (by positivity) h3
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [cut_eventually_one z.2] with n hn
    unfold cutField
    rw [hn.eq_of_nhds, one_smul, sub_self, norm_zero]
    simp

theorem fderiv_cutField_sub (n : ℕ) {F : Space → Space} (hF : Differentiable ℝ F) (y : Space) :
    fderiv ℝ (fun x => cut n x • F x) y - fderiv ℝ F y
      = (cut n y - 1) • fderiv ℝ F y + (fderiv ℝ (cut n) y).smulRight (F y) := by
  have e : (fun x => cut n x • F x) = cut n • F := rfl
  rw [e, fderiv_smul (((cut_contDiff n).differentiable (by simp)) y) (hF y), sub_smul, one_smul]
  abel

theorem curl_cutField_tendsto {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2))
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hFd : periodLIntegral (fun σ y => matSq (fderiv ℝ (F σ) y)) < ⊤) :
    Tendsto (fun n => periodLIntegral (fun σ y =>
      ‖curlVec (fderiv ℝ (cutField n F σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := cut_fderiv_bound
  have hFc : Continuous (fun z : ℝ × Space => F z.1 z.2) := hF.continuous
  have hdF : Continuous (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) :=
    (PairingSplitInternal.contDiff_slice (V := F) (n := 0) hF (by norm_num)).continuous
  have hsl : ∀ σ, Differentiable ℝ (F σ) := fun σ =>
    ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num))
  have hc : ∀ n, Continuous (fun z : ℝ × Space =>
      curlVec (fderiv ℝ (cutField n F z.1) z.2) - curlVec (fderiv ℝ (F z.1) z.2)) := fun n =>
    (PairingSplitInternal.continuous_curl (cutField_contDiff n hF)).sub (PairingSplitInternal.continuous_curl hF)
  have e : ∀ n, periodLIntegral (fun σ y =>
      ‖curlVec (fderiv ℝ (cutField n F σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)
      = ∫⁻ z, ENNReal.ofReal (‖curlVec (fderiv ℝ (cutField n F z.1) z.2)
          - curlVec (fderiv ℝ (F z.1) z.2)‖ ^ 2) ∂slab := fun n =>
    periodLIntegral_eq_slab _ ((hc n).norm.pow 2).aestronglyMeasurable
  simp_rw [e]
  have mF := (hFc.norm.pow 2).aestronglyMeasurable (μ := slab)
  have mD := (Internal.PerturbationFacts.continuous_matNorm.comp hdF).aestronglyMeasurable (μ := slab)
  rw [periodLIntegral_eq_slab _ mF] at hF2
  rw [periodLIntegral_eq_slab _ mD] at hFd
  have hfin : ∫⁻ z, (ENNReal.ofReal (4374 * matSq (fderiv ℝ (F z.1) z.2))
      + ENNReal.ofReal (1458 * K ^ 2 * ‖F z.1 z.2‖ ^ 2)) ∂slab ≠ ⊤ := by
    have hm1 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (4374 * matSq (fderiv ℝ (F z.1) z.2))) slab :=
      (mD.aemeasurable.const_mul 4374).ennreal_ofReal
    rw [lintegral_add_left' hm1]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4374)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFd.ne
    · simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1458 * K ^ 2)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF2.ne
  have h0 : (0 : ℝ≥0∞) = ∫⁻ _z, (0 : ℝ≥0∞) ∂slab := lintegral_zero.symm
  rw [h0]
  refine tendsto_lintegral_of_dominated_convergence' _
    (fun n => ((hc n).norm.pow 2).aestronglyMeasurable.aemeasurable.ennreal_ofReal) (fun n => ae_of_all _ fun z => ?_)
    hfin (ae_of_all _ fun z => ?_)
  · have hfr : 0 ≤ matSq (fderiv ℝ (F z.1) z.2) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    show ‖curlVec (fderiv ℝ (fun x => cut n x • F z.1 x) z.2) - curlVec (fderiv ℝ (F z.1) z.2)‖ ^ 2 ≤ _
    rw [curlVec_sub, fderiv_cutField_sub n (hsl z.1) z.2]
    have h1 := norm_curlVec_le ((cut n z.2 - 1) • fderiv ℝ (F z.1) z.2 + (fderiv ℝ (cut n) z.2).smulRight (F z.1 z.2))
    have h2 : ‖(cut n z.2 - 1) • fderiv ℝ (F z.1) z.2 + (fderiv ℝ (cut n) z.2).smulRight (F z.1 z.2)‖
        ≤ ‖fderiv ℝ (F z.1) z.2‖ + K * ‖F z.1 z.2‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        have a1 := cut_nonneg n z.2
        have a2 := cut_le_one n z.2
        have a3 : |cut n z.2 - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        exact mul_le_of_le_one_left (norm_nonneg _) a3
      · rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul_of_nonneg_right (hK n z.2) (norm_nonneg _)
    have h3 := Internal.PerturbationFacts.sq_norm_le_three_matNorm (fderiv ℝ (F z.1) z.2)
    have hA := norm_nonneg (fderiv ℝ (F z.1) z.2)
    have hB := norm_nonneg (F z.1 z.2)
    have hC := norm_nonneg (curlVec ((cut n z.2 - 1) • fderiv ℝ (F z.1) z.2
      + (fderiv ℝ (cut n) z.2).smulRight (F z.1 z.2)))
    have h4 : ‖curlVec ((cut n z.2 - 1) • fderiv ℝ (F z.1) z.2 + (fderiv ℝ (cut n) z.2).smulRight (F z.1 z.2))‖
        ≤ 27 * (‖fderiv ℝ (F z.1) z.2‖ + K * ‖F z.1 z.2‖) := h1.trans (by linarith)
    have h5 := pow_le_pow_left₀ hC h4 2
    have h6 := sq_add_le_two ‖fderiv ℝ (F z.1) z.2‖ (K * ‖F z.1 z.2‖)
    nlinarith
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [cut_eventually_one z.2] with n hn
    have hev : (fun x => cut n x • F z.1 x) =ᶠ[𝓝 z.2] F z.1 := by
      filter_upwards [hn] with x hx
      rw [hx, one_smul]
    show (0 : ℝ≥0∞) = ENNReal.ofReal (‖curlVec (fderiv ℝ (fun x => cut n x • F z.1 x) z.2)
      - curlVec (fderiv ℝ (F z.1) z.2)‖ ^ 2)
    rw [hev.fderiv_eq, sub_self, norm_zero]
    simp

theorem solenoidal_sub {F₁ F₂ Q₁ Q₂ : ℝ → Space → Space}
    (hF₁ : AEStronglyMeasurable (fun z : ℝ × Space => F₁ z.1 z.2) volume)
    (hF₁2 : periodLIntegral (fun σ y => ‖F₁ σ y‖ ^ 2) < ⊤)
    (hF₂ : AEStronglyMeasurable (fun z : ℝ × Space => F₂ z.1 z.2) volume)
    (hF₂2 : periodLIntegral (fun σ y => ‖F₂ σ y‖ ^ 2) < ⊤)
    (h₁ : IsSolenoidalPartOf F₁ Q₁) (h₂ : IsSolenoidalPartOf F₂ Q₂) :
    IsSolenoidalPartOf (fun σ y => F₁ σ y - F₂ σ y) (fun σ y => Q₁ σ y - Q₂ σ y) := by
  have m1 := Internal.TestDensityProof.memLp_of h₁.1 h₁.2.2.1
  have m2 := Internal.TestDensityProof.memLp_of h₂.1 h₂.2.2.1
  have n1 := Internal.TestDensityProof.memLp_of hF₁ hF₁2
  have n2 := Internal.TestDensityProof.memLp_of hF₂ hF₂2
  refine ⟨h₁.1.sub h₂.1, fun σ y => ?_, Internal.CurlGraphDensity.lt_top_of_memLp (m1.sub m2),
    fun q hq => ?_, fun ψ hψ => ?_⟩
  · show Q₁ (σ + 1) y - Q₂ (σ + 1) y = Q₁ σ y - Q₂ σ y
    rw [h₁.2.1 σ y, h₂.2.1 σ y]
  · obtain ⟨R, hR⟩ := hq.2.2
    have hY := Internal.CurlGraphDensity.memLp_of_continuous (Internal.CurlGraphDensity.gradient_continuous hq.1)
      ⟨R, fun σ y hy => Internal.CurlGraphDensity.gradient_vanish hR σ y hy⟩
    rw [Internal.CurlGraphDensity.pairing_sub m1 m2 hY, h₁.2.2.2.1 q hq, h₂.2.2.2.1 q hq, sub_zero]
  · have hY := Internal.CurlGraphDensity.memLp_of_continuous hψ.1.continuous hψ.2.2.1
    rw [Internal.CurlGraphDensity.pairing_sub m1 m2 hY, Internal.CurlGraphDensity.pairing_sub n1 n2 hY,
      h₁.2.2.2.2 ψ hψ, h₂.2.2.2.2 ψ hψ]

theorem solenoidal_diff_le (hSolMode : SolenoidalModeHolds) {F₁ F₂ Q₁ Q₂ : ℝ → Space → Space}
    (hF₁ : AEStronglyMeasurable (fun z : ℝ × Space => F₁ z.1 z.2) volume) (hF₁p : IsTimePeriodic F₁)
    (hF₁2 : periodLIntegral (fun σ y => ‖F₁ σ y‖ ^ 2) < ⊤)
    (hF₂ : AEStronglyMeasurable (fun z : ℝ × Space => F₂ z.1 z.2) volume) (hF₂p : IsTimePeriodic F₂)
    (hF₂2 : periodLIntegral (fun σ y => ‖F₂ σ y‖ ^ 2) < ⊤)
    (h₁ : IsSolenoidalPartOf F₁ Q₁) (h₂ : IsSolenoidalPartOf F₂ Q₂) :
    periodLIntegral (fun σ y => ‖Q₁ σ y - Q₂ σ y‖ ^ 2) ≤ periodLIntegral (fun σ y => ‖F₁ σ y - F₂ σ y‖ ^ 2) := by
  have hD := solenoidal_sub hF₁ hF₁2 hF₂ hF₂2 h₁ h₂
  have n1 := Internal.TestDensityProof.memLp_of hF₁ hF₁2
  have n2 := Internal.TestDensityProof.memLp_of hF₂ hF₂2
  have hDp : IsTimePeriodic (fun σ y => F₁ σ y - F₂ σ y) := fun σ y => by
    show F₁ (σ + 1) y - F₂ (σ + 1) y = F₁ σ y - F₂ σ y
    rw [hF₁p σ y, hF₂p σ y]
  have hD2 : periodLIntegral (fun σ y => ‖F₁ σ y - F₂ σ y‖ ^ 2) < ⊤ :=
    Internal.CurlGraphDensity.lt_top_of_memLp (n1.sub n2)
  obtain ⟨Q', hQ', hnorm, -, huniq, -⟩ := hSolMode _ (hF₁.sub hF₂) hDp hD2
  have hae := huniq _ hD
  have e : periodLIntegral (fun σ y => ‖Q₁ σ y - Q₂ σ y‖ ^ 2) = periodLIntegral (fun σ y => ‖Q' σ y‖ ^ 2) := by
    refine Internal.CurlGraphDensity.periodLIntegral_congr ?_
    filter_upwards [hae] with z hz
    rw [← hz]
  rw [e]
  unfold periodNorm at hnorm
  have a := (Real.sqrt_le_sqrt_iff ENNReal.toReal_nonneg).1 hnorm
  exact (ENNReal.toReal_le_toReal hQ'.2.2.1.ne hD2.ne).1 a

theorem curlGraphDensityL2 (hSolMode : SolenoidalModeHolds) (F Q : ℝ → Space → Space)
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2))
    (hp : IsTimePeriodic F) (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hFd : periodLIntegral (fun σ y => matSq (fderiv ℝ (F σ) y)) < ⊤) (hQ : IsSolenoidalPartOf F Q) :
    ∃ ψ : ℕ → ℝ → Space → Space, (∀ n, IsPeriodicTestField (ψ n)) ∧
      Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun n => periodLIntegral (fun σ y =>
        ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) atTop (𝓝 0) := by
  have hFc := hF.continuous
  have key : ∀ k : ℕ, ∃ ψ : ℝ → Space → Space, IsPeriodicTestField ψ ∧
      periodLIntegral (fun σ y => ‖ψ σ y - Q σ y‖ ^ 2) ≤ 4 * ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∧
      periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (ψ σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)
        ≤ 4 * ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro k
    set δ := ENNReal.ofReal (1 / ((k : ℝ) + 1)) with hδ
    have hδpos : 0 < δ := ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨n, hn1, hn2⟩ := (((tendsto_order.1 (cutField_tendsto hFc hF2)).2 δ hδpos).and
      ((tendsto_order.1 (curl_cutField_tendsto hF hF2 hFd)).2 δ hδpos)).exists
    have hFn := cutField_contDiff n hF
    have hFnp := cutField_periodic n hp
    have hFnR := cutField_far n F
    have hFnm : AEStronglyMeasurable (fun z : ℝ × Space => cutField n F z.1 z.2) volume :=
      hFn.continuous.aestronglyMeasurable
    have hFn2 : periodLIntegral (fun σ y => ‖cutField n F σ y‖ ^ 2) < ⊤ :=
      Internal.CurlGraphDensity.lt_top_of_memLp (Internal.CurlGraphDensity.memLp_of_continuous hFn.continuous hFnR)
    obtain ⟨Qn, hQn, -⟩ := hSolMode _ hFnm hFnp hFn2
    obtain ⟨ψ, hψt, h1, h2⟩ := curlGraphDensityHolds_proof (cutField n F) Qn hFn hFnp hFnR hQn
    obtain ⟨j, hj1, hj2⟩ := (((tendsto_order.1 h1).2 δ hδpos).and ((tendsto_order.1 h2).2 δ hδpos)).exists
    have hψ1 : ContDiff ℝ 1 (fun z : ℝ × Space => ψ j z.1 z.2) := (hψt j).1.of_le (by simp)
    refine ⟨ψ j, hψt j, ?_, ?_⟩
    · have hle := solenoidal_diff_le hSolMode hFnm hFnp hFn2 hFc.aestronglyMeasurable hp hF2 hQn hQ
      calc periodLIntegral (fun σ y => ‖ψ j σ y - Q σ y‖ ^ 2)
          ≤ 2 * periodLIntegral (fun σ y => ‖ψ j σ y - Qn σ y‖ ^ 2)
            + 2 * periodLIntegral (fun σ y => ‖Qn σ y - Q σ y‖ ^ 2) :=
            periodLIntegral_triangle hψ1.continuous.aestronglyMeasurable hQn.1 hQ.1
        _ ≤ 2 * δ + 2 * δ := by
            gcongr
            exact hle.trans hn1.le
        _ = 4 * δ := by ring
    · calc periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (ψ j σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)
          ≤ 2 * periodLIntegral (fun σ y =>
              ‖curlVec (fderiv ℝ (ψ j σ) y) - curlVec (fderiv ℝ (cutField n F σ) y)‖ ^ 2)
            + 2 * periodLIntegral (fun σ y =>
              ‖curlVec (fderiv ℝ (cutField n F σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2) :=
            periodLIntegral_triangle (X := fun σ y => curlVec (fderiv ℝ (ψ j σ) y))
              (Y := fun σ y => curlVec (fderiv ℝ (cutField n F σ) y)) (Z := fun σ y => curlVec (fderiv ℝ (F σ) y))
              (PairingSplitInternal.continuous_curl hψ1).aestronglyMeasurable
              (PairingSplitInternal.continuous_curl hFn).aestronglyMeasurable
              (PairingSplitInternal.continuous_curl hF).aestronglyMeasurable
        _ ≤ 2 * δ + 2 * δ := by
            gcongr
        _ = 4 * δ := by ring
  choose ψ hψt h1 h2 using key
  have hlim : Tendsto (fun k : ℕ => 4 * ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have a : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have b := ENNReal.Tendsto.const_mul a (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))
    rwa [mul_zero] at b
  exact ⟨ψ, hψt, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) h1,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) h2⟩

end Internal.SmoothWeightSplit

end Coercive

end Breakdown
