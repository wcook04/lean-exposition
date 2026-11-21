import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal NNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem finrank_space : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin

private theorem hs_space : ∃ S : ℝ≥0, ∀ u : Space → Space, ContDiff ℝ 1 u →
    HasCompactSupport u →
      eLpNorm u (6 : ℝ≥0) volume ≤ S * eLpNorm (fderiv ℝ u) (2 : ℝ≥0) volume := by
  refine ⟨_, fun u hu hc => eLpNorm_le_eLpNorm_fderiv_of_eq (μ := volume) hu hc ?_ ?_ ?_⟩
  · norm_num
  · rw [finrank_space]; norm_num
  · rw [finrank_space]; norm_num

private theorem opNorm_le_sqrt_sum (L : Space →L[ℝ] Space) :
    ‖L‖ ≤ Real.sqrt (∑ i, ‖L (unitVector i)‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  have hv : v = ∑ i, v i • unitVector i := by
    simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v).symm
  calc ‖L v‖ = ‖∑ i, v i • L (unitVector i)‖ := by
        conv_lhs => rw [hv]
        simp only [map_sum, map_smul]
    _ ≤ ∑ i, ‖v i • L (unitVector i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ * ‖L (unitVector i)‖ := by simp only [norm_smul]
    _ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) * Real.sqrt (∑ i, ‖L (unitVector i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by rw [EuclideanSpace.norm_eq v, mul_comm]

private theorem norm_fderiv_cutoffSq_smul_le {r c : ℝ} (hr : 0 < r)
    (hc : ∀ x, ‖fderiv ℝ (radialCutoff r) x‖ ≤ c / r) {w : Space → Space}
    (hw : Differentiable ℝ w) (x : Space) :
    ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x‖ ≤
      Real.sqrt (cutoffPow r x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2) + 2 * c / r * ‖w x‖ := by
  have hη : HasFDerivAt (radialCutoff r) (fderiv ℝ (radialCutoff r) x) x :=
    ((contDiff_radialCutoff hr).differentiable (by simp) x).hasFDerivAt
  have hs : HasFDerivAt (fun y => radialCutoff r y ^ 2 • w y) _ x :=
    (hη.pow 2).smul (hw x).hasFDerivAt
  rw [hs.fderiv]
  have h0 := radialCutoff_nonneg r x
  have h1 := radialCutoff_le_one r x
  have hsq : Real.sqrt (cutoffPow r x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2) =
      radialCutoff r x ^ 2 * Real.sqrt (∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2) := by
    rw [Real.sqrt_mul (by unfold cutoffPow; positivity), cutoffPow,
      show radialCutoff r x ^ 4 = (radialCutoff r x ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (opNorm_le_sqrt_sum _) (by positivity)
  · rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul]
    have hk : ‖((2 : ℕ) • radialCutoff r x ^ (2 - 1) : ℝ)‖ ≤ 2 := by
      rw [nsmul_eq_mul, pow_one, Real.norm_of_nonneg (by positivity)]
      push_cast
      linarith
    calc _ ≤ (2 * (c / r)) * ‖w x‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul hk (hc x) (norm_nonneg _) (by norm_num))
            (norm_nonneg _)
      _ = 2 * c / r * ‖w x‖ := by ring

private theorem eLpNorm_nat_eq {f : Space → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : ∀ x, 0 ≤ f x) {n : ℕ} (hn : n ≠ 0) :
    eLpNorm f ((n : ℝ≥0) : ℝ≥0∞) volume = ENNReal.ofReal ((∫ x, f x ^ n) ^ (1 / (n : ℝ))) := by
  have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
  rw [eLpNorm_nnreal_eq_lintegral hn']
  have hpt : ∀ x, ‖f x‖ₑ ^ ((n : ℝ≥0) : ℝ) = ENNReal.ofReal (f x ^ n) := by
    intro x
    rw [NNReal.coe_natCast, ENNReal.rpow_natCast, Real.enorm_eq_ofReal (h0 x),
      ENNReal.ofReal_pow (h0 x)]
  simp_rw [hpt]
  have hint : Integrable (fun x => f x ^ n) volume :=
    (hf.pow n).integrable_of_hasCompactSupport
      (hc.comp_left (g := fun t : ℝ => t ^ n) (zero_pow hn))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => pow_nonneg (h0 x) n),
    NNReal.coe_natCast, ENNReal.ofReal_rpow_of_nonneg
      (integral_nonneg fun x => pow_nonneg (h0 x) n) (by positivity)]

private theorem eLpNorm_norm_le_of_energy {A : ℝ} {w : Space → Space} (hw : IsFiniteEnergyField A w) :
    eLpNorm (fun x => ‖w x‖) (2 : ℝ≥0) volume ≤ ENNReal.ofReal A := by
  rw [eLpNorm_nnreal_eq_lintegral (by norm_num)]
  have hpt : ∀ x, ‖‖w x‖‖ₑ ^ ((2 : ℝ≥0) : ℝ) = ENNReal.ofReal (‖w x‖ ^ 2) := by
    intro x
    rw [show ((2 : ℝ≥0) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      Real.enorm_eq_ofReal (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
  simp_rw [hpt]
  calc (∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2)) ^ (1 / ((2 : ℝ≥0) : ℝ)) ≤
        ENNReal.ofReal (A ^ 2) ^ (1 / ((2 : ℝ≥0) : ℝ)) :=
        ENNReal.rpow_le_rpow hw.energy (by positivity)
    _ = ENNReal.ofReal A := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
        congr 1
        rw [show ((2 : ℝ≥0) : ℝ) = 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_sq hw.nonneg]

private theorem outside_ball {r : ℝ} {x : Space} (hx : x ∉ Metric.closedBall (0 : Space) (2 * r)) :
    2 * r ≤ ‖x‖ := by
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  exact hx.le

theorem cutoffSixthNorm_le : ∃ S c : ℝ, 0 ≤ S ∧ 0 ≤ c ∧ ∀ (A : ℝ) (w : Space → Space),
    IsFiniteEnergyField A w → ∀ r : ℝ, 1 ≤ r →
      cutoffSixthNorm r w ≤ S * (Real.sqrt (cutoffDissipation r w) + c * A / r) := by
  obtain ⟨S, hS⟩ := hs_space
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have hc0 : 0 ≤ c := by simpa using (norm_nonneg _).trans (hc 1 one_pos 0)
  refine ⟨S, 2 * c, S.coe_nonneg, by positivity, fun A w hw r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hA : 0 ≤ A := hw.nonneg
  have hwd : Differentiable ℝ w := hw.smooth.differentiable (by simp)
  have hηc : ContDiff ℝ ∞ (radialCutoff r) := contDiff_radialCutoff hr0
  have hu1 : ContDiff ℝ 1 (fun x => radialCutoff r x ^ 2 • w x) :=
    ((hηc.pow 2).smul hw.smooth).of_le (by simp)
  have huc : HasCompactSupport (fun x => radialCutoff r x ^ 2 • w x) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * r)) fun x hx => by
      simp [radialCutoff_eq_zero hr0 (outside_ball hx)]
  have hnu : (fun x => ‖radialCutoff r x ^ 2 • w x‖) = fun x => radialCutoff r x ^ 2 * ‖w x‖ := by
    funext x
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (radialCutoff_nonneg r x) 2)]
  have hf6c : Continuous (fun x => radialCutoff r x ^ 2 * ‖w x‖) :=
    (hηc.continuous.pow 2).mul hw.smooth.continuous.norm
  have hf6s : HasCompactSupport (fun x => radialCutoff r x ^ 2 * ‖w x‖) := by
    rw [← hnu]; exact huc.norm
  have h6 : eLpNorm (fun x => radialCutoff r x ^ 2 • w x) (6 : ℝ≥0) volume =
      ENNReal.ofReal (cutoffSixthNorm r w) := by
    rw [← eLpNorm_norm, hnu]
    have := eLpNorm_nat_eq hf6c hf6s (fun x => by positivity) (n := 6) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    rw [this, cutoffSixthNorm]
  have hcp : Continuous (cutoffPow r) := by
    unfold cutoffPow; exact hηc.continuous.pow 4
  have hdw : Continuous (fderiv ℝ w) := hw.smooth.continuous_fderiv (by simp)
  have hGc : Continuous (fun x => Real.sqrt (cutoffPow r x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2)) :=
    (hcp.mul (continuous_finsetSum _ fun i _ =>
      (hdw.clm_apply continuous_const).norm.pow 2)).sqrt
  have hGs : HasCompactSupport
      (fun x => Real.sqrt (cutoffPow r x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2)) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * r)) fun x hx => by
      simp [cutoffPow, radialCutoff_eq_zero hr0 (outside_ball hx)]
  have hint : ∫ x, Real.sqrt (cutoffPow r x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2) ^ 2 =
      cutoffDissipation r w := by
    unfold cutoffDissipation
    congr 1
    funext x
    exact Real.sq_sqrt (by unfold cutoffPow; positivity)
  have hG : eLpNorm (fun x => Real.sqrt (cutoffPow r x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2))
      (2 : ℝ≥0) volume = ENNReal.ofReal (Real.sqrt (cutoffDissipation r w)) := by
    have := eLpNorm_nat_eq hGc hGs (fun x => Real.sqrt_nonneg _) (n := 2) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    rw [this, hint, Real.sqrt_eq_rpow]
  have hpt : ∀ x, ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x‖ ≤
      (fun x => Real.sqrt (cutoffPow r x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2)) x +
        (fun x => 2 * c / r * ‖w x‖) x :=
    fun x => norm_fderiv_cutoffSq_smul_le hr0 (hc r hr0) hwd x
  have hmeasW : AEStronglyMeasurable (fun x => 2 * c / r * ‖w x‖) volume :=
    (continuous_const.mul hw.smooth.continuous.norm).aestronglyMeasurable
  have hD : eLpNorm (fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y)) (2 : ℝ≥0) volume ≤
      ENNReal.ofReal (Real.sqrt (cutoffDissipation r w)) +
        ENNReal.ofReal (2 * c / r) * ENNReal.ofReal A := by
    calc _ ≤ eLpNorm ((fun x => Real.sqrt (cutoffPow r x * ∑ i, ‖fderiv ℝ w x (unitVector i)‖ ^ 2)) +
          fun x => 2 * c / r * ‖w x‖) (2 : ℝ≥0) volume := eLpNorm_mono_real hpt
      _ ≤ _ := eLpNorm_add_le hGc.aestronglyMeasurable hmeasW (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (cutoffDissipation r w)) +
          ENNReal.ofReal (2 * c / r) * eLpNorm (fun x => ‖w x‖) (2 : ℝ≥0) volume := by
          rw [hG]
          congr 1
          rw [show (fun x => 2 * c / r * ‖w x‖) = (2 * c / r) • fun x => ‖w x‖ from rfl,
            eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
      _ ≤ _ := by gcongr; exact eLpNorm_norm_le_of_energy hw
  have key : ENNReal.ofReal (cutoffSixthNorm r w) ≤
      ENNReal.ofReal (S * (Real.sqrt (cutoffDissipation r w) + 2 * c * A / r)) := by
    rw [← h6]
    calc _ ≤ S * eLpNorm (fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y)) (2 : ℝ≥0) volume :=
          hS _ hu1 huc
      _ ≤ S * (ENNReal.ofReal (Real.sqrt (cutoffDissipation r w)) +
          ENNReal.ofReal (2 * c / r) * ENNReal.ofReal A) := by gcongr
      _ = _ := by
          rw [show 2 * c * A / r = 2 * c / r * A by ring, ENNReal.ofReal_mul S.coe_nonneg,
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_add (Real.sqrt_nonneg _) (by positivity),
            ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

end Breakdown
