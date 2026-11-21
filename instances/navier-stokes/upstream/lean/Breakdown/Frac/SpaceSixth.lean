import Breakdown.Frac.StSpace
import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal NNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private theorem sixth_finrank : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin

private theorem sixth_embedding : ∃ S : ℝ≥0, ∀ u : Space → Space, ContDiff ℝ 1 u →
    HasCompactSupport u →
      eLpNorm u (6 : ℝ≥0) volume ≤ S * eLpNorm (fderiv ℝ u) (2 : ℝ≥0) volume := by
  refine ⟨_, fun u hu hc => eLpNorm_le_eLpNorm_fderiv_of_eq (μ := volume) hu hc ?_ ?_ ?_⟩
  · norm_num
  · rw [sixth_finrank]; norm_num
  · rw [sixth_finrank]; norm_num

private theorem sixth_opNorm_le (L : Space →L[ℝ] Space) :
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

private theorem sixth_eLpNorm_nat_eq {f : Space → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
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

private theorem sixth_outside {r : ℝ} {x : Space}
    (hx : x ∉ Metric.closedBall (0 : Space) (2 * r)) : 2 * r ≤ ‖x‖ := by
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  exact hx.le

private theorem sixth_sqrt_le {A D E : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hE : E ≤ A ^ 2 + D) :
    Real.sqrt E ≤ A + Real.sqrt D := by
  have hs : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
  calc Real.sqrt E ≤ Real.sqrt ((A + Real.sqrt D) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hA hs])
    _ = A + Real.sqrt D := Real.sqrt_sq (by positivity)

theorem fracSixthNorm_of (h1 : FracGradientBoundStatement) : FracSixthNormStatement := by
  intro α hα1 hα2
  obtain ⟨S, hS⟩ := sixth_embedding
  refine ⟨S, S.coe_nonneg, fun A w hw r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hA : 0 ≤ A := hw.nonneg
  have hηc : ContDiff ℝ ∞ (radialCutoff r) := contDiff_radialCutoff hr0
  have hWs : ContDiff ℝ ∞ (fun y => radialCutoff r y ^ 2 • w y) := (hηc.pow 2).smul hw.smooth
  have hWc : HasCompactSupport (fun y => radialCutoff r y ^ 2 • w y) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * r)) fun x hx => by
      simp [radialCutoff_eq_zero hr0 (sixth_outside hx)]
  obtain ⟨hD0, hgrad⟩ := h1 α hα1 hα2 _ hWs hWc
  have hDdef : cutoffFracDissipation α r w = ∫ x, inner ℝ (radialCutoff r x ^ 2 • w x)
      (fractionalPowerAt α (fun y => radialCutoff r y ^ 2 • w y) x) := rfl
  rw [hDdef]
  have hdW : Continuous (fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y)) :=
    hWs.continuous_fderiv (by simp)
  have hGc : Continuous (fun x => Real.sqrt
      (∑ i, ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x (unitVector i)‖ ^ 2)) :=
    (continuous_finsetSum _ fun i _ => (hdW.clm_apply continuous_const).norm.pow 2).sqrt
  have hGs : HasCompactSupport (fun x => Real.sqrt
      (∑ i, ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x (unitVector i)‖ ^ 2)) :=
    (hWc.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Space →L[ℝ] Space => Real.sqrt (∑ i, ‖L (unitVector i)‖ ^ 2)) (by simp)
  have hG2 : ∫ x, Real.sqrt
      (∑ i, ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x (unitVector i)‖ ^ 2) ^ 2 =
      ∫ x, ∑ i, ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x (unitVector i)‖ ^ 2 := by
    congr 1
    funext x
    exact Real.sq_sqrt (by positivity)
  have hG : eLpNorm (fun x => Real.sqrt
      (∑ i, ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x (unitVector i)‖ ^ 2))
      (2 : ℝ≥0) volume = ENNReal.ofReal (Real.sqrt
        (∫ x, ∑ i, ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x (unitVector i)‖ ^ 2)) := by
    have := sixth_eLpNorm_nat_eq hGc hGs (fun x => Real.sqrt_nonneg _) (n := 2) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    rw [this, hG2, Real.sqrt_eq_rpow]
  have hdl : eLpNorm (fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y)) (2 : ℝ≥0) volume ≤
      eLpNorm (fun x => Real.sqrt
        (∑ i, ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x (unitVector i)‖ ^ 2))
        (2 : ℝ≥0) volume :=
    eLpNorm_mono_real fun x => sixth_opNorm_le _
  have hpt : ∀ x, ‖radialCutoff r x ^ 2 • w x‖ ≤ ‖w x‖ := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (radialCutoff_nonneg r x) 2)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ (radialCutoff_nonneg r x) (radialCutoff_le_one r x))
  have hW2 : ∫ x, ‖radialCutoff r x ^ 2 • w x‖ ^ 2 ≤ A ^ 2 := by
    have hint : Integrable (fun x => ‖radialCutoff r x ^ 2 • w x‖ ^ 2) volume :=
      (hWs.continuous.norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * r)) fun x hx => by
          simp [radialCutoff_eq_zero hr0 (sixth_outside hx)])
    rw [← ENNReal.ofReal_le_ofReal_iff (sq_nonneg A),
      ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity)]
    refine le_trans (lintegral_mono fun x => ?_) hw.energy
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hpt x) 2)
  have hsq := sixth_sqrt_le hA hD0 (hgrad.trans (by linarith))
  have hnu : (fun x => ‖radialCutoff r x ^ 2 • w x‖) = fun x => radialCutoff r x ^ 2 * ‖w x‖ := by
    funext x
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (radialCutoff_nonneg r x) 2)]
  have hf6c : Continuous (fun x => radialCutoff r x ^ 2 * ‖w x‖) :=
    (hηc.continuous.pow 2).mul hw.smooth.continuous.norm
  have hf6s : HasCompactSupport (fun x => radialCutoff r x ^ 2 * ‖w x‖) := by
    rw [← hnu]; exact hWc.norm
  have h6 : eLpNorm (fun x => radialCutoff r x ^ 2 • w x) (6 : ℝ≥0) volume =
      ENNReal.ofReal (cutoffSixthNorm r w) := by
    rw [← eLpNorm_norm, hnu]
    have := sixth_eLpNorm_nat_eq hf6c hf6s (fun x => by positivity) (n := 6) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    rw [this, cutoffSixthNorm]
  have hu1 : ContDiff ℝ 1 (fun x => radialCutoff r x ^ 2 • w x) := hWs.of_le (by simp)
  have key : ENNReal.ofReal (cutoffSixthNorm r w) ≤
      ENNReal.ofReal (S * (A + Real.sqrt (∫ x, inner ℝ (radialCutoff r x ^ 2 • w x)
        (fractionalPowerAt α (fun y => radialCutoff r y ^ 2 • w y) x)))) := by
    rw [← h6]
    calc _ ≤ S * eLpNorm (fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y)) (2 : ℝ≥0) volume :=
          hS _ hu1 hWc
      _ ≤ S * ENNReal.ofReal (Real.sqrt
          (∫ x, ∑ i, ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x (unitVector i)‖ ^ 2)) := by
          rw [← hG]; gcongr
      _ ≤ S * ENNReal.ofReal (A + Real.sqrt (∫ x, inner ℝ (radialCutoff r x ^ 2 • w x)
          (fractionalPowerAt α (fun y => radialCutoff r y ^ 2 • w y) x))) := by
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul S.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

end Breakdown
