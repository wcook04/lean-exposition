import Breakdown.Cert.ExtendedCoercivePairingSplitAeDiff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral

open scoped ContDiff Convolution
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.WeakMollify

theorem prodVolume_invariantClass : (volume : Measure (ℝ × Space)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

attribute [local instance] prodVolume_invariantClass

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def bump (k : ℕ) : ContDiffBump (0 : ℝ × Space) where
  rIn := 1 / (4 * ((k : ℝ) + 2))
  rOut := 1 / (2 * ((k : ℝ) + 2))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

theorem bump_rOut (k : ℕ) : (bump k).rOut = 1 / (2 * ((k : ℝ) + 2)) := rfl

theorem bump_rIn (k : ℕ) : (bump k).rIn = 1 / (4 * ((k : ℝ) + 2)) := rfl

theorem bump_rOut_le (k : ℕ) : (bump k).rOut ≤ 1 / 2 := by
  rw [bump_rOut]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

theorem bump_rOut_tendsto : Filter.Tendsto (fun k => (bump k).rOut) Filter.atTop (nhds 0) := by
  refine squeeze_zero (fun k => (bump k).rOut_pos.le) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [bump_rOut]
  exact one_div_le_one_div_of_le (by positivity) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

theorem bump_ratio (k : ℕ) : (bump k).rOut ≤ 2 * (bump k).rIn := by
  rw [bump_rOut, bump_rIn]
  have h : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  apply le_of_eq
  field_simp
  ring

def smear (k : ℕ) (F : ℝ → Space → E) (z : ℝ × Space) : E :=
  ((bump k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    (fun u : ℝ × Space => F u.1 u.2)) z

theorem smear_eq (k : ℕ) (F : ℝ → Space → E) (σ : ℝ) (y : Space) :
    smear k F (σ, y) = ∫ t : ℝ × Space, (bump k).normed volume t • F (σ - t.1) (y - t.2) := by
  simp [smear, convolution_def]

theorem integrable_term (k : ℕ) {F : ℝ → Space → E}
    (hF : LocallyIntegrable (fun u : ℝ × Space => F u.1 u.2) volume) (σ : ℝ) (y : Space) :
    Integrable (fun t : ℝ × Space => (bump k).normed volume t • F (σ - t.1) (y - t.2)) volume := by
  have h := ((bump k).hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (bump k).continuous_normed hF (σ, y)
  simpa [ConvolutionExistsAt] using h

theorem hasFDerivAt_smear (k : ℕ) {F : ℝ → Space → E} {F' : ℝ → Space → (Space →L[ℝ] E)} {L : NNReal}
    (hF : LocallyIntegrable (fun u : ℝ × Space => F u.1 u.2) volume)
    (hF' : LocallyIntegrable (fun u : ℝ × Space => F' u.1 u.2) volume)
    (hincr : ∀ s, LipschitzWith L (F s))
    (hd : ∀ᵐ u : ℝ × Space, HasFDerivAt (F u.1) (F' u.1 u.2) u.2) (σ : ℝ) (x₀ : Space) :
    HasFDerivAt (fun x => smear k F (σ, x)) (smear k F' (σ, x₀)) x₀ := by
  simp only [smear_eq]
  have hqmp : Measure.QuasiMeasurePreserving (fun t : ℝ × Space => (σ, x₀) - t) volume volume :=
    (Measure.measurePreserving_sub_left volume (σ, x₀)).quasiMeasurePreserving
  have hd' : ∀ᵐ t : ℝ × Space, HasFDerivAt (F (σ - t.1)) (F' (σ - t.1) (x₀ - t.2)) (x₀ - t.2) := by
    have h := hqmp.ae hd
    simpa using h
  refine (hasFDerivAt_integral_of_dominated_loc_of_lip
    (F := fun x t => (bump k).normed volume t • F (σ - t.1) (x - t.2))
    (F' := fun t => (bump k).normed volume t • F' (σ - t.1) (x₀ - t.2))
    (bound := fun t => (bump k).normed volume t * L) (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x => (integrable_term k hF σ x).aestronglyMeasurable)
    (integrable_term k hF σ x₀) (integrable_term k hF' σ x₀).aestronglyMeasurable ?_ ?_ ?_).2
  · refine Filter.Eventually.of_forall fun t => ?_
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun a b => ?_)
    have hn : 0 ≤ (bump k).normed volume t := (bump k).nonneg_normed t
    rw [dist_smul₀, Real.coe_nnabs, abs_of_nonneg (mul_nonneg hn (NNReal.coe_nonneg L)), Real.norm_of_nonneg hn, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hn
    have h := (hincr (σ - t.1)).dist_le_mul (a - t.2) (b - t.2)
    rwa [dist_sub_right] at h
  · exact (bump k).integrable_normed.mul_const _
  · filter_upwards [hd'] with t ht
    have h1 : HasFDerivAt (fun x : Space => x - t.2) (ContinuousLinearMap.id ℝ Space) x₀ :=
      (hasFDerivAt_id x₀).sub_const t.2
    have h3 := ht.comp x₀ h1
    rw [ContinuousLinearMap.comp_id] at h3
    exact h3.const_smul ((bump k).normed volume t)

theorem norm_smear_le (k : ℕ) {F : ℝ → Space → E} {D : ℝ} {n : ℕ} (hn : n ≤ 3) (hD : 0 ≤ D)
    (hb : ∀ s y, ‖F s y‖ ≤ D / (1 + ‖y‖) ^ n) (σ : ℝ) (y : Space) :
    ‖smear k F (σ, y)‖ ≤ 8 * D / (1 + ‖y‖) ^ n := by
  rw [smear_eq]
  have hC : ∀ t : ℝ × Space, ‖(bump k).normed volume t • F (σ - t.1) (y - t.2)‖ ≤
      (bump k).normed volume t * (8 * D / (1 + ‖y‖) ^ n) := by
    intro t
    have hn0 : 0 ≤ (bump k).normed volume t := (bump k).nonneg_normed t
    rw [norm_smul, Real.norm_of_nonneg hn0]
    rcases eq_or_lt_of_le hn0 with h0 | hpos
    · rw [← h0]
      simp
    refine mul_le_mul_of_nonneg_left ?_ hn0
    have hts : t ∈ Function.support ((bump k).normed volume) := hpos.ne'
    rw [(bump k).support_normed_eq, Metric.mem_ball, dist_zero_right] at hts
    have ht : ‖t.2‖ ≤ 1 / 2 := (norm_snd_le t).trans (hts.le.trans (bump_rOut_le k))
    refine (hb _ _).trans ?_
    have hy : 1 + ‖y‖ ≤ 2 * (1 + ‖y - t.2‖) := by
      linarith [norm_sub_norm_le y t.2, norm_nonneg (y - t.2)]
    have e1 : (1 + ‖y‖) ^ n ≤ (2 * (1 + ‖y - t.2‖)) ^ n := pow_le_pow_left₀ (by positivity) hy n
    have e2 : (2 : ℝ) ^ n ≤ 8 := by
      calc (2 : ℝ) ^ n ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hn
        _ = 8 := by norm_num
    rw [mul_pow] at e1
    have ha : 0 < (1 + ‖y - t.2‖) ^ n := by positivity
    rw [div_le_div_iff₀ ha (by positivity)]
    calc D * (1 + ‖y‖) ^ n ≤ D * (2 ^ n * (1 + ‖y - t.2‖) ^ n) := mul_le_mul_of_nonneg_left e1 hD
      _ ≤ D * (8 * (1 + ‖y - t.2‖) ^ n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 ha.le) hD
      _ = 8 * D * (1 + ‖y - t.2‖) ^ n := by ring
  calc ‖∫ t : ℝ × Space, (bump k).normed volume t • F (σ - t.1) (y - t.2)‖
      ≤ ∫ t : ℝ × Space, (bump k).normed volume t * (8 * D / (1 + ‖y‖) ^ n) :=
        norm_integral_le_of_norm_le ((bump k).integrable_normed.mul_const _)
          (Filter.Eventually.of_forall hC)
    _ = 8 * D / (1 + ‖y‖) ^ n := by rw [integral_mul_const, (bump k).integral_normed, one_mul]

theorem locallyIntegrable_of_bound {F : ℝ → Space → E} {B : ℝ}
    (hm : AEStronglyMeasurable (fun u : ℝ × Space => F u.1 u.2) volume) (hb : ∀ s y, ‖F s y‖ ≤ B) :
    LocallyIntegrable (fun u : ℝ × Space => F u.1 u.2) volume := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  exact Measure.integrableOn_of_bounded (M := B) measure_ball_lt_top.ne hm
    (Filter.Eventually.of_forall fun u => hb u.1 u.2)

variable {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}

theorem smoothApprox_of (hW : IsWeakSecondDerivState W HW D)
    (hc1 : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2))
    (hae : ∀ᵐ z : ℝ × Space, HasFDerivAt (fderiv ℝ (W z.1)) (HW z.1 z.2) z.2) :
    ∃ D' : ℝ, ∃ V : ℕ → ℝ → Space → Space,
      (∀ k, ContDiff ℝ 2 (fun z : ℝ × Space => V k z.1 z.2)) ∧ (∀ k, IsTimePeriodic (V k)) ∧
      (∀ k σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (V k σ) y‖ ≤ D' / (1 + ‖y‖) ^ (j + 1)) ∧
      (∀ σ y, Filter.Tendsto (fun k => V k σ y) Filter.atTop (nhds (W σ y))) ∧
      (∀ σ y, Filter.Tendsto (fun k => fderiv ℝ (V k σ) y) Filter.atTop (nhds (fderiv ℝ (W σ) y))) ∧
      (∀ᵐ z : ℝ × Space, Filter.Tendsto (fun k => fderiv ℝ (fun x => fderiv ℝ (V k z.1) x) z.2)
        Filter.atTop (nhds (HW z.1 z.2))) := by
  have hD : 0 ≤ D := WeakAeDiff.decay_nonneg hW
  have hc0 : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have hdiff : ∀ σ, Differentiable ℝ (W σ) := fun σ =>
    (hW.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero
  have hone : ∀ (y : Space) (n : ℕ), D / (1 + ‖y‖) ^ n ≤ D := fun y n =>
    div_le_self hD (one_le_pow₀ (by linarith [norm_nonneg y]))
  have hincr0 : ∀ σ, LipschitzWith (Real.toNNReal D) (W σ) := fun σ =>
    lipschitzWith_of_nnnorm_fderiv_le (hdiff σ) fun y => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hD]
      exact (hW.decay σ y).2.1.trans (hone y 2)
  have hL0 : LocallyIntegrable (fun u : ℝ × Space => W u.1 u.2) volume := hc0.locallyIntegrable
  have hL1 : LocallyIntegrable (fun u : ℝ × Space => fderiv ℝ (W u.1) u.2) volume := hc1.locallyIntegrable
  have hL2 : LocallyIntegrable (fun u : ℝ × Space => HW u.1 u.2) volume :=
    locallyIntegrable_of_bound hW.secondDeriv_measurable (B := D) fun s y =>
      (hW.decay s y).2.2.trans (hone y 3)
  have hd1 : ∀ k σ x, HasFDerivAt (fun y => smear k W (σ, y))
      (smear k (fun s y => fderiv ℝ (W s) y) (σ, x)) x := fun k σ x =>
    hasFDerivAt_smear k hL0 hL1 hincr0
      (Filter.Eventually.of_forall fun u => (hdiff u.1 u.2).hasFDerivAt) σ x
  have hd2 : ∀ k σ x, HasFDerivAt (fun y => smear k (fun s y => fderiv ℝ (W s) y) (σ, y))
      (smear k HW (σ, x)) x := fun k σ x =>
    hasFDerivAt_smear k hL1 hL2 (WeakAeDiff.fderiv_increment hW) hae σ x
  have hf1 : ∀ k σ, fderiv ℝ (fun y => smear k W (σ, y)) =
      fun x => smear k (fun s y => fderiv ℝ (W s) y) (σ, x) :=
    fun k σ => funext fun x => (hd1 k σ x).fderiv
  have hf2 : ∀ k σ y, fderiv ℝ (fun x => fderiv ℝ (fun y => smear k W (σ, y)) x) y =
      smear k HW (σ, y) := by
    intro k σ y
    rw [hf1 k σ]
    exact (hd2 k σ y).fderiv
  refine ⟨8 * D, fun k σ y => smear k W (σ, y), fun k => ?_, fun k σ y => ?_, fun k σ y j hj => ?_,
    fun σ y => ?_, fun σ y => ?_, ?_⟩
  · have h : ContDiff ℝ 2 (smear k W) :=
      ((bump k).hasCompactSupport_normed).contDiff_convolution_left _ (bump k).contDiff_normed hL0
    simpa using h
  · show smear k W (σ + 1, y) = smear k W (σ, y)
    rw [smear_eq, smear_eq]
    congr 1
    ext t
    rw [show σ + 1 - t.1 = σ - t.1 + 1 by ring, hW.periodic]
  · interval_cases j
    · rw [norm_iteratedFDeriv_zero]
      simpa using norm_smear_le k (n := 1) (by norm_num) hD (fun s y => by simpa using (hW.decay s y).1) σ y
    · rw [norm_iteratedFDeriv_one, hf1 k σ]
      exact norm_smear_le k (n := 2) (by norm_num) hD (fun s y => (hW.decay s y).2.1) σ y
    · rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
      show ‖fderiv ℝ (fun x => fderiv ℝ (fun y => smear k W (σ, y)) x) y‖ ≤ _
      rw [hf2 k σ y]
      exact norm_smear_le k (n := 3) (by norm_num) hD (fun s y => (hW.decay s y).2.2) σ y
  · exact ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) (φ := bump) bump_rOut_tendsto hc0 (σ, y)
  · show Filter.Tendsto (fun k => fderiv ℝ (fun y => smear k W (σ, y)) y) Filter.atTop _
    simp only [hf1]
    exact ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) (φ := bump) bump_rOut_tendsto hc1 (σ, y)
  · filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) (φ := bump)
      bump_rOut_tendsto (K := 2) (Filter.Eventually.of_forall bump_ratio) hL2] with z hz
    show Filter.Tendsto (fun k => fderiv ℝ (fun x => fderiv ℝ (fun y => smear k W (z.1, y)) x) z.2)
      Filter.atTop _
    simp only [hf2, Prod.mk.eta]
    exact hz

end Internal.WeakMollify

end CoerciveWeak

end Breakdown
