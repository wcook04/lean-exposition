import Breakdown.Frac.StSpaceBlowup
import Breakdown.FreqTr.Realization

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown

private lemma ballPreimageRot (R : Space ≃ₗᵢ[ℝ] Space) (ρ : ℝ) :
    (R.symm : Space → Space) ⁻¹' Metric.ball 0 ρ = Metric.ball 0 ρ := by
  ext y
  simp [Metric.mem_ball, dist_zero_right]

private lemma ballNormRot (R : Space ≃ₗᵢ[ℝ] Space) {f : Space → Space}
    (hf : AEStronglyMeasurable f volume) (ρ : ℝ) :
    eLpNorm (pushForward R f) 6 (volume.restrict (Metric.ball (0 : Space) ρ)) =
      eLpNorm f 6 (volume.restrict (Metric.ball (0 : Space) ρ)) := by
  have e1 : eLpNorm (pushForward R f) 6 (volume.restrict (Metric.ball (0 : Space) ρ)) =
      eLpNorm (f ∘ (R.symm : Space → Space)) 6
        (volume.restrict (Metric.ball (0 : Space) ρ)) := by
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun y => ?_)
    simp [pushForward]
  have hmp : MeasurePreserving (R.symm : Space → Space)
      (volume.restrict (Metric.ball (0 : Space) ρ))
      (volume.restrict (Metric.ball (0 : Space) ρ)) := by
    have := (R.symm.measurePreserving).restrict_preimage
      (s := Metric.ball (0 : Space) ρ) Metric.isOpen_ball.measurableSet
    rwa [ballPreimageRot] at this
  rw [e1, eLpNorm_comp_measurePreserving hf.restrict hmp]

private lemma ballNormVelRot (R : Space ≃ₗᵢ[ℝ] Space) (x : Freq.X) (ρ : ℝ) :
    eLpNorm (Freq.velocity (Freq.rotX R x) : Space → Space) 6
        (volume.restrict (Metric.ball (0 : Space) ρ)) =
      eLpNorm (Freq.velocity x : Space → Space) 6
        (volume.restrict (Metric.ball (0 : Space) ρ)) := by
  rw [eLpNorm_congr_ae (ae_restrict_of_ae (Freq.velocityCov_holds.1 R x))]
  exact ballNormRot R (Lp.aestronglyMeasurable _) ρ

private lemma someBallNormNeZero (f : Space → Space)
    (hf : AEStronglyMeasurable f volume) (hne : ¬ f =ᵐ[volume] 0) :
    ∃ n : ℕ, eLpNorm f 6 (volume.restrict (Metric.ball (0 : Space) n)) ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  have e2 : ∀ n : ℕ, ∀ᵐ y ∂(volume.restrict (Metric.ball (0 : Space) n)),
      f y = (0 : Space → Space) y := fun n =>
    (eLpNorm_eq_zero_iff hf.restrict (by norm_num)).1 (h n)
  have e3 := (ae_restrict_iUnion_iff (fun n : ℕ => Metric.ball (0 : Space) n) _).2 e2
  rwa [Metric.iUnion_ball_nat, Measure.restrict_univ] at e3

private lemma scaleFieldAeCongr (α : ℝ) {f g : Space → Space} (hfg : f =ᵐ[volume] g) {μ : ℝ}
    (hμ : 0 < μ) : scaleField α μ f =ᵐ[volume] scaleField α μ g := by
  have hq : Measure.QuasiMeasurePreserving (fun y : Space => μ ^ (1 / (2 * α)) • y) volume volume :=
    Measure.quasiMeasurePreserving_smul (μ := volume) (Real.rpow_pos_of_pos hμ _).ne'
  have := hq.ae_eq_comp hfg
  filter_upwards [this] with y hy
  simp only [Function.comp_apply] at hy
  simp only [scaleField, hy]

private lemma scaleFieldNormLe {α : ℝ} (hα : 0 < α) {v : Space → Space} {μ ρ M : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hM : ∀ z ∈ Metric.closedBall (0 : Space) ρ, ‖v z‖ ≤ M) :
    ∀ y ∈ Metric.ball (0 : Space) ρ, ‖scaleField α μ v y‖ ≤ μ ^ (1 - 1 / (2 * α)) * M := by
  intro y hy
  have hg : 0 ≤ 1 / (2 * α) := by positivity
  have hs0 : 0 ≤ μ ^ (1 / (2 * α)) := Real.rpow_nonneg hμ0.le _
  have hs1 : μ ^ (1 / (2 * α)) ≤ 1 := Real.rpow_le_one hμ0.le hμ1 hg
  have hmem : μ ^ (1 / (2 * α)) • y ∈ Metric.closedBall (0 : Space) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hs0]
    rw [Metric.mem_ball, dist_zero_right] at hy
    nlinarith [norm_nonneg y]
  have ht0 : 0 ≤ μ ^ (1 - 1 / (2 * α)) := Real.rpow_nonneg hμ0.le _
  rw [scaleField, norm_smul, Real.norm_of_nonneg ht0]
  exact mul_le_mul_of_nonneg_left (hM _ hmem) ht0

private lemma ballNormStep {α K : ℝ} (hα0 : 0 < α) (h1 : Freq.FracVelocityDilate α)
    (hK0 : 0 ≤ K) (hK : ∀ y : Freq.X, ‖Freq.velocity y‖ ≤ K * ‖y‖)
    {a x : Freq.X} {f : Space → Space} (hf : (Freq.velocity x : Space → Space) =ᵐ[volume] f)
    {μ ρ M E : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hM : ∀ z ∈ Metric.closedBall (0 : Space) ρ, ‖f z‖ ≤ M)
    (hr : ‖Freq.fracDilX α μ x - a‖ ≤ E) :
    eLpNorm (Freq.velocity a : Space → Space) 6 (volume.restrict (Metric.ball (0 : Space) ρ)) ≤
      ENNReal.ofReal (K * E) +
        (volume.restrict (Metric.ball (0 : Space) ρ)) univ ^ ((6 : ℝ≥0∞).toReal)⁻¹ *
          ENNReal.ofReal (μ ^ (1 - 1 / (2 * α)) * M) := by
  have hsplit : eLpNorm (Freq.velocity a : Space → Space) 6
        (volume.restrict (Metric.ball (0 : Space) ρ)) ≤
      eLpNorm ((Freq.velocity a : Space → Space) - (Freq.velocity (Freq.fracDilX α μ x) : Space → Space)) 6
          (volume.restrict (Metric.ball (0 : Space) ρ)) +
        eLpNorm (Freq.velocity (Freq.fracDilX α μ x) : Space → Space) 6
          (volume.restrict (Metric.ball (0 : Space) ρ)) := by
    calc eLpNorm (Freq.velocity a : Space → Space) 6 (volume.restrict (Metric.ball (0 : Space) ρ))
        = eLpNorm (((Freq.velocity a : Space → Space) -
            (Freq.velocity (Freq.fracDilX α μ x) : Space → Space)) +
            (Freq.velocity (Freq.fracDilX α μ x) : Space → Space)) 6
            (volume.restrict (Metric.ball (0 : Space) ρ)) := by
          rw [sub_add_cancel]
      _ ≤ _ := eLpNorm_add_le
          ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)).restrict
          (Lp.aestronglyMeasurable _).restrict (by norm_num)
  have hdiff : eLpNorm ((Freq.velocity a : Space → Space) -
        (Freq.velocity (Freq.fracDilX α μ x) : Space → Space)) 6
        (volume.restrict (Metric.ball (0 : Space) ρ)) ≤
      ENNReal.ofReal (K * E) := by
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    rw [← Lp.edist_def, edist_dist, dist_eq_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← map_sub]
    refine (hK _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK0
    rw [norm_sub_rev]
    exact hr
  have hbd : eLpNorm (Freq.velocity (Freq.fracDilX α μ x) : Space → Space) 6
        (volume.restrict (Metric.ball (0 : Space) ρ)) ≤
      (volume.restrict (Metric.ball (0 : Space) ρ)) univ ^ ((6 : ℝ≥0∞).toReal)⁻¹ *
        ENNReal.ofReal (μ ^ (1 - 1 / (2 * α)) * M) := by
    have hae : (Freq.velocity (Freq.fracDilX α μ x) : Space → Space) =ᵐ[volume]
        scaleField α μ f := (h1 μ hμ0 x).trans (scaleFieldAeCongr α hf hμ0)
    rw [eLpNorm_congr_ae (ae_restrict_of_ae hae)]
    refine eLpNorm_le_of_ae_bound ?_
    refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet ?_
    exact scaleFieldNormLe hα0 hμ0 hμ1 hM
  exact hsplit.trans (add_le_add hdiff hbd)

private lemma periodicBallNorm {R : Space ≃ₗᵢ[ℝ] Space} {w : ℝ → Freq.X} {P : ℝ}
    (hper : ∀ s, w (s + P) = Freq.rotX R (w s)) (s₀ ρ : ℝ) (n : ℕ) :
    eLpNorm (Freq.velocity (w (s₀ + n * P)) : Space → Space) 6
        (volume.restrict (Metric.ball (0 : Space) ρ)) =
      eLpNorm (Freq.velocity (w s₀) : Space → Space) 6
        (volume.restrict (Metric.ball (0 : Space) ρ)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : s₀ + ((k + 1 : ℕ) : ℝ) * P = (s₀ + k * P) + P := by push_cast; ring
    rw [hk, hper, ballNormVelRot, ih]

private lemma limitForcesZero {K C κ γ M s₀ P : ℝ} {c N : ℝ≥0∞} (hκ : 0 < κ) (hγ : 0 < γ)
    (hP : 0 < P) (hcne : c ≠ ⊤)
    (hbound : ∀ n : ℕ, 0 ≤ s₀ + n * P → N ≤ ENNReal.ofReal (K * (C * Real.exp (-(s₀ + n * P)) ^ κ)) +
      c * ENNReal.ofReal (Real.exp (-(s₀ + n * P)) ^ γ * M)) : N = 0 := by
  have hsn : Tendsto (fun n : ℕ => s₀ + n * P) atTop atTop :=
    tendsto_atTop_add_const_left _ s₀
      (tendsto_natCast_atTop_atTop.atTop_mul_const hP)
  have hμn : Tendsto (fun n : ℕ => Real.exp (-(s₀ + n * P))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hsn
  have l1 : Tendsto (fun n : ℕ => K * (C * Real.exp (-(s₀ + n * P)) ^ κ)) atTop (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto.comp hμn
    rw [Real.zero_rpow hκ.ne'] at this
    simpa using (this.const_mul C).const_mul K
  have l2 : Tendsto (fun n : ℕ => Real.exp (-(s₀ + n * P)) ^ γ * M) atTop (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto.comp hμn
    rw [Real.zero_rpow hγ.ne'] at this
    simpa using this.mul_const M
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (K * (C * Real.exp (-(s₀ + n * P)) ^ κ)) +
      c * ENNReal.ofReal (Real.exp (-(s₀ + n * P)) ^ γ * M)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_ofReal l1).add
      (ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal l2) (Or.inr hcne))
    simpa using this
  have hev : ∀ᶠ n : ℕ in atTop, N ≤ ENNReal.ofReal (K * (C * Real.exp (-(s₀ + n * P)) ^ κ)) +
      c * ENNReal.ofReal (Real.exp (-(s₀ + n * P)) ^ γ * M) := by
    filter_upwards [hsn.eventually_ge_atTop 0] with n hn
    exact hbound n hn
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto hlim hev)

theorem fracOrbitRateFalse (α : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (h1 : Freq.FracVelocityDilate α) :
    FracOrbitRateFalseStatement α := by
  intro F hD R w P hw u C κ hκ hrate v hv hagree
  have hα0 : 0 < α := by linarith
  have hexp : 0 < 1 - 1 / (2 * α) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Freq.X, ‖Freq.velocity y‖ ≤ K * ‖y‖ :=
    ⟨_, norm_nonneg _, Freq.velocity.le_opNorm⟩
  obtain ⟨s₀, hs₀⟩ := hw.nonzero
  have hne : ¬ (Freq.velocity (w s₀) : Space → Space) =ᵐ[volume] 0 := fun h =>
    hs₀ (Freq.velocityInjective_holds _ h)
  obtain ⟨n₀, hn₀⟩ := someBallNormNeZero _ (Lp.aestronglyMeasurable _) hne
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) (n₀ : ℝ))).exists_bound_of_continuousOn
    (hv.mono (prod_mono subset_rfl (subset_univ _)))
  have hcne : (volume.restrict (Metric.ball (0 : Space) (n₀ : ℝ))) univ ^ ((6 : ℝ≥0∞).toReal)⁻¹ ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top.ne
  have key : ∀ s : ℝ, 0 ≤ s → eLpNorm (Freq.velocity (w s) : Space → Space) 6
      (volume.restrict (Metric.ball (0 : Space) (n₀ : ℝ))) ≤
      ENNReal.ofReal (K * (C * Real.exp (-s) ^ κ)) +
        (volume.restrict (Metric.ball (0 : Space) (n₀ : ℝ))) univ ^ ((6 : ℝ≥0∞).toReal)⁻¹ *
          ENNReal.ofReal (Real.exp (-s) ^ (1 - 1 / (2 * α)) * M) := by
    intro s hs
    have hμ0 : 0 < Real.exp (-s) := Real.exp_pos _
    have hμ1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have ht : 1 - Real.exp (-s) ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have h1t : 1 - (1 - Real.exp (-s)) = Real.exp (-s) := by ring
    have hr := hrate _ ht
    rw [h1t, Real.log_exp, neg_neg, hD] at hr
    exact ballNormStep hα0 h1 hK0 hK (hagree _ ht) hμ0 hμ1
      (fun z hz => hM (1 - Real.exp (-s), z) ⟨⟨ht.1, ht.2.le⟩, hz⟩) hr
  exact hn₀ (limitForcesZero hκ hexp hw.pos hcne
    (fun n hn => by rw [← periodicBallNorm hw.periodic s₀ _ n]; exact key _ hn))

end Breakdown
