import Breakdown.Uniqueness.Basic

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown

private lemma preimage_symm_ball_eq (R : Space ≃ₗᵢ[ℝ] Space) (ρ : ℝ) :
    (R.symm : Space → Space) ⁻¹' Metric.ball 0 ρ = Metric.ball 0 ρ := by
  ext y
  simp [Metric.mem_ball, dist_zero_right]

private lemma eLpNorm_ball_pushForward (R : Space ≃ₗᵢ[ℝ] Space) {f : Space → Space}
    (hf : AEStronglyMeasurable f volume) (ρ : ℝ) :
    eLpNorm (pushForward R f) 6 (volume.restrict (Metric.ball (0 : Space) ρ)) =
      eLpNorm f 6 (volume.restrict (Metric.ball (0 : Space) ρ)) := by
  have h1 : eLpNorm (pushForward R f) 6 (volume.restrict (Metric.ball (0 : Space) ρ)) =
      eLpNorm (f ∘ (R.symm : Space → Space)) 6
        (volume.restrict (Metric.ball (0 : Space) ρ)) := by
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun y => ?_)
    simp [pushForward]
  have hmp : MeasurePreserving (R.symm : Space → Space)
      (volume.restrict (Metric.ball (0 : Space) ρ))
      (volume.restrict (Metric.ball (0 : Space) ρ)) := by
    have := (R.symm.measurePreserving).restrict_preimage
      (s := Metric.ball (0 : Space) ρ) Metric.isOpen_ball.measurableSet
    rwa [preimage_symm_ball_eq] at this
  rw [h1, eLpNorm_comp_measurePreserving hf.restrict hmp]

private lemma eLpNorm_ball_rot {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] {Rlz : Realization X} {vel : X →L[ℝ] Lp (α := Space) Space 6}
    (hF : FieldReading Rlz vel) (R : Space ≃ₗᵢ[ℝ] Space) (x : X) (ρ : ℝ) :
    eLpNorm (vel (Rlz.rot R x) : Space → Space) 6 (volume.restrict (Metric.ball (0 : Space) ρ)) =
      eLpNorm (vel x : Space → Space) 6 (volume.restrict (Metric.ball (0 : Space) ρ)) := by
  rw [eLpNorm_congr_ae (ae_restrict_of_ae (hF.rot R x))]
  exact eLpNorm_ball_pushForward R (Lp.aestronglyMeasurable _) ρ

private lemma exists_ball_eLpNorm_ne_zero (f : Space → Space)
    (hf : AEStronglyMeasurable f volume) (hne : ¬ f =ᵐ[volume] 0) :
    ∃ n : ℕ, eLpNorm f 6 (volume.restrict (Metric.ball (0 : Space) n)) ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  have h2 : ∀ n : ℕ, ∀ᵐ y ∂(volume.restrict (Metric.ball (0 : Space) n)),
      f y = (0 : Space → Space) y := fun n =>
    (eLpNorm_eq_zero_iff hf.restrict (by norm_num)).1 (h n)
  have h3 := (ae_restrict_iUnion_iff (fun n : ℕ => Metric.ball (0 : Space) n) _).2 h2
  rwa [Metric.iUnion_ball_nat, Measure.restrict_univ] at h3

private lemma dilateField_ae_congr {f g : Space → Space} (hfg : f =ᵐ[volume] g) {μ : ℝ}
    (hμ : 0 < μ) : dilateField μ f =ᵐ[volume] dilateField μ g := by
  have hq : Measure.QuasiMeasurePreserving (fun y : Space => Real.sqrt μ • y) volume volume :=
    Measure.quasiMeasurePreserving_smul (μ := volume) (Real.sqrt_pos.2 hμ).ne'
  have := hq.ae_eq_comp hfg
  filter_upwards [this] with y hy
  simp only [Function.comp_apply] at hy
  simp only [dilateField, hy]

private lemma norm_dilateField_le {v : Space → Space} {μ ρ M : ℝ} (hμ1 : μ ≤ 1)
    (hM : ∀ z ∈ Metric.closedBall (0 : Space) ρ, ‖v z‖ ≤ M) :
    ∀ y ∈ Metric.ball (0 : Space) ρ, ‖dilateField μ v y‖ ≤ Real.sqrt μ * M := by
  intro y hy
  have hs0 : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg μ
  have hs1 : Real.sqrt μ ≤ 1 := Real.sqrt_le_one.mpr hμ1
  have hmem : Real.sqrt μ • y ∈ Metric.closedBall (0 : Space) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hs0]
    rw [Metric.mem_ball, dist_zero_right] at hy
    nlinarith [norm_nonneg y]
  rw [dilateField, norm_smul, Real.norm_of_nonneg hs0]
  exact mul_le_mul_of_nonneg_left (hM _ hmem) hs0

theorem false_of_orbit_rate {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] {Rlz : Realization X} {vel : X →L[ℝ] Lp (α := Space) Space 6}
    (hF : FieldReading Rlz vel) {R : Space ≃ₗᵢ[ℝ] Space} {w : ℝ → X} {P : ℝ}
    (hw : Rlz.F.IsOrbit (Rlz.rot R) w P) {u : ℝ → X} {C κ : ℝ} (hκ : 0 < κ)
    (hrate : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖Rlz.F.D (1 - t) (u t) - w (-Real.log (1 - t))‖ ≤ C * (1 - t) ^ κ)
    {v : ℝ → Space → Space}
    (hv : ContinuousOn (fun z : ℝ × Space => v z.1 z.2) (Icc 0 1 ×ˢ univ))
    (hagree : ∀ t ∈ Ico (0 : ℝ) 1, (vel (u t) : Space → Space) =ᵐ[volume] v t) : False := by
  obtain ⟨s₀, hs₀⟩ := hw.nonzero
  have hne : ¬ (vel (w s₀) : Space → Space) =ᵐ[volume] 0 := fun h => hs₀ (hF.injective _ h)
  obtain ⟨n₀, hn₀⟩ := exists_ball_eLpNorm_ne_zero _ (Lp.aestronglyMeasurable _) hne
  set ρ : ℝ := (n₀ : ℝ) with hρ
  set ν : Measure Space := volume.restrict (Metric.ball (0 : Space) ρ) with hν
  set N := eLpNorm (vel (w s₀) : Space → Space) 6 ν with hN
  have hiter : ∀ n : ℕ, eLpNorm (vel (w (s₀ + n * P)) : Space → Space) 6 ν = N := by
    intro n
    induction n with
    | zero => simp [hN]
    | succ k ih =>
      have hk : s₀ + ((k + 1 : ℕ) : ℝ) * P = (s₀ + k * P) + P := by push_cast; ring
      rw [hk, hw.periodic, hν, eLpNorm_ball_rot hF, ← hν, ih]
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) ρ)).exists_bound_of_continuousOn
    (hv.mono (prod_mono subset_rfl (subset_univ _)))
  set c : ℝ≥0∞ := ν univ ^ ((6 : ℝ≥0∞).toReal)⁻¹ with hc
  have hcne : c ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
    rw [hν, Measure.restrict_apply_univ]
    exact measure_ball_lt_top.ne
  have key : ∀ s : ℝ, 0 ≤ s → eLpNorm (vel (w s) : Space → Space) 6 ν ≤
      ENNReal.ofReal (‖vel‖ * (C * Real.exp (-s) ^ κ)) +
        c * ENNReal.ofReal (Real.sqrt (Real.exp (-s)) * M) := by
    intro s hs
    set μ := Real.exp (-s) with hμdef
    have hμ0 : 0 < μ := Real.exp_pos _
    have hμ1 : μ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    set t := 1 - μ with htdef
    have ht : t ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have h1t : 1 - t = μ := by rw [htdef]; ring
    have hlog : -Real.log (1 - t) = s := by rw [h1t, hμdef, Real.log_exp, neg_neg]
    have hr := hrate t ht
    rw [hlog, h1t] at hr
    set a := vel (w s) with ha
    set b := vel (Rlz.F.D μ (u t)) with hb
    have hsplit : eLpNorm (a : Space → Space) 6 ν ≤
        eLpNorm ((a : Space → Space) - (b : Space → Space)) 6 ν + eLpNorm (b : Space → Space) 6 ν := by
      calc eLpNorm (a : Space → Space) 6 ν
          = eLpNorm (((a : Space → Space) - (b : Space → Space)) + (b : Space → Space)) 6 ν := by
            rw [sub_add_cancel]
        _ ≤ _ := eLpNorm_add_le
            ((Lp.aestronglyMeasurable a).sub (Lp.aestronglyMeasurable b)).restrict
            (Lp.aestronglyMeasurable b).restrict (by norm_num)
    have hdiff : eLpNorm ((a : Space → Space) - (b : Space → Space)) 6 ν ≤
        ENNReal.ofReal (‖vel‖ * (C * μ ^ κ)) := by
      refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      rw [← Lp.edist_def, edist_dist, dist_eq_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [ha, hb, ← map_sub]
      refine (vel.le_opNorm _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_sub_rev]
      exact hr
    have hbd : eLpNorm (b : Space → Space) 6 ν ≤ c * ENNReal.ofReal (Real.sqrt μ * M) := by
      have hae : (b : Space → Space) =ᵐ[volume] dilateField μ (v t) :=
        (hF.dil μ hμ0 (u t)).trans (dilateField_ae_congr (hagree t ht) hμ0)
      rw [eLpNorm_congr_ae (ae_restrict_of_ae hae)]
      refine eLpNorm_le_of_ae_bound ?_
      refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet ?_
      refine norm_dilateField_le hμ1 ?_
      intro z hz
      exact hM (t, z) ⟨⟨ht.1, ht.2.le⟩, hz⟩
    calc eLpNorm (a : Space → Space) 6 ν ≤ _ := hsplit
      _ ≤ _ := add_le_add hdiff hbd
  have hsn : Tendsto (fun n : ℕ => s₀ + n * P) atTop atTop :=
    tendsto_atTop_add_const_left _ s₀
      (tendsto_natCast_atTop_atTop.atTop_mul_const hw.pos)
  have hμn : Tendsto (fun n : ℕ => Real.exp (-(s₀ + n * P))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hsn
  have h1 : Tendsto (fun n : ℕ => ‖vel‖ * (C * Real.exp (-(s₀ + n * P)) ^ κ)) atTop (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto.comp hμn
    rw [Real.zero_rpow hκ.ne'] at this
    simpa using (this.const_mul C).const_mul ‖vel‖
  have h2 : Tendsto (fun n : ℕ => Real.sqrt (Real.exp (-(s₀ + n * P))) * M) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hμn).mul_const M
    simpa using this
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (‖vel‖ * (C * Real.exp (-(s₀ + n * P)) ^ κ)) +
      c * ENNReal.ofReal (Real.sqrt (Real.exp (-(s₀ + n * P))) * M)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_ofReal h1).add
      (ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal h2) (Or.inr hcne))
    simpa using this
  have hev : ∀ᶠ n : ℕ in atTop, N ≤ ENNReal.ofReal (‖vel‖ * (C * Real.exp (-(s₀ + n * P)) ^ κ)) +
      c * ENNReal.ofReal (Real.sqrt (Real.exp (-(s₀ + n * P))) * M) := by
    filter_upwards [hsn.eventually_ge_atTop 0] with n hn
    rw [← hiter n]
    exact key _ hn
  have hN0 : N ≤ 0 := ge_of_tendsto hlim hev
  exact hn₀ (nonpos_iff_eq_zero.mp hN0)

end Breakdown
