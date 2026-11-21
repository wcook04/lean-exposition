import Breakdown.Cert.Nodes

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.CoerciveBordered

theorem lintegral_Ioc_periodic (Φ : ℝ → ℝ≥0∞) (hper : Function.Periodic Φ 1) (c : ℝ) :
    ∫⁻ σ in Set.Ioc c (c + 1), Φ σ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, Φ σ := by
  have e1 := AddCircle.lintegral_preimage (T := (1 : ℝ)) c hper.lift
  have e0 := AddCircle.lintegral_preimage (T := (1 : ℝ)) 0 hper.lift
  simp only [Function.Periodic.lift_coe, zero_add] at e1 e0
  rw [e1, ← e0, Measure.restrict_congr_set Ioc_ae_eq_Icc]

theorem locallyIntegrable_of_periodic_sq (a : ℝ → Space → ℝ)
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => a z.1 z.2) volume) (hp : IsTimePeriodic a)
    (hf : periodLIntegral (fun σ y => a σ y ^ 2) < ⊤) :
    LocallyIntegrable (fun z : ℝ × Space => a z.1 z.2) volume := by
  intro x
  refine ⟨Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 1,
    prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) (Metric.ball_mem_nhds _ one_pos), ?_⟩
  have hsfin : volume (Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 (1 : ℝ)) < ⊤ :=
    ((Metric.isBounded_Ioo _ _).prod Metric.isBounded_ball).measure_lt_top
  have : IsFiniteMeasure (volume.restrict
      (Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 (1 : ℝ))) :=
    ⟨by simpa using hsfin⟩
  have hsq : Integrable (fun z : ℝ × Space => a z.1 z.2 ^ 2)
      (volume.restrict (Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 (1 : ℝ))) := by
    refine ⟨(hm.pow 2).restrict, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg _)]
    have hper : Function.Periodic (fun σ => ∫⁻ y, ENNReal.ofReal (a σ y ^ 2)) 1 :=
      fun σ => by simp only [hp σ]
    calc ∫⁻ z in Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 (1 : ℝ),
          ENNReal.ofReal (a z.1 z.2 ^ 2)
        ≤ ∫⁻ z in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ (Set.univ : Set Space),
          ENNReal.ofReal (a z.1 z.2 ^ 2) :=
          lintegral_mono_set (Set.prod_mono Set.Ioo_subset_Ioc_self (Set.subset_univ _))
      _ = ∫⁻ σ in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1), ∫⁻ y in (Set.univ : Set Space),
          ENNReal.ofReal (a σ y ^ 2) := by
          rw [Measure.volume_eq_prod, setLIntegral_prod (fun z : ℝ × Space => ENNReal.ofReal (a z.1 z.2 ^ 2))
            (hm.pow 2).aemeasurable.ennreal_ofReal.restrict]
      _ = ∫⁻ σ in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1), ∫⁻ y, ENNReal.ofReal (a σ y ^ 2) := by
          simp only [Measure.restrict_univ]
      _ = periodLIntegral (fun σ y => a σ y ^ 2) := lintegral_Ioc_periodic _ hper _
      _ < ⊤ := hf
  refine (hsq.add (integrable_const (1 : ℝ))).mono' hm.restrict (Eventually.of_forall fun z => ?_)
  show ‖a z.1 z.2‖ ≤ a z.1 z.2 ^ 2 + 1
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (a z.1 z.2), abs_nonneg (a z.1 z.2), sq_nonneg (|a z.1 z.2| - 1)]

theorem lintegral_ball_velocity_le (h : Freq.X) (y₀ : Space) :
    ∫⁻ y in Metric.ball y₀ 1, ‖(velocity h : Space → Space) y‖ₑ ≤
      ENNReal.ofReal (‖velocity‖ * ‖h‖) *
        volume (Metric.ball y₀ 1) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) := by
  rw [← eLpNorm_one_eq_lintegral_enorm]
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (Metric.ball y₀ 1))
    (p := 1) (q := 6) (by norm_num) (Lp.aestronglyMeasurable (velocity h)).restrict
  rw [Measure.restrict_apply_univ] at h1
  refine h1.trans ?_
  gcongr
  calc eLpNorm (velocity h : Space → Space) 6 (volume.restrict (Metric.ball y₀ 1))
      ≤ eLpNorm (velocity h : Space → Space) 6 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = ‖velocity h‖ₑ := (Lp.enorm_def _).symm
    _ = ENNReal.ofReal ‖velocity h‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖velocity‖ * ‖h‖) := ENNReal.ofReal_le_ofReal (velocity.le_opNorm h)

theorem ball_bound (x₀ : Space) (q : XBar) (w : Space → Space)
    (hw : w =ᵐ[volume] (velocity (gradPart q) : Space → Space)) :
    ∫⁻ y in Metric.ball x₀ (1 : ℝ), ‖w y‖ₑ ≤
      ENNReal.ofReal (‖velocity‖ * ‖gradPart‖ * ‖q‖) *
        volume (Metric.ball x₀ (1 : ℝ)) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) := by
  calc ∫⁻ y in Metric.ball x₀ (1 : ℝ), ‖w y‖ₑ
      = ∫⁻ y in Metric.ball x₀ (1 : ℝ), ‖(velocity (gradPart q) : Space → Space) y‖ₑ :=
        lintegral_congr_ae (ae_restrict_of_ae (hw.mono fun y hy => congrArg (fun a : Space => ‖a‖ₑ) hy))
    _ ≤ ENNReal.ofReal (‖velocity‖ * ‖gradPart q‖) *
          volume (Metric.ball x₀ (1 : ℝ)) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) :=
        lintegral_ball_velocity_le _ _
    _ ≤ _ := by
        gcongr ?_ * _
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (gradPart.le_opNorm _) (norm_nonneg _)

theorem locallyIntegrable_norm_velocity {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (h : IsReadingOf u v G H) :
    LocallyIntegrable (fun z : ℝ × Space => ‖v z.1 z.2‖) volume := by
  intro x
  refine ⟨Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 1,
    prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) (Metric.ball_mem_nhds _ one_pos), ?_⟩
  refine ⟨h.measurable_velocity.norm.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [enorm_norm]
  have hK : volume (Metric.ball x.2 (1 : ℝ)) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  have hu : ∫⁻ t : TimeCircle, ENNReal.ofReal (‖velocity‖ * ‖gradPart‖ *
      ‖(u : TimeCircle → XBar) t‖) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => by positivity)).1
      (((Lp.memLp u).integrable one_le_two).norm.const_mul (‖velocity‖ * ‖gradPart‖)).2
  have hu' : ∫⁻ σ in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1), ENNReal.ofReal (‖velocity‖ * ‖gradPart‖ *
      ‖(u : TimeCircle → XBar) (σ : TimeCircle)‖) < ⊤ := by
    rw [AddCircle.lintegral_preimage (T := (1 : ℝ)) (x.1 - 1 / 2)
      (fun t => ENNReal.ofReal (‖velocity‖ * ‖gradPart‖ * ‖(u : TimeCircle → XBar) t‖))]
    exact hu
  calc ∫⁻ z in Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 (1 : ℝ), ‖v z.1 z.2‖ₑ
      ≤ ∫⁻ z in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 (1 : ℝ), ‖v z.1 z.2‖ₑ :=
        lintegral_mono_set (Set.prod_mono Set.Ioo_subset_Ioc_self subset_rfl)
    _ = ∫⁻ σ in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1), ∫⁻ y in Metric.ball x.2 (1 : ℝ), ‖v σ y‖ₑ := by
        rw [Measure.volume_eq_prod, setLIntegral_prod (fun z : ℝ × Space => ‖v z.1 z.2‖ₑ)
          h.measurable_velocity.enorm.restrict]
    _ ≤ ∫⁻ σ in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1),
        ENNReal.ofReal (‖velocity‖ * ‖gradPart‖ * ‖(u : TimeCircle → XBar) (σ : TimeCircle)‖) *
          volume (Metric.ball x.2 (1 : ℝ)) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae h.velocity_eq] with σ hσ
        exact ball_bound _ _ _ hσ
    _ = (∫⁻ σ in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1),
        ENNReal.ofReal (‖velocity‖ * ‖gradPart‖ * ‖(u : TimeCircle → XBar) (σ : TimeCircle)‖)) *
          volume (Metric.ball x.2 (1 : ℝ)) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) :=
        lintegral_mul_const' _ _ hK
    _ < ⊤ := ENNReal.mul_lt_top hu' hK.lt_top

theorem integrable_of_le {f a c : ℝ × Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (ha : LocallyIntegrable a volume) (hc : Continuous c) (hcs : HasCompactSupport c)
    (hle : ∀ z, ‖f z‖ ≤ a z * c z) : Integrable f volume := by
  have h : Integrable (fun z => a z • c z) volume :=
    ha.integrable_smul_right_of_hasCompactSupport hc hcs
  exact h.mono' hf (Eventually.of_forall fun z => by simpa [smul_eq_mul] using hle z)

theorem periodLIntegral_mono {a b : ℝ → Space → ℝ} (h : ∀ σ y, a σ y ≤ b σ y) :
    periodLIntegral a ≤ periodLIntegral b :=
  lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (h σ y)

theorem continuous_test {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous

theorem continuous_fderiv_test {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2) := by
  have h1 : ContDiff ℝ (1 : ℕ) (fun z : ℝ × Space => φ z.1 z.2) := contDiff_infty.1 hφ.1 1
  have h2 : ContDiff ℝ (1 : ℕ) (Function.uncurry fun (z : ℝ × Space) (y : Space) => φ z.1 y) :=
    h1.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (h2.fderiv (g := fun z : ℝ × Space => z.2) contDiff_snd (n := 0) (by norm_num)).continuous

theorem hasCompactSupport_fderiv_test {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    HasCompactSupport (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2) := by
  apply hφ.2.1.mono'
  intro z hz
  by_contra hn
  apply hz
  have h0 : ∀ᶠ w in 𝓝 z, (fun z : ℝ × Space => φ z.1 z.2) w = 0 :=
    notMem_tsupport_iff_eventuallyEq.1 hn
  have hc : Continuous (fun y : Space => ((z.1, y) : ℝ × Space)) := by fun_prop
  have h2 : (φ z.1) =ᶠ[𝓝 z.2] fun _ => 0 := hc.continuousAt.tendsto.eventually h0
  show fderiv ℝ (φ z.1) z.2 = 0
  rw [h2.fderiv_eq]
  simp

theorem continuous_fderiv_test_apply {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ)
    (i : Fin 3) : Continuous (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector i)) :=
  (continuous_fderiv_test hφ).clm_apply continuous_const

theorem hasCompactSupport_fderiv_test_apply {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ)
    (i : Fin 3) : HasCompactSupport (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector i)) :=
  (hasCompactSupport_fderiv_test hφ).comp_left (g := fun L : Space →L[ℝ] Space => L (unitVector i))
    (by simp)

theorem norm_apply_le_sum (L : Space →L[ℝ] Space) (x : Space) :
    ‖L x‖ ≤ ‖x‖ * ∑ j : Fin 3, ‖L (unitVector j)‖ := by
  have hx : x = ∑ j : Fin 3, x j • unitVector j := by
    have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
    simpa [EuclideanSpace.basisFun_apply, unitVector] using h.symm
  calc ‖L x‖ = ‖∑ j : Fin 3, x j • L (unitVector j)‖ := by
        conv_lhs => rw [hx]
        simp [map_sum, map_smul]
    _ ≤ ∑ j : Fin 3, ‖x j • L (unitVector j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ‖x‖ * ‖L (unitVector j)‖ := by
        gcongr with j
        rw [norm_smul]
        gcongr
        exact PiLp.norm_apply_le x j
    _ = ‖x‖ * ∑ j : Fin 3, ‖L (unitVector j)‖ := by rw [Finset.mul_sum]

theorem integrable_inner_of_periodic {F : ℝ → Space → Space}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hp : IsTimePeriodic F)
    (hf : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) {ψ : ℝ × Space → Space}
    (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (ψ z)) volume := by
  have ha := locallyIntegrable_of_periodic_sq (fun σ y => ‖F σ y‖) hm.norm
    (fun σ y => by simp only [hp σ y]) hf
  refine integrable_of_le (hm.inner hψ.aestronglyMeasurable) ha hψ.norm hψs.norm fun z => ?_
  rw [Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

theorem column_measurable {G : GradField}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (i : Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (unitVector i)) volume :=
  (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable hm

theorem column_periodic {G : GradField} (hp : IsTimePeriodic G) (i : Fin 3) :
    IsTimePeriodic (fun σ y => G σ y (unitVector i)) := fun σ y => by simp only [hp σ y]

theorem column_finite {G : GradField} (hf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤)
    (i : Fin 3) : periodLIntegral (fun σ y => ‖G σ y (unitVector i)‖ ^ 2) < ⊤ := by
  refine lt_of_le_of_lt (periodLIntegral_mono fun σ y => ?_) hf
  unfold matSq
  exact Finset.single_le_sum (f := fun j : Fin 3 => ‖G σ y (unitVector j)‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)

theorem column_locallyIntegrable {G : GradField}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hp : IsTimePeriodic G)
    (hf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) (i : Fin 3) :
    LocallyIntegrable (fun z : ℝ × Space => ‖G z.1 z.2 (unitVector i)‖) volume :=
  locallyIntegrable_of_periodic_sq (fun σ y => ‖G σ y (unitVector i)‖) (column_measurable hm i).norm
    (fun σ y => by simp only [hp σ y]) (column_finite hf i)

theorem integrable_matNorm {G : GradField}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) (hp : IsTimePeriodic G)
    (hf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤) {φ : ℝ → Space → Space}
    (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) volume := by
  unfold matInner
  refine integrable_finsetSum _ fun i _ => ?_
  exact integrable_inner_of_periodic (column_measurable hm i) (column_periodic hp i)
    (column_finite hf i) (continuous_fderiv_test_apply hφ i) (hasCompactSupport_fderiv_test_apply hφ i)

theorem continuous_profile {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) (p : Fin k → ℝ) :
    Continuous (fun z : ℝ × Space => d.profile p z.1 z.2) :=
  hd.profile_smooth.continuous.comp (continuous_const.prodMk continuous_id)

theorem continuous_fderiv_profile {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    (p : Fin k → ℝ) : Continuous (fun z : ℝ × Space => fderiv ℝ (d.profile p z.1) z.2) := by
  have h2 : ContDiff ℝ 2 (Function.uncurry fun (z : ℝ × Space) (y : Space) => d.profile p z.1 y) :=
    hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_fst.fst.prodMk contDiff_snd))
  exact (h2.fderiv (g := fun z : ℝ × Space => z.2) contDiff_snd (n := 0) (by norm_num)).continuous

theorem integrable_convection {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    (p : Fin k → ℝ) {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hread : IsReadingOf u v G H) (hGf : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤)
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (G z.1 z.2 (d.profile p z.1 z.2)
      + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)) volume := by
  have hW := continuous_profile hd p
  have hDW := continuous_fderiv_profile hd p
  have hφc := continuous_test hφ
  have hGm := hread.measurable_gradient
  have hvm := hread.measurable_velocity
  simp_rw [inner_add_left]
  refine Integrable.add ?_ ?_
  · have hmeas : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (d.profile p z.1 z.2)) volume :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hGm hW.aestronglyMeasurable
    refine integrable_of_le (c := fun z => ‖d.profile p z.1 z.2‖ * ‖φ z.1 z.2‖)
      (hmeas.inner hφc.aestronglyMeasurable)
      (locallyIntegrable_finsetSum Finset.univ fun j _ =>
        column_locallyIntegrable hGm hread.periodic_gradient hGf j)
      (hW.norm.mul hφc.norm) (hφ.2.1.norm.mul_left) fun z => ?_
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := norm_apply_le_sum (G z.1 z.2) (d.profile p z.1 z.2)
    calc ‖G z.1 z.2 (d.profile p z.1 z.2)‖ * ‖φ z.1 z.2‖
        ≤ (‖d.profile p z.1 z.2‖ * ∑ j : Fin 3, ‖G z.1 z.2 (unitVector j)‖) * ‖φ z.1 z.2‖ := by
          gcongr
      _ = _ := by ring
  · have hmeas : AEStronglyMeasurable
        (fun z : ℝ × Space => fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) volume :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hDW.aestronglyMeasurable hvm
    refine integrable_of_le (c := fun z => ‖fderiv ℝ (d.profile p z.1) z.2‖ * ‖φ z.1 z.2‖)
      (hmeas.inner hφc.aestronglyMeasurable)
      (locallyIntegrable_norm_velocity hread) (hDW.norm.mul hφc.norm) (hφ.2.1.norm.mul_left)
      fun z => ?_
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)‖ * ‖φ z.1 z.2‖
        ≤ (‖fderiv ℝ (d.profile p z.1) z.2‖ * ‖v z.1 z.2‖) * ‖φ z.1 z.2‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ = _ := by ring

theorem integrable_actuator {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    (κ : Fin k → ℝ) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    Integrable (fun z : ℝ × Space => inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)) volume := by
  simp_rw [sum_inner, inner_smul_left]
  refine integrable_finsetSum _ fun i _ => ?_
  refine Integrable.const_mul ?_ _
  have hfin : periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) < ⊤ := by
    have h := hd.actuator_norm
    have hle : periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
        ∑ j, periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2) :=
      Finset.single_le_sum (f := fun j => periodLIntegral (fun σ y => ‖d.actuator j σ y‖ ^ 2))
        (fun j _ => bot_le) (Finset.mem_univ i)
    exact lt_of_le_of_lt (hle.trans h) ENNReal.ofReal_lt_top
  exact integrable_inner_of_periodic (hd.actuator_measurable i) (hd.actuator_periodic i) hfin
    (continuous_test hφ) hφ.2.1

theorem bordered_fst {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (f : HH) (κ : Fin k → ℝ) :
    (bordered d p (f, κ)).1 = f + convection d p (freeInv (d.period p) f) + actuatorH d κ := by
  simp only [bordered, ContinuousLinearMap.prod_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']

theorem integrand_eq (g F1 F2 F3 φ : Space) (a : ℝ) :
    inner ℝ g φ + a + inner ℝ (F1 + F2) φ + inner ℝ F3 φ = inner ℝ (g + F1 + F2 + F3) φ + a := by
  simp only [inner_add_left]
  ring

theorem isRightSide_of {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) (p : Fin k → ℝ)
    (f : HH) (κ : Fin k → ℝ) (F : ℝ → Space → Space) {u : XX} {v : VelField} {G : GradField}
    {H : SecondField} {g : ℝ → Space → Space} (hread : IsReadingOf u v G H)
    (hpert : IsPerturbation d.symmetries (d.period p) v G H g)
    (hpair : ∀ φ, IsSpaceTimeTestField φ → ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
      inner ℝ (f + convection d p u + actuatorH d κ) (testInHH φ))
    (hg : ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) = inner ℝ f (testInHH φ))
    (hconv : ∀ φ, IsSpaceTimeTestField φ →
      ∫ z : ℝ × Space, inner ℝ (G z.1 z.2 (d.profile p z.1 z.2)
        + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) (φ z.1 z.2) =
        inner ℝ (convection d p u) (testInHH φ))
    (hact : ∀ φ, IsSpaceTimeTestField φ → inner ℝ (actuatorH d κ) (testInHH φ) =
      ∫ z : ℝ × Space, inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)) :
    IsRightSide (d.profile p) d.actuator κ v G g F := by
  intro φ hφ
  have hA : Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) volume :=
    (integrable_inner_of_periodic hpert.measurable_derivative hpert.periodic_derivative
      hpert.derivative_finite (continuous_test hφ) hφ.2.1).add
      (integrable_matNorm hpert.measurable_gradient hpert.periodic_gradient hpert.gradient_finite hφ)
  have hB := integrable_convection hd p hread hpert.gradient_finite hφ
  have hC := integrable_actuator hd κ hφ
  have hAB : Integrable (fun z : ℝ × Space => (inner ℝ (g z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) + inner ℝ (G z.1 z.2 (d.profile p z.1 z.2)
      + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)) volume := hA.add hB
  have e3 : ∫ z : ℝ × Space, (inner ℝ (g z.1 z.2 + G z.1 z.2 (d.profile p z.1 z.2)
        + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2) + ∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) =
      ∫ z : ℝ × Space, ((inner ℝ (g z.1 z.2) (φ z.1 z.2)
        + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) + inner ℝ (G z.1 z.2 (d.profile p z.1 z.2)
        + fderiv ℝ (d.profile p z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)
        + inner ℝ (∑ i, κ i • d.actuator i z.1 z.2) (φ z.1 z.2)) :=
    integral_congr_ae (Eventually.of_forall fun z => (integrand_eq _ _ _ _ _ _).symm)
  have e4 := integral_add hAB hC
  have e5 := integral_add hA hB
  have e1 := hpair φ hφ
  simp only [inner_add_left] at e1
  have e6 := hg φ hφ
  have e7 := hconv φ hφ
  have e8 := hact φ hφ
  show _ = _
  linarith

theorem size_bound_of {k : ℕ} (w : Space → ℝ) (u : XX) (κ : Fin k → ℝ) (W A c : ℝ)
    (x y : Fin k → ℝ) (hE : W = energyW w u) (hxy : x = y)
    (hc : Real.sqrt (W + ∑ i, κ i ^ 2) ≤ A + c * vecNorm x) : sizeZ w u κ ≤ A + c * vecNorm y := by
  subst hE
  subst hxy
  exact hc

end Internal.CoerciveBordered

open Internal.CoerciveBordered

theorem coerciveBorderedHolds_of (h1 : ReadingExistsHolds) (h2 : ReadingEnergyHolds)
    (h3 : FreePerturbationHolds) (h4 : ConvectionHolds) (h5 : DataHolds) (_h6 : TestPairingHolds) :
    CoerciveBorderedHolds := by
  intro k d hd p hp f hf κ F hF hpair
  have h1' := h1 (freeInv (d.period p) f)
  obtain ⟨v, hv⟩ := h1'
  obtain ⟨G, hG⟩ := hv
  obtain ⟨H, hH⟩ := hG
  have hread := hH.1
  have h3' := h3 d.symmetries (d.period p) (hd.period_pos p hp) f hf v G H hread
  obtain ⟨g, hg0⟩ := h3'
  have hpert := hg0.1
  have hg := hg0.2
  have hadm : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hE := (h2 d.weightFn d.weight hadm _ v G H hread).1
  have hconv := (h4 d hd p hp).2.2
  have hact := (h5 d hd p hp).2.2.1
  have hpin := (h5 d hd p hp).2.2.2.2.2
  have hpair' : ∀ φ, IsSpaceTimeTestField φ → ∫ z : ℝ × Space, inner ℝ (F z.1 z.2) (φ z.1 z.2) =
      inner ℝ (f + convection d p (freeInv (d.period p) f) + actuatorH d κ) (testInHH φ) := by
    intro φ hφ
    exact (hpair φ hφ).trans (congrArg (fun x : HH => inner ℝ x (testInHH φ)) (bordered_fst d p f κ))
  have hRS := isRightSide_of hd p f κ F hread hpert hpair' hg (fun φ hφ => hconv _ v G H hread φ hφ)
    (fun φ hφ => hact κ φ hφ)
  have hc := hd.coercive p hp v G H g hpert κ F hF.1 hF.2.1 hF.2.2 hRS
  have hpv : (fun i => pinValue (d.pin i) G) = pinMap d (freeInv (d.period p) f) :=
    funext fun i => (hpin _ v G H hread i).symm
  exact size_bound_of _ _ κ _ _ _ _ _ hE hpv hc

end Breakdown.Cert
