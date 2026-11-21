import Breakdown.CertCell.AssemblyStatements

open MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open CellCalculus SteadyCert

private def harmonicCutoff (σ : ℝ) : ℝ := Real.smoothTransition σ - Real.smoothTransition (σ - 1)

private theorem harmonicCutoff_contDiff : ContDiff ℝ ∞ harmonicCutoff :=
  (Real.smoothTransition.contDiff (n := ⊤)).sub
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const))

private theorem harmonicCutoff_eq_zero {σ : ℝ} (h : σ ∉ Set.Icc (0 : ℝ) 2) : harmonicCutoff σ = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · simp [harmonicCutoff, Real.smoothTransition.zero_of_nonpos h.le,
      Real.smoothTransition.zero_of_nonpos (by linarith : σ - 1 ≤ 0)]
  · simp [harmonicCutoff, Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ σ),
      Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ σ - 1)]

private theorem harmonicCutoff_abs_le (σ : ℝ) : |harmonicCutoff σ| ≤ 1 := by
  unfold harmonicCutoff
  have h1 := Real.smoothTransition.nonneg σ
  have h2 := Real.smoothTransition.le_one σ
  have h3 := Real.smoothTransition.nonneg (σ - 1)
  have h4 := Real.smoothTransition.le_one (σ - 1)
  rw [abs_le]
  constructor <;> linarith

private theorem harmonicCutoff_add_shift {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    harmonicCutoff σ + harmonicCutoff (σ + 1) = 1 := by
  unfold harmonicCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : σ - 1 ≤ 0),
    Real.smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ σ + 1), show σ + 1 - 1 = σ by ring]
  ring

private theorem integral_harmonicCutoff_mul {g : ℝ → ℝ} (hg : ∀ σ, g (σ + 1) = g σ)
    (hint : IntegrableOn g (Set.Icc (0 : ℝ) 1)) :
    ∫ σ, harmonicCutoff σ * g σ = ∫ σ in Set.Icc (0 : ℝ) 1, g σ := by
  have hc : Continuous harmonicCutoff := harmonicCutoff_contDiff.continuous
  have hg01 : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 hint
  have hA : IntervalIntegrable (fun σ => harmonicCutoff σ * g σ) volume 0 1 :=
    hg01.continuousOn_mul hc.continuousOn
  have hshift : (fun σ => harmonicCutoff (σ + 1) * g (σ + 1)) = fun σ => harmonicCutoff (σ + 1) * g σ := by
    funext σ
    rw [hg]
  have hB0 : IntervalIntegrable (fun σ => harmonicCutoff (σ + 1) * g (σ + 1)) volume 0 1 := by
    rw [hshift]
    exact hg01.continuousOn_mul (hc.comp (continuous_id.add continuous_const)).continuousOn
  have hB : IntervalIntegrable (fun σ => harmonicCutoff σ * g σ) volume 1 2 := by
    have h := hB0.comp_add_right (-1)
    norm_num at h
    exact h
  have hsupp : ∀ σ, σ ∉ Set.Icc (0 : ℝ) 2 → harmonicCutoff σ * g σ = 0 := fun σ h => by
    rw [harmonicCutoff_eq_zero h, zero_mul]
  have h12 : (∫ σ in (1 : ℝ)..2, harmonicCutoff σ * g σ) =
      ∫ σ in (0 : ℝ)..1, harmonicCutoff (σ + 1) * g (σ + 1) := by
    have h := intervalIntegral.integral_comp_add_right (fun σ => harmonicCutoff σ * g σ) (1 : ℝ)
      (a := 0) (b := 1)
    norm_num at h
    exact h.symm
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    ← intervalIntegral.integral_add_adjacent_intervals hA hB, h12, ← intervalIntegral.integral_add hA hB0,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  refine intervalIntegral.integral_congr (fun σ hσ => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hσ
  rw [hg, ← add_mul, harmonicCutoff_add_shift hσ.1 hσ.2, one_mul]

private theorem harmonic_testField {φ : Space → Space} (hφ : IsStationaryTestField φ) {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) : IsSpaceTimeTestField (fun σ y => (harmonicCutoff σ * w σ) • φ y) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((harmonicCutoff_contDiff.mul hw).comp contDiff_fst).smul (hφ.1.comp contDiff_snd)
  · refine HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 2 ×ˢ tsupport φ)
      (isCompact_Icc.prod hφ.2.1.isCompact) ?_
    intro z hz
    simp only [Set.mem_prod, not_and_or] at hz
    rcases hz with h | h
    · simp [harmonicCutoff_eq_zero h]
    · simp [image_eq_zero_of_notMem_tsupport h]
  · intro s y
    have hd : DifferentiableAt ℝ φ y := (hφ.1.differentiable (by simp)).differentiableAt
    have h0 := hφ.2.2 y
    unfold divergenceAt at h0 ⊢
    show ∑ i, ((fderiv ℝ ((harmonicCutoff s * w s) • φ) y) (unitVector i)).ofLp i = 0
    rw [fderiv_const_smul hd]
    simp only [FunLike.coe_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      h0, mul_zero]

private theorem harmonic_swap_aesm {P : ℝ → Space → Space}
    (hP : AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2) volume) (t : Set Space) (s : Set ℝ) :
    AEStronglyMeasurable (fun z : Space × ℝ => P z.2 z.1) ((volume.restrict t).prod (volume.restrict s)) := by
  have h1 : AEStronglyMeasurable (fun z : Space × ℝ => P z.2 z.1)
      ((volume : Measure Space).prod (volume : Measure ℝ)) := by
    rw [Measure.volume_eq_prod] at hP
    exact hP.prod_swap
  rw [Measure.prod_restrict]
  exact h1.restrict

private theorem harmonic_weighted_aesm {P : ℝ → Space → Space}
    (hP : AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2) volume) {w : ℝ → ℝ} (hw : Continuous w) :
    AEStronglyMeasurable (fun y => ∫ τ in Set.Icc (0 : ℝ) 1, w τ • P τ y) volume := by
  have h := harmonic_swap_aesm hP Set.univ (Set.Icc (0 : ℝ) 1)
  rw [Measure.restrict_univ] at h
  exact ((hw.comp continuous_snd).aestronglyMeasurable.smul h).integral_prod_right'

private theorem harmonic_box_integrable {P : ℝ → Space → Space}
    (hP : AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2) volume) (hsq : HasLocalSquare P) (R : ℝ) :
    IntegrableOn (fun z : ℝ × Space => P z.1 z.2) (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall 0 R)
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => ‖P z.1 z.2‖ ^ 2) volume := hP.norm.pow 2
  have hfin : (∫⁻ z in Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖P z.1 z.2‖ ^ 2)) < ⊤ := by
    rw [Measure.volume_eq_prod, setLIntegral_prod]
    · exact hsq R
    · exact hm.aemeasurable.ennreal_ofReal.restrict
  have hsqint : IntegrableOn (fun z : ℝ × Space => ‖P z.1 z.2‖ ^ 2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) := by
    refine ⟨hm.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => by positivity))]
    exact hfin
  have hone : IntegrableOn (fun _ : ℝ × Space => (1 : ℝ))
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) := continuousOn_const.integrableOn_compact hK
  refine Integrable.mono' (hone.add hsqint) hP.restrict (Filter.Eventually.of_forall (fun z => ?_))
  show ‖P z.1 z.2‖ ≤ 1 + ‖P z.1 z.2‖ ^ 2
  nlinarith [norm_nonneg (P z.1 z.2), sq_nonneg (‖P z.1 z.2‖ - 1)]

private theorem harmonic_box_integrable_shift {P : ℝ → Space → Space}
    (hP : AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2) volume) (hper : IsTimePeriodic P)
    (hsq : HasLocalSquare P) (R : ℝ) :
    IntegrableOn (fun z : ℝ × Space => P z.1 z.2) (Set.Icc (1 : ℝ) 2 ×ˢ Metric.closedBall (0 : Space) R) := by
  have he : MeasurePreserving (Prod.map (fun σ : ℝ => σ + 1) (id : Space → Space)) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (measurePreserving_add_right volume (1 : ℝ)).prod (MeasurePreserving.id volume)
  have hemb : MeasurableEmbedding (Prod.map (fun σ : ℝ => σ + 1) (id : Space → Space)) :=
    ((MeasurableEquiv.addRight (1 : ℝ)).prodCongr (MeasurableEquiv.refl Space)).measurableEmbedding
  rw [← he.integrableOn_comp_preimage hemb]
  have hpre : Prod.map (fun σ : ℝ => σ + 1) (id : Space → Space) ⁻¹'
      (Set.Icc (1 : ℝ) 2 ×ˢ Metric.closedBall (0 : Space) R) =
      Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R := by
    ext ⟨σ, y⟩
    simp only [Set.mem_preimage, Prod.map, Set.mem_prod, Set.mem_Icc, id]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3⟩
  have hcomp : ((fun z : ℝ × Space => P z.1 z.2) ∘ Prod.map (fun σ : ℝ => σ + 1) (id : Space → Space)) =
      fun z => P z.1 z.2 := by
    funext z
    simp [hper z.1 z.2]
  rw [hpre, hcomp]
  exact harmonic_box_integrable hP hsq R

private theorem harmonic_sq_norm_integral_le {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : μ Set.univ = 1)
    {g : ℝ → Space} (hg : AEStronglyMeasurable g μ) :
    ENNReal.ofReal (‖∫ τ, g τ ∂μ‖ ^ 2) ≤ ∫⁻ τ, ENNReal.ofReal (‖g τ‖ ^ 2) ∂μ := by
  have h1 : ‖∫ τ, g τ ∂μ‖ₑ ≤ eLpNorm g 2 μ := by
    calc ‖∫ τ, g τ ∂μ‖ₑ ≤ ∫⁻ τ, ‖g τ‖ₑ ∂μ := enorm_integral_le_lintegral_enorm g
      _ = eLpNorm g 1 μ := eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm g 2 μ * μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hg
      _ = eLpNorm g 2 μ := by rw [hμ, ENNReal.one_rpow, mul_one]
  have h2 : eLpNorm g 2 μ ^ 2 = ∫⁻ τ, ‖g τ‖ₑ ^ 2 ∂μ := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := μ) (p := 2) (by norm_num)
    simpa using h
  calc ENNReal.ofReal (‖∫ τ, g τ ∂μ‖ ^ 2) = ‖∫ τ, g τ ∂μ‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ eLpNorm g 2 μ ^ 2 := by gcongr
    _ = ∫⁻ τ, ‖g τ‖ₑ ^ 2 ∂μ := h2
    _ = ∫⁻ τ, ENNReal.ofReal (‖g τ‖ ^ 2) ∂μ := by
        congr 1
        funext τ
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

private theorem harmonic_weighted_localSquare {P : ℝ → Space → Space}
    (hP : AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2) volume) (hsq : HasLocalSquare P)
    {w : ℝ → ℝ} (hw : Continuous w) (hwb : ∀ σ, |w σ| ≤ 1) :
    IsLocalSquareIntegrable (fun y => ‖∫ τ in Set.Icc (0 : ℝ) 1, w τ • P τ y‖ ^ 2) := by
  intro K hK
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Space)).1 hK.isBounded
  refine IntegrableOn.mono_set ?_ hR
  have hμ : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by simp
  have hslice : ∀ᵐ y ∂(volume : Measure Space),
      AEStronglyMeasurable (fun τ => w τ • P τ y) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have h := harmonic_swap_aesm hP Set.univ (Set.Icc (0 : ℝ) 1)
    rw [Measure.restrict_univ] at h
    exact ((hw.comp continuous_snd).aestronglyMeasurable.smul h).prodMk_left
  have hbound : ∀ᵐ y ∂(volume.restrict (Metric.closedBall (0 : Space) R)),
      ENNReal.ofReal (‖∫ τ in Set.Icc (0 : ℝ) 1, w τ • P τ y‖ ^ 2) ≤
        ∫⁻ τ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (‖P τ y‖ ^ 2) := by
    refine ae_restrict_of_ae (hslice.mono (fun y hy => ?_))
    refine (harmonic_sq_norm_integral_le hμ hy).trans (lintegral_mono (fun τ => ?_))
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hwb τ)
  have hmeas : AEMeasurable (Function.uncurry fun y τ => ENNReal.ofReal (‖P τ y‖ ^ 2))
      ((volume.restrict (Metric.closedBall (0 : Space) R)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have h := (harmonic_swap_aesm hP (Metric.closedBall (0 : Space) R) (Set.Icc (0 : ℝ) 1)).norm.pow 2
    exact h.aemeasurable.ennreal_ofReal
  have hswap := lintegral_lintegral_swap hmeas
  refine ⟨((harmonic_weighted_aesm hP hw).norm.pow 2).restrict, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun y => by positivity))]
  calc _ ≤ _ := lintegral_mono_ae hbound
    _ = _ := hswap
    _ < ⊤ := hsq R

private theorem harmonic_weighted_annihilates {P : ℝ → Space → Space}
    (hP : AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2) volume) (hper : IsTimePeriodic P)
    (hsq : HasLocalSquare P) (hann : IsSpaceTimeAnnihilator P)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hwp : ∀ σ, w (σ + 1) = w σ) (hwb : ∀ σ, |w σ| ≤ 1)
    {φ : Space → Space} (hφ : IsStationaryTestField φ) :
    ∫ y, inner ℝ (∫ τ in Set.Icc (0 : ℝ) 1, w τ • P τ y) (φ y) = 0 := by
  have hwc : Continuous w := hw.continuous
  have hcc : Continuous harmonicCutoff := harmonicCutoff_contDiff.continuous
  have hφc : Continuous φ := hφ.1.continuous
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Space)).1 hφ.2.1.isCompact.isBounded
  obtain ⟨M, hM⟩ := hφc.bounded_above_of_compact_support hφ.2.1
  have hφB : ∀ y, y ∉ Metric.closedBall (0 : Space) R → φ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hR h))
  let F : ℝ × Space → ℝ := fun z => inner ℝ (P z.1 z.2) ((harmonicCutoff z.1 * w z.1) • φ z.2)
  have hFsupp : Function.support F ⊆ Set.Icc (0 : ℝ) 2 ×ˢ Metric.closedBall (0 : Space) R := by
    intro z hz
    by_contra h
    simp only [Set.mem_prod, not_and_or] at h
    apply hz
    rcases h with h | h
    · simp [F, harmonicCutoff_eq_zero h]
    · simp [F, hφB _ h]
  have hbox : IntegrableOn (fun z : ℝ × Space => P z.1 z.2)
      (Set.Icc (0 : ℝ) 2 ×ˢ Metric.closedBall (0 : Space) R) := by
    refine ((harmonic_box_integrable hP hsq R).union (harmonic_box_integrable_shift hP hper hsq R)).mono_set ?_
    rintro ⟨σ, y⟩ ⟨⟨h0, h2⟩, hy⟩
    rcases le_total σ 1 with h | h
    · exact Or.inl ⟨⟨h0, h⟩, hy⟩
    · exact Or.inr ⟨⟨h, h2⟩, hy⟩
  have hFint : Integrable F := by
    rw [← integrableOn_iff_integrable_of_support_subset hFsupp]
    refine Integrable.mono' (hbox.norm.const_mul M) ?_ (Filter.Eventually.of_forall (fun z => ?_))
    · exact (hP.inner ((((hcc.mul hwc).comp continuous_fst).smul
        (hφc.comp continuous_snd)).aestronglyMeasurable)).restrict
    · show ‖F z‖ ≤ M * ‖P z.1 z.2‖
      calc ‖F z‖ ≤ ‖P z.1 z.2‖ * ‖(harmonicCutoff z.1 * w z.1) • φ z.2‖ := norm_inner_le_norm _ _
        _ ≤ ‖P z.1 z.2‖ * M := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_mul]
          calc |harmonicCutoff z.1| * |w z.1| * ‖φ z.2‖ ≤ 1 * 1 * M := by
                gcongr
                · exact harmonicCutoff_abs_le _
                · exact hwb _
                · exact hM _
            _ = M := by ring
        _ = M * ‖P z.1 z.2‖ := mul_comm _ _
  have hfub : ∫ z, F z = ∫ y, ∫ σ, F (σ, y) :=
    integral_prod_symm (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space)) F hFint
  have hslice : ∀ᵐ y ∂(volume : Measure Space), y ∈ Metric.closedBall (0 : Space) R →
      Integrable (fun σ => P σ y) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have h := harmonic_box_integrable hP hsq R
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    exact (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).1 h.prod_left_ae
  have hpt : ∀ᵐ y ∂(volume : Measure Space),
      ∫ σ, F (σ, y) = inner ℝ (∫ τ in Set.Icc (0 : ℝ) 1, w τ • P τ y) (φ y) := by
    refine hslice.mono (fun y hy => ?_)
    by_cases hyB : y ∈ Metric.closedBall (0 : Space) R
    · have hI := hy hyB
      have hwI : Integrable (fun σ => w σ • P σ y) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        refine Integrable.mono' hI.norm (hwc.aestronglyMeasurable.smul hI.aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun σ => ?_))
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hwb σ)
      have hF : ∀ σ, F (σ, y) = harmonicCutoff σ * inner ℝ (w σ • P σ y) (φ y) := by
        intro σ
        simp only [F, real_inner_smul_left, real_inner_smul_right]
        ring
      have hg : IntegrableOn (fun σ => inner ℝ (w σ • P σ y) (φ y)) (Set.Icc (0 : ℝ) 1) :=
        hwI.inner_const (φ y)
      calc ∫ σ, F (σ, y) = ∫ σ, harmonicCutoff σ * inner ℝ (w σ • P σ y) (φ y) := by
            congr 1
            funext σ
            exact hF σ
        _ = ∫ σ in Set.Icc (0 : ℝ) 1, inner ℝ (w σ • P σ y) (φ y) :=
            integral_harmonicCutoff_mul (g := fun σ => inner ℝ (w σ • P σ y) (φ y))
              (fun σ => by simp only [hwp σ, hper σ y]) hg
        _ = ∫ σ in Set.Icc (0 : ℝ) 1, inner ℝ (φ y) (w σ • P σ y) := by
            congr 1
            funext σ
            exact real_inner_comm _ _
        _ = inner ℝ (φ y) (∫ σ in Set.Icc (0 : ℝ) 1, w σ • P σ y) := integral_inner hwI (φ y)
        _ = _ := real_inner_comm _ _
    · have h0 := hφB y hyB
      simp [F, h0]
  have h := hann _ (harmonic_testField hφ hw)
  calc ∫ y, inner ℝ (∫ τ in Set.Icc (0 : ℝ) 1, w τ • P τ y) (φ y) = ∫ y, ∫ σ, F (σ, y) :=
        (integral_congr_ae hpt).symm
    _ = ∫ z, F z := hfub.symm
    _ = 0 := h

end Internal

open _root_.Breakdown.CertCell.Assembly.Internal CellCalculus

theorem harmonicAnnihilator_holds : HarmonicAnnihilatorHolds := by
  intro P hP hper hsq hann ν
  have hcd : ContDiff ℝ ∞ (fun τ : ℝ => Real.cos (2 * Real.pi * ν * τ)) :=
    Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  have hsd : ContDiff ℝ ∞ (fun τ : ℝ => Real.sin (2 * Real.pi * ν * τ)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have hcp : ∀ σ : ℝ, Real.cos (2 * Real.pi * ν * (σ + 1)) = Real.cos (2 * Real.pi * ν * σ) := fun σ => by
    rw [show 2 * Real.pi * (ν : ℝ) * (σ + 1) = 2 * Real.pi * ν * σ + (ν : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_add_int_mul_two_pi _ ν
  have hsp : ∀ σ : ℝ, Real.sin (2 * Real.pi * ν * (σ + 1)) = Real.sin (2 * Real.pi * ν * σ) := fun σ => by
    rw [show 2 * Real.pi * (ν : ℝ) * (σ + 1) = 2 * Real.pi * ν * σ + (ν : ℝ) * (2 * Real.pi) by ring]
    exact Real.sin_add_int_mul_two_pi _ ν
  have hcb : ∀ σ : ℝ, |Real.cos (2 * Real.pi * ν * σ)| ≤ 1 := fun σ => Real.abs_cos_le_one _
  have hsb : ∀ σ : ℝ, |Real.sin (2 * Real.pi * ν * σ)| ≤ 1 := fun σ => Real.abs_sin_le_one _
  refine ⟨harmonic_weighted_aesm hP hcd.continuous, (harmonic_weighted_aesm hP hsd.continuous).neg,
    harmonic_weighted_localSquare hP hsq hcd.continuous hcb, ?_,
    fun φ hφ => harmonic_weighted_annihilates hP hper hsq hann hcd hcp hcb hφ, fun φ hφ => ?_⟩
  · intro K hK
    have h := harmonic_weighted_localSquare hP hsq hsd.continuous hsb K hK
    simpa [harmonicSin, norm_neg] using h
  · have h := harmonic_weighted_annihilates hP hper hsq hann hsd hsp hsb hφ
    simp only [harmonicSin, inner_neg_left, integral_neg, h, neg_zero]

end Assembly

end CertCell

end Breakdown
