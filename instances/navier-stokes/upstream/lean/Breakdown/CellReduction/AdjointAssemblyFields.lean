import Breakdown.CellReduction.AdjointAssemblyMeasure

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

theorem continuous_transposeApply :
    Continuous (fun p : (Space →L[ℝ] Space) × Space => transposeApply p.1 p.2) := by
  unfold transposeApply
  fun_prop

theorem continuous_advectionShift {δ ζ : ℝ → Space → Space}
    (hδ : ContDiff ℝ 1 (fun z : ℝ × Space => δ z.1 z.2)) (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) :
    Continuous (fun z : ℝ × Space => advectionShift δ ζ z.1 z.2) := by
  unfold advectionShift
  exact (continuous_transposeApply.comp ((slice_fderiv_continuous hδ).prodMk hζ.continuous)).sub
    ((slice_fderiv_continuous hζ).clm_apply hδ.continuous)

theorem continuous_adjointTransport (P : ℝ) {W ζ : ℝ → Space → Space}
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) (hζ : ContDiff ℝ 1 (fun z : ℝ × Space => ζ z.1 z.2)) :
    Continuous (fun z : ℝ × Space => adjointTransport P W ζ z.1 z.2) := by
  have h0 := timeDerivative_continuous hζ
  have h1 : Continuous (fun z : ℝ × Space => -(1 / P) • timeDerivative ζ z.1 z.2) := by fun_prop
  have h2 : Continuous (fun z : ℝ × Space => ζ z.1 z.2) := hζ.continuous
  have h5 := (slice_fderiv_continuous hζ).clm_apply continuous_snd
  have h3 : Continuous (fun z : ℝ × Space => (1 / 2 : ℝ) • fderiv ℝ (ζ z.1) z.2 z.2) := by fun_prop
  have h4 := continuous_advectionShift hW hζ
  exact ((h1.sub h2).sub h3).add h4

theorem adjointField_nonneg {ζ : ℝ → Space → Space} {C γ : ℝ} (h : IsAdjointField ζ C γ) : 0 ≤ C := by
  have h0 := (h.decay 0 0).1
  simp only [norm_zero, add_zero, Real.one_rpow, div_one] at h0
  exact (norm_nonneg _).trans h0

theorem norm_advectionShift_le {δ ζ : ℝ → Space → Space} {D C γ : ℝ} (hδ : IsFlowPiece δ D)
    (hζ : IsAdjointField ζ C γ) (σ : ℝ) (y : Space) :
    ‖advectionShift δ ζ σ y‖ ≤ 4 * D * C / (1 + ‖y‖) ^ γ := by
  have hD := flowPiece_nonneg hδ
  have hC := adjointField_nonneg hζ
  obtain ⟨d1, d2⟩ := hδ.decay σ y
  obtain ⟨z1, -, z3⟩ := hζ.decay σ y
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hw : 0 < (1 + ‖y‖) ^ γ := by positivity
  set a := C / (1 + ‖y‖) ^ γ with ha
  have ha0 : 0 ≤ a := div_nonneg hC hw.le
  have e1 : D / (1 + ‖y‖) ≤ D := div_le_self hD (by linarith)
  have t1 : ‖transposeApply (fderiv ℝ (δ σ) y) (ζ σ y)‖ ≤ 3 * D * a := by
    refine (norm_transposeApply_le _ _).trans ?_
    have := mul_le_mul (d2.trans e1) z1 (norm_nonneg _) hD
    nlinarith
  have t2 : ‖fderiv ℝ (ζ σ) y (δ σ y)‖ ≤ D * a := by
    refine ((fderiv ℝ (ζ σ) y).le_opNorm _).trans ?_
    have := mul_le_mul (z3.trans (div_succ_le hy hC)) d1 (norm_nonneg _) ha0
    linarith
  have e : 4 * D * C / (1 + ‖y‖) ^ γ = 4 * D * a := by rw [ha, mul_div_assoc]
  rw [e]
  unfold advectionShift
  refine (norm_sub_le _ _).trans ?_
  linarith

theorem norm_adjointTransport_le {W ζ : ℝ → Space → Space} {D C γ : ℝ} (P : ℝ) (hW : IsFlowPiece W D)
    (hζ : IsAdjointField ζ C γ) (σ : ℝ) (y : Space) :
    ‖adjointTransport P W ζ σ y‖ ≤ (|1 / P| + 2 + 4 * D) * C / (1 + ‖y‖) ^ γ := by
  have hD := flowPiece_nonneg hW
  have hC := adjointField_nonneg hζ
  obtain ⟨z1, z2, z3⟩ := hζ.decay σ y
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hw : 0 < (1 + ‖y‖) ^ γ := by positivity
  have hadv := norm_advectionShift_le hW hζ σ y
  set a := C / (1 + ‖y‖) ^ γ with ha
  have ha0 : 0 ≤ a := div_nonneg hC hw.le
  have e4 : 4 * D * C / (1 + ‖y‖) ^ γ = 4 * D * a := by rw [ha, mul_div_assoc]
  rw [e4] at hadv
  have t1 : ‖(1 / P) • timeDerivative ζ σ y‖ ≤ |1 / P| * a := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left z2 (abs_nonneg _)
  have t3 : ‖(1 / 2 : ℝ) • fderiv ℝ (ζ σ) y y‖ ≤ (1 / 2) * a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left (((fderiv ℝ (ζ σ) y).le_opNorm y).trans ?_) (by norm_num)
    have := mul_le_mul_of_nonneg_right z3 hy
    have h2 := mul_div_succ_le (γ := γ) hy hC
    linarith
  have e : (|1 / P| + 2 + 4 * D) * C / (1 + ‖y‖) ^ γ = (|1 / P| + 2 + 4 * D) * a := by rw [ha, mul_div_assoc]
  rw [e]
  unfold adjointTransport
  have n1 := norm_sub_le (-(1 / P) • timeDerivative ζ σ y - ζ σ y) ((1 / 2 : ℝ) • fderiv ℝ (ζ σ) y y)
  have n2 := norm_sub_le (-(1 / P) • timeDerivative ζ σ y) (ζ σ y)
  have n3 := norm_add_le (-(1 / P) • timeDerivative ζ σ y - ζ σ y - (1 / 2 : ℝ) • fderiv ℝ (ζ σ) y y)
    (advectionShift W ζ σ y)
  have n4 : ‖-(1 / P) • timeDerivative ζ σ y‖ = ‖(1 / P) • timeDerivative ζ σ y‖ := by rw [neg_smul, norm_neg]
  nlinarith [abs_nonneg (1 / P)]

theorem norm_fittedResidual_le {f ζ : ℝ → Space → Space} {D C γ : ℝ} (c : ℝ) (hf : IsFlowPiece f D)
    (hζ : IsAdjointField ζ C γ) (σ : ℝ) (y : Space) :
    ‖advectionShift f ζ σ y - c • timeDerivative ζ σ y‖ ≤ (4 * D + |c|) * C / (1 + ‖y‖) ^ γ := by
  have hadv := norm_advectionShift_le hf hζ σ y
  obtain ⟨-, z2, -⟩ := hζ.decay σ y
  have t : ‖c • timeDerivative ζ σ y‖ ≤ |c| * (C / (1 + ‖y‖) ^ γ) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left z2 (abs_nonneg _)
  have e : (4 * D + |c|) * C / (1 + ‖y‖) ^ γ = 4 * D * C / (1 + ‖y‖) ^ γ + |c| * (C / (1 + ‖y‖) ^ γ) := by
    ring
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add hadv t)

theorem matrixDivergence_zero : matrixDivergence (fun _ : Space => (0 : Space →L[ℝ] Space)) = fun _ => 0 := by
  funext y
  simp [matrixDivergence]

theorem fittedField {f ζ : ℝ → Space → Space} {D C γ : ℝ} (c : ℝ) (hf : IsFlowPiece f D)
    (hζ : IsAdjointField ζ C γ) :
    IsResidualField (fun σ y => advectionShift f ζ σ y - c • timeDerivative ζ σ y) (fun _ _ => 0)
      ((4 * D + |c|) * C) γ := by
  have hD := flowPiece_nonneg hf
  have hC := adjointField_nonneg hζ
  have hK : 0 ≤ (4 * D + |c|) * C := mul_nonneg (by positivity) hC
  refine ⟨hζ.rate_gt, ?_, aestronglyMeasurable_const, fun σ => ?_, fun σ y => ⟨?_, ?_⟩, fun σ => ?_⟩
  · have h1 := continuous_advectionShift hf.smooth hζ.smooth
    have h0 := timeDerivative_continuous hζ.smooth
    have h2 : Continuous (fun z : ℝ × Space => c • timeDerivative ζ z.1 z.2) := by fun_prop
    exact (h1.sub h2).aestronglyMeasurable
  · rw [matrixDivergence_zero]
    exact ⟨locallyIntegrable_zero, locallyIntegrable_zero, fun φ _ c => by simp⟩
  · exact norm_fittedResidual_le c hf hζ σ y
  · simp only [norm_zero]
    positivity
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [matrixDivergence_zero, norm_zero]
    positivity

theorem gradientNorm_le {Γ : Set Symmetry} {P : ℝ} {v g : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hp : IsPerturbation Γ P v G H g) {w₀ : ℝ} (hw : 0 < w₀) :
    gradientNorm G ≤ Real.sqrt (weightedEnergy (fun _ => w₀) G H) / Real.sqrt w₀ := by
  have hmG : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2))) periodMeasure :=
    (continuous_entrySq.comp_aestronglyMeasurable (aesm_period hp.measurable_gradient)).aemeasurable.ennreal_ofReal
  have hmH : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2)) periodMeasure := by
    have h1 : Continuous (fun A : Space →L[ℝ] Space →L[ℝ] Space => ‖secondDerivTrace A‖ ^ 2) := by
      unfold secondDerivTrace
      fun_prop
    exact (h1.comp_aestronglyMeasurable (aesm_period hp.measurable_secondDeriv)).aemeasurable.ennreal_ofReal
  have eG : periodLIntegral (fun σ y => matSq (G σ y)) =
      ∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2)) ∂periodMeasure := periodL_eq hmG
  have eH : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) =
      ∫⁻ z, ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2) ∂periodMeasure := periodL_eq hmH
  have hsum : AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2 + w₀ * matSq (G z.1 z.2))) periodMeasure := by
    have h1 : Continuous (fun p : (Space →L[ℝ] Space →L[ℝ] Space) × (Space →L[ℝ] Space) =>
        ‖secondDerivTrace p.1‖ ^ 2 + w₀ * matSq p.2) := by
      unfold secondDerivTrace matSq
      fun_prop
    have hHG : AEStronglyMeasurable (fun z : ℝ × Space => (H z.1 z.2, G z.1 z.2)) periodMeasure :=
      AEStronglyMeasurable.prodMk (aesm_period hp.measurable_secondDeriv) (aesm_period hp.measurable_gradient)
    exact (h1.comp_aestronglyMeasurable hHG).aemeasurable.ennreal_ofReal
  have eE : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y)) =
      ∫⁻ z, ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2 + w₀ * matSq (G z.1 z.2)) ∂periodMeasure :=
    periodL_eq hsum
  have split : ∫⁻ z, ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2 + w₀ * matSq (G z.1 z.2)) ∂periodMeasure =
      (∫⁻ z, ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2) ∂periodMeasure)
        + ENNReal.ofReal w₀ * ∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2)) ∂periodMeasure := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left' hmH]
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hw.le (entrySq_nonneg _)), ENNReal.ofReal_mul hw.le]
  have hLG : ∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2)) ∂periodMeasure < ⊤ := eG ▸ hp.gradient_finite
  have hLH : ∫⁻ z, ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2) ∂periodMeasure < ⊤ := eH ▸ hp.sumSecondPartials_finite
  have hE : weightedEnergy (fun _ => w₀) G H =
      (∫⁻ z, ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2) ∂periodMeasure).toReal
        + w₀ * (∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2)) ∂periodMeasure).toReal := by
    unfold weightedEnergy
    rw [eE, split, ENNReal.toReal_add hLH.ne (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hLG).ne,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hw.le]
  have hgn : gradientNorm G = Real.sqrt (∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2)) ∂periodMeasure).toReal := by
    unfold gradientNorm
    rw [eG]
  rw [hgn, hE, le_div_iff₀ (Real.sqrt_pos.2 hw), ← Real.sqrt_mul ENNReal.toReal_nonneg]
  apply Real.sqrt_le_sqrt
  have := (ENNReal.toReal_nonneg : 0 ≤ (∫⁻ z, ENNReal.ofReal (‖secondDerivTrace (H z.1 z.2)‖ ^ 2) ∂periodMeasure).toReal)
  nlinarith

theorem exists_bound_periodic_compact {E : Type*} [NormedAddCommGroup E] {K : ℝ → Space → E}
    (hc : Continuous (fun z : ℝ × Space => K z.1 z.2)) (hp : IsTimePeriodic K) {R : ℝ}
    (hs : ∀ σ y, R < ‖y‖ → K σ y = 0) : ∃ B, 0 ≤ B ∧ ∀ σ y, ‖K σ y‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun σ y => ?_⟩
  rcases lt_or_ge R ‖y‖ with hy | hy
  · rw [hs σ y hy, norm_zero]
    exact le_max_right _ _
  · have hfr : K σ y = K (Int.fract σ) y := by
      have h := (show Function.Periodic (fun s => K s y) 1 from fun s => hp s y).sub_int_mul_eq (x := σ) ⌊σ⌋
      rw [mul_one] at h
      exact h.symm
    rw [hfr]
    have hmem : (Int.fract σ, y) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R :=
      ⟨⟨Int.fract_nonneg σ, (Int.fract_lt_one σ).le⟩, by simpa [Metric.mem_closedBall, dist_zero_right] using hy⟩
    exact (hB _ hmem).trans (le_max_left _ _)

theorem generatorFlux_bound {k : ℕ} {χ : Fin k → ℝ → Space → (Space →L[ℝ] Space)} {pd : PinData k} {C R₀ : ℝ}
    (h : IsPinData χ pd C R₀) (l : Fin k) :
    ∃ B, (∀ σ y, ‖fderiv ℝ (pd.generator l σ) y - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l σ) y)‖
        ≤ B / (1 + ‖y‖) ^ (2 : ℝ)) ∧
      Continuous (fun z : ℝ × Space => fderiv ℝ (pd.generator l z.1) z.2
        - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l z.1) z.2)) := by
  have hsm := h.generator_smooth l
  have hc := slice_fderiv_continuous hsm
  have hper : IsTimePeriodic (fun σ y => fderiv ℝ (pd.generator l σ) y) := by
    intro σ y
    have e : pd.generator l (σ + 1) = pd.generator l σ := funext fun y => h.generator_periodic l σ y
    simp only [e]
  have hzero : ∀ σ y, R₀ < ‖y‖ → fderiv ℝ (pd.generator l σ) y = 0 := by
    intro σ y hy
    have hev : pd.generator l σ =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with x hx
      exact h.generator_support l σ x hx.le
    rw [hev.fderiv_eq]
    simp
  obtain ⟨B₀, hB₀, hB⟩ := exists_bound_periodic_compact hc hper hzero
  have hadjc : Continuous (fun A : Space →L[ℝ] Space => ContinuousLinearMap.adjoint A) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Space) (F := Space)).continuous
  refine ⟨2 * B₀ * (1 + |R₀|) ^ (2 : ℝ), fun σ y => ?_, hc.sub (hadjc.comp hc)⟩
  have hnorm : ‖fderiv ℝ (pd.generator l σ) y - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l σ) y)‖
      ≤ 2 * B₀ := by
    refine (norm_sub_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    linarith [hB σ y]
  have hp : 0 < (1 + ‖y‖) ^ (2 : ℝ) := by positivity
  rcases lt_or_ge R₀ ‖y‖ with hy | hy
  · rw [hzero σ y hy, ContinuousLinearMap.adjoint.map_zero, sub_zero, norm_zero]
    positivity
  · rw [le_div_iff₀ hp]
    have h1 : (1 + ‖y‖) ^ (2 : ℝ) ≤ (1 + |R₀|) ^ (2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith [le_abs_self R₀]) (by norm_num)
    have h2 : 0 ≤ ‖fderiv ℝ (pd.generator l σ) y - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l σ) y)‖ :=
      norm_nonneg _
    exact mul_le_mul hnorm h1 hp.le (by positivity)

end Internal

end AdjointDefect

end Breakdown
