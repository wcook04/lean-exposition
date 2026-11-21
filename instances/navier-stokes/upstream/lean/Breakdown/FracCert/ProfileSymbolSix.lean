import Breakdown.FracCert.StFreeNiceParts
import Breakdown.Uniqueness.RegPhysAuxDeriv
import Breakdown.FreqTr.GradSixDecay

open scoped ContDiff ENNReal FourierTransform
open MeasureTheory Real

noncomputable section

namespace Breakdown.SteadyCert.Internal.SymbolSix

theorem decay_of_deriv {g : Space → Freq.CSpace} (hg : Integrable g) (hd : Differentiable ℝ g)
    (hg' : Integrable (fderiv ℝ g)) (y : Space) :
    2 * π * ‖y‖ * ‖𝓕⁻ g y‖ ≤ ∫ ξ, ‖fderiv ℝ g ξ‖ := by
  set L : Space →L[ℝ] Space →L[ℝ] ℝ := -innerSL ℝ with hL
  have h := VectorFourier.fourierIntegral_fderiv (L := L) (μ := volume) hg hd hg'
  have h1 := congrArg (fun F => F y y) h
  simp only [VectorFourier.fourierSMulRight_apply] at h1
  have hF : 𝓕⁻ g y = VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ g y :=
    SmoothFlow.Internal.freqTrInv_eq_integral g y
  have hLyy : (-L.flip) y y = ‖y‖ ^ 2 := by
    simp only [hL, neg_apply, ContinuousLinearMap.flip_apply, neg_neg]
    exact real_inner_self_eq_norm_sq y
  rw [hLyy] at h1
  have hle : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ (fderiv ℝ g) y y‖ ≤
      (∫ ξ, ‖fderiv ℝ g ξ‖) * ‖y‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _) (norm_nonneg _))
  rw [h1, ← hF, norm_smul, norm_smul] at hle
  have hc : ‖-(2 * (π : ℂ) * Complex.I)‖ = 2 * π := by
    simp [Complex.norm_I, abs_of_pos pi_pos]
  rw [hc, Real.norm_of_nonneg (by positivity)] at hle
  have hI : 0 ≤ ∫ ξ, ‖fderiv ℝ g ξ‖ := integral_nonneg fun _ => norm_nonneg _
  rcases eq_or_lt_of_le (norm_nonneg y) with h0 | hpos
  · rw [← h0]; simpa using hI
  · have : ‖y‖ * (2 * π * ‖y‖ * ‖𝓕⁻ g y‖) ≤ ‖y‖ * ∫ ξ, ‖fderiv ℝ g ξ‖ := by nlinarith
    exact le_of_mul_le_mul_left this hpos

open Freq.Internal.GradSixDecay

theorem profile_bounds {α : ℝ} {w : Space → Freq.CSpace} (hw : IsProfileSymbol α w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Space, ξ ≠ 0 →
      ‖w ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 4) ∧ ‖fderiv ℝ w ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 5) := by
  obtain ⟨C0, h0⟩ := hw.2.2.1 0
  obtain ⟨C1, h1⟩ := hw.2.2.1 1
  refine ⟨|C0| + |C1|, by positivity, fun ξ hξ => ⟨?_, ?_⟩⟩
  · have := h0 ξ hξ
    rw [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero] at this
    have hp : 0 ≤ ‖ξ‖ ^ (2 * α - 4) := by positivity
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C0, abs_nonneg C1]) hp)
  · have := h1 ξ hξ
    rw [norm_iteratedFDeriv_one, show (2 * α - 4 - ((1 : ℕ) : ℝ)) = 2 * α - 5 by push_cast; ring] at this
    have hp : 0 ≤ ‖ξ‖ ^ (2 * α - 5) := by positivity
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C1, abs_nonneg C0]) hp)

theorem majorant_integrable {α : ℝ} (hα : 1 < α) (ρ : ℝ) :
    Integrable (Set.indicator (Metric.ball (0 : Space) ρ) (fun ξ : Space => ‖ξ‖ ^ (2 * α - 5))) := by
  refine IntegrableOn.integrable_indicator ?_ measurableSet_ball
  refine integrableOn_ball_of_norm_le_rpow (by simp) (α := 5 - 2 * α) (C := 1) ?_ ?_
    (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  · simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
    linarith
  · refine Filter.Eventually.of_forall fun ξ => ?_
    rw [Real.norm_of_nonneg (by positivity), one_mul, neg_sub]

theorem profile_aesm {α : ℝ} {w : Space → Freq.CSpace} (hw : IsProfileSymbol α w) :
    AEStronglyMeasurable w volume := by
  have h1 : AEStronglyMeasurable w (volume.restrict ({0}ᶜ : Set Space)) :=
    hw.1.continuousOn.aestronglyMeasurable isClosed_singleton.isOpen_compl.measurableSet
  rwa [restrict_compl_singleton] at h1

theorem rpow_split {ξ : Space} (hξ : ξ ≠ 0) (α : ℝ) :
    ‖ξ‖ ^ (2 * α - 4) = ‖ξ‖ * ‖ξ‖ ^ (2 * α - 5) := by
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [show 2 * α - 4 = 1 + (2 * α - 5) by ring, Real.rpow_add hpos, Real.rpow_one]

theorem fderiv_cutoff_le {K ε : ℝ} (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hK : ∀ y : Space, ‖fderiv ℝ (cutoff ε) y‖ ≤ K / ε) {ξ : Space} (hξ : ξ ≠ 0) :
    ‖fderiv ℝ (cutoff ε) ξ‖ ≤ 2 * K / ‖ξ‖ := by
  have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have h0 : 0 ≤ 2 * K / ‖ξ‖ := by positivity
  rcases lt_or_ge ‖ξ‖ ε with h1 | h1
  · rw [fderiv_cutoff_eq_zero_of_lt hε h1, norm_zero]; exact h0
  rcases lt_or_ge (2 * ε) ‖ξ‖ with h2 | h2
  · rw [fderiv_cutoff_eq_zero_of_gt hε h2, norm_zero]; exact h0
  refine (hK ξ).trans ?_
  rw [div_le_div_iff₀ hε hpos]
  nlinarith

theorem smooth_part_hasFDerivAt {α : ℝ} {w : Space → Freq.CSpace} (hw : IsProfileSymbol α w)
    {ε : ℝ} {ξ : Space} (hξ : ξ ≠ 0) :
    HasFDerivAt (fun ξ => (1 - cutoff ε ξ) • w ξ)
      ((1 - cutoff ε ξ) • fderiv ℝ w ξ + (-fderiv ℝ (cutoff ε) ξ).smulRight (w ξ)) ξ := by
  have hwd : HasFDerivAt w (fderiv ℝ w ξ) ξ :=
    ((hw.1.contDiffAt (isOpen_ne.mem_nhds hξ)).differentiableAt (by simp)).hasFDerivAt
  have hc : HasFDerivAt (fun ξ => 1 - cutoff ε ξ) (-fderiv ℝ (cutoff ε) ξ) ξ :=
    (((cutoff_contDiff ε).differentiable (by simp) ξ).hasFDerivAt).const_sub 1
  exact hc.smul hwd

theorem smooth_part_zero_near {w : Space → Freq.CSpace} {ε : ℝ} (hε : 0 < ε) {ξ : Space}
    (hξ : ‖ξ‖ < ε) : (fun ξ => (1 - cutoff ε ξ) • w ξ) =ᶠ[nhds ξ] fun _ => 0 := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (show ξ ∈ Metric.ball (0 : Space) ε by simpa using hξ)]
    with z hz
  rw [cutoff_eq_one hε (mem_ball_zero_iff.1 hz).le, sub_self, zero_smul]

theorem smooth_part_differentiable {α : ℝ} {w : Space → Freq.CSpace} (hw : IsProfileSymbol α w)
    {ε : ℝ} (hε : 0 < ε) : Differentiable ℝ (fun ξ => (1 - cutoff ε ξ) • w ξ) := by
  intro ξ
  by_cases hξ : ξ = 0
  · have h : ‖ξ‖ < ε := by rw [hξ, norm_zero]; exact hε
    exact ((hasFDerivAt_const (0 : Freq.CSpace) ξ).congr_of_eventuallyEq
      (smooth_part_zero_near hε h)).differentiableAt
  · exact (smooth_part_hasFDerivAt hw hξ).differentiableAt

theorem smooth_part_fderiv_le {α : ℝ} {w : Space → Freq.CSpace} (hw : IsProfileSymbol α w)
    {R C K ε : ℝ} (hR : ∀ ξ : Space, R < ‖ξ‖ → w ξ = 0) (hC0 : 0 ≤ C)
    (hC : ∀ ξ : Space, ξ ≠ 0 → ‖w ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 4) ∧ ‖fderiv ℝ w ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 5))
    (hK0 : 0 ≤ K) (hε : 0 < ε) (hK : ∀ y : Space, ‖fderiv ℝ (cutoff ε) y‖ ≤ K / ε) (ξ : Space) :
    ‖fderiv ℝ (fun ξ => (1 - cutoff ε ξ) • w ξ) ξ‖ ≤
      (C + 2 * K * C) * Set.indicator (Metric.ball (0 : Space) (|R| + 1))
        (fun ξ : Space => ‖ξ‖ ^ (2 * α - 5)) ξ := by
  have hnn : 0 ≤ (C + 2 * K * C) * Set.indicator (Metric.ball (0 : Space) (|R| + 1))
      (fun ξ : Space => ‖ξ‖ ^ (2 * α - 5)) ξ :=
    mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by positivity) _)
  by_cases hξ : ξ = 0
  · have h : ‖ξ‖ < ε := by rw [hξ, norm_zero]; exact hε
    rw [(smooth_part_zero_near hε h).fderiv_eq]
    simpa using hnn
  by_cases hin : ξ ∈ Metric.ball (0 : Space) (|R| + 1)
  · rw [Set.indicator_of_mem hin, (smooth_part_hasFDerivAt hw hξ).fderiv]
    have hpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hc0 := cutoff_nonneg ε ξ
    have hc1 := cutoff_le_one ε ξ
    have hD := fderiv_cutoff_le hK0 hε hK hξ
    obtain ⟨hw0, hw1⟩ := hC ξ hξ
    rw [rpow_split hξ α] at hw0
    have hp : 0 ≤ ‖ξ‖ ^ (2 * α - 5) := by positivity
    calc ‖(1 - cutoff ε ξ) • fderiv ℝ w ξ + (-fderiv ℝ (cutoff ε) ξ).smulRight (w ξ)‖
        ≤ ‖(1 - cutoff ε ξ) • fderiv ℝ w ξ‖ + ‖(-fderiv ℝ (cutoff ε) ξ).smulRight (w ξ)‖ :=
          norm_add_le _ _
      _ ≤ ‖fderiv ℝ w ξ‖ + ‖fderiv ℝ (cutoff ε) ξ‖ * ‖w ξ‖ := by
          refine add_le_add ?_ (le_of_eq ?_)
          · rw [norm_smul, Real.norm_of_nonneg (by linarith)]
            exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
          · rw [ContinuousLinearMap.norm_smulRight_apply, norm_neg]
      _ ≤ C * ‖ξ‖ ^ (2 * α - 5) + (2 * K / ‖ξ‖) * (C * (‖ξ‖ * ‖ξ‖ ^ (2 * α - 5))) :=
          add_le_add hw1 (mul_le_mul hD hw0 (norm_nonneg _) (by positivity))
      _ = (C + 2 * K * C) * ‖ξ‖ ^ (2 * α - 5) := by
          field_simp
  · rw [Set.indicator_of_notMem hin, mul_zero]
    have hout : R < ‖ξ‖ := by
      have : |R| + 1 ≤ ‖ξ‖ := by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hin
      linarith [le_abs_self R]
    have hev : (fun ξ => (1 - cutoff ε ξ) • w ξ) =ᶠ[nhds ξ] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hout] with z hz
      rw [hR z hz, smul_zero]
    rw [hev.fderiv_eq]
    simp

theorem cut_part_le {α : ℝ} {w : Space → Freq.CSpace}
    {R C ε : ℝ} (hR : ∀ ξ : Space, R < ‖ξ‖ → w ξ = 0) (hC0 : 0 ≤ C)
    (hC : ∀ ξ : Space, ξ ≠ 0 → ‖w ξ‖ ≤ C * ‖ξ‖ ^ (2 * α - 4)) (hε : 0 < ε) {ξ : Space} (hξ : ξ ≠ 0) :
    ‖cutoff ε ξ • w ξ‖ ≤ (2 * ε * C) * Set.indicator (Metric.ball (0 : Space) (|R| + 1))
        (fun ξ : Space => ‖ξ‖ ^ (2 * α - 5)) ξ := by
  have hnn : 0 ≤ (2 * ε * C) * Set.indicator (Metric.ball (0 : Space) (|R| + 1))
      (fun ξ : Space => ‖ξ‖ ^ (2 * α - 5)) ξ :=
    mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by positivity) _)
  by_cases hin : ξ ∈ Metric.ball (0 : Space) (|R| + 1)
  · rw [Set.indicator_of_mem hin]
    rcases le_or_gt (2 * ε) ‖ξ‖ with h2 | h2
    · rw [cutoff_eq_zero hε h2, zero_smul, norm_zero]
      rw [Set.indicator_of_mem hin] at hnn; exact hnn
    have hp : 0 ≤ ‖ξ‖ ^ (2 * α - 5) := by positivity
    have hw0 := hC ξ hξ
    rw [rpow_split hξ α] at hw0
    rw [norm_smul, Real.norm_of_nonneg (cutoff_nonneg ε ξ)]
    calc cutoff ε ξ * ‖w ξ‖ ≤ ‖w ξ‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one ε ξ)
      _ ≤ C * (‖ξ‖ * ‖ξ‖ ^ (2 * α - 5)) := hw0
      _ ≤ C * (2 * ε * ‖ξ‖ ^ (2 * α - 5)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2.le hp) hC0
      _ = 2 * ε * C * ‖ξ‖ ^ (2 * α - 5) := by ring
  · rw [Set.indicator_of_notMem hin, mul_zero]
    have hout : R < ‖ξ‖ := by
      have : |R| + 1 ≤ ‖ξ‖ := by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hin
      linarith [le_abs_self R]
    rw [hR ξ hout, smul_zero, norm_zero]

theorem continuous_two_inner : Continuous (fun p : Space × Space =>
    (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ p.1 p.2) := by
  apply (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).continuous₂

theorem inverseTransform_split {w s g : Space → Freq.CSpace} (hs : Integrable s) (hg : Integrable g)
    (h : w = s + g) (y : Space) : 𝓕⁻ w y = 𝓕⁻ s y + 𝓕⁻ g y := by
  simp only [SmoothFlow.Internal.freqTrInv_eq_integral]
  rw [h, VectorFourier.fourierIntegral_add continuous_fourierChar continuous_two_inner hs hg]
  rfl

theorem norm_inverseTransform_le (a : Space → Freq.CSpace) (y : Space) : ‖𝓕⁻ a y‖ ≤ ∫ ξ, ‖a ξ‖ := by
  rw [SmoothFlow.Internal.freqTrInv_eq_integral]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem transform_decay {α : ℝ} (hα : 1 < α) {w : Space → Freq.CSpace} (hw : IsProfileSymbol α w) :
    ∃ M : ℝ, Integrable w ∧ ∀ y : Space, ‖𝓕⁻ w y‖ ≤ M / (1 + ‖y‖) := by
  obtain ⟨R, hR⟩ := hw.2.1
  obtain ⟨C, hC0, hC⟩ := profile_bounds hw
  obtain ⟨K, hK0, hK⟩ := exists_fderiv_cutoff_le
  set b := Set.indicator (Metric.ball (0 : Space) (|R| + 1)) (fun ξ : Space => ‖ξ‖ ^ (2 * α - 5))
    with hb
  have hbi : Integrable b := majorant_integrable hα _
  have hb0 : ∀ ξ, 0 ≤ b ξ := fun ξ => Set.indicator_nonneg (fun _ _ => by positivity) _
  set I := ∫ ξ, b ξ with hI
  have hI0 : 0 ≤ I := integral_nonneg hb0
  have hae : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hwb : ∀ ξ, ξ ≠ 0 → ‖w ξ‖ ≤ (C * (|R| + 1)) * b ξ := by
    intro ξ hξ
    by_cases hin : ξ ∈ Metric.ball (0 : Space) (|R| + 1)
    · rw [hb, Set.indicator_of_mem hin]
      have h0 := (hC ξ hξ).1
      rw [rpow_split hξ α] at h0
      have hlt : ‖ξ‖ < |R| + 1 := mem_ball_zero_iff.1 hin
      have hp : 0 ≤ ‖ξ‖ ^ (2 * α - 5) := by positivity
      calc ‖w ξ‖ ≤ C * (‖ξ‖ * ‖ξ‖ ^ (2 * α - 5)) := h0
        _ ≤ C * ((|R| + 1) * ‖ξ‖ ^ (2 * α - 5)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlt.le hp) hC0
        _ = _ := by ring
    · rw [hb, Set.indicator_of_notMem hin, mul_zero]
      have : |R| + 1 ≤ ‖ξ‖ := by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hin
      rw [hR ξ (by linarith [le_abs_self R]), norm_zero]
  have hwi : Integrable w := (hbi.const_mul (C * (|R| + 1))).mono' (profile_aesm hw)
    (hae.mono fun ξ hξ => hwb ξ hξ)
  refine ⟨2 * C * I + (∫ ξ, ‖w ξ‖) + (C + 2 * K * C) * I / (2 * π), hwi, fun y => ?_⟩
  have ht : 0 < 1 + ‖y‖ := by positivity
  set ε := 1 / (1 + ‖y‖) with hε
  have hε0 : 0 < ε := by positivity
  have hKε := hK ε hε0
  set s : Space → Freq.CSpace := fun ξ => cutoff ε ξ • w ξ with hs
  set g : Space → Freq.CSpace := fun ξ => (1 - cutoff ε ξ) • w ξ with hg
  have hgd : Differentiable ℝ g := smooth_part_differentiable hw hε0
  have hsi : Integrable s := hwi.norm.mono'
    (((cutoff_contDiff ε).continuous.aestronglyMeasurable).smul (profile_aesm hw))
    (Filter.Eventually.of_forall fun ξ => by
      simp only [hs, norm_smul, Real.norm_of_nonneg (cutoff_nonneg ε ξ)]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one ε ξ))
  have hgw : ∀ ξ, ‖g ξ‖ ≤ ‖w ξ‖ := fun ξ => by
    have h0 := cutoff_nonneg ε ξ
    have h1 := cutoff_le_one ε ξ
    simp only [hg, norm_smul, Real.norm_of_nonneg (show 0 ≤ 1 - cutoff ε ξ by linarith)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have hgi : Integrable g := hwi.norm.mono' hgd.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hgw)
  have hDb : ∀ ξ, ‖fderiv ℝ g ξ‖ ≤ (C + 2 * K * C) * b ξ := fun ξ =>
    smooth_part_fderiv_le hw hR hC0 hC hK0 hε0 hKε ξ
  have hgdi : Integrable (fderiv ℝ g) := (hbi.const_mul (C + 2 * K * C)).mono'
    (measurable_fderiv ℝ g).aestronglyMeasurable (Filter.Eventually.of_forall hDb)
  have h1 : 𝓕⁻ w y = 𝓕⁻ s y + 𝓕⁻ g y := inverseTransform_split hsi hgi (funext fun ξ => by
    simp only [hs, hg, Pi.add_apply]
    rw [← add_smul, add_sub_cancel, one_smul]) y
  have h2 : ‖𝓕⁻ s y‖ ≤ 2 * ε * C * I := by
    refine (norm_inverseTransform_le s y).trans ?_
    rw [hI, ← integral_const_mul]
    exact integral_mono_ae hsi.norm (hbi.const_mul _)
      (hae.mono fun ξ hξ => cut_part_le hR hC0 (fun ξ hξ => (hC ξ hξ).1) hε0 hξ)
  have h3 : ‖𝓕⁻ g y‖ ≤ ∫ ξ, ‖w ξ‖ :=
    (norm_inverseTransform_le g y).trans (integral_mono hgi.norm hwi.norm hgw)
  have h4 : 2 * π * ‖y‖ * ‖𝓕⁻ g y‖ ≤ (C + 2 * K * C) * I := by
    refine (decay_of_deriv hgi hgd hgdi y).trans ?_
    rw [hI, ← integral_const_mul]
    exact integral_mono hgdi.norm (hbi.const_mul _) hDb
  have hεt : ε * (1 + ‖y‖) = 1 := by rw [hε]; field_simp
  have hs' : ‖𝓕⁻ s y‖ * (1 + ‖y‖) ≤ 2 * C * I := by
    calc ‖𝓕⁻ s y‖ * (1 + ‖y‖) ≤ 2 * ε * C * I * (1 + ‖y‖) :=
          mul_le_mul_of_nonneg_right h2 ht.le
      _ = 2 * C * I * (ε * (1 + ‖y‖)) := by ring
      _ = 2 * C * I := by rw [hεt, mul_one]
  have hy' : ‖y‖ * ‖𝓕⁻ g y‖ ≤ (C + 2 * K * C) * I / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [h1, le_div_iff₀ ht]
  calc ‖𝓕⁻ s y + 𝓕⁻ g y‖ * (1 + ‖y‖) ≤ (‖𝓕⁻ s y‖ + ‖𝓕⁻ g y‖) * (1 + ‖y‖) :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) ht.le
    _ = ‖𝓕⁻ s y‖ * (1 + ‖y‖) + ‖𝓕⁻ g y‖ + ‖y‖ * ‖𝓕⁻ g y‖ := by ring
    _ ≤ _ := by linarith

end Breakdown.SteadyCert.Internal.SymbolSix

namespace Breakdown.SteadyCert

theorem profileSymbolSix : ProfileSymbolSixStatement := by
  intro α hα _ w hw
  obtain ⟨M, hwi, hM⟩ := Internal.SymbolSix.transform_decay hα hw
  have hF : 𝓕⁻ w = VectorFourier.fourierIntegral 𝐞 volume
      (-innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).toLinearMap₁₂ w :=
    funext fun y => SmoothFlow.Internal.freqTrInv_eq_integral w y
  have hc : Continuous (𝓕⁻ w) := by
    rw [hF]
    exact VectorFourier.fourierIntegral_continuous continuous_fourierChar
      Internal.SymbolSix.continuous_two_inner hwi
  have hcont : Continuous (Freq.niceField w) := Freq.realVec.continuous.comp hc
  refine Freq.Internal.GradSixDecay.memLp_six_of_le hcont (C := ‖Freq.realVec‖ * M) fun y => ?_
  calc ‖Freq.niceField w y‖ = ‖Freq.realVec (𝓕⁻ w y)‖ := rfl
    _ ≤ ‖Freq.realVec‖ * ‖𝓕⁻ w y‖ := Freq.realVec.le_opNorm _
    _ ≤ ‖Freq.realVec‖ * (M / (1 + ‖y‖)) := mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _)
    _ = ‖Freq.realVec‖ * M / (1 + ‖y‖) := by ring

end Breakdown.SteadyCert
