import Breakdown.Profile.StatementsPhysical

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private def similarityDeriv (W : ℝ → Space → Space) (s : ℝ) (y : Space) : Space :=
  deriv (fun σ => W σ y) s + (1 / 2 : ℝ) • W s y + (1 / 2 : ℝ) • fderiv ℝ (W s) y y

private lemma slice_contDiff {W : ℝ → Space → Space}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) (s : ℝ) : ContDiff ℝ ∞ (W s) :=
  hW.comp (contDiff_const.prodMk contDiff_id)

private lemma physicalField_continuous {W : ℝ → Space → Space}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) (s₀ τ : ℝ) :
    Continuous (physicalField W s₀ τ) := by
  have hc := (slice_contDiff hW (physicalTime s₀ τ)).continuous
  unfold physicalField dilateField
  exact (hc.comp (continuous_id.const_smul (Real.sqrt ((1 - τ)⁻¹)))).const_smul
    (Real.sqrt ((1 - τ)⁻¹))

private lemma physicalScale_le {t τ : ℝ} (h : τ ≤ t) (ht : t < 1) :
    physicalScale τ ≤ physicalScale t := by
  have h1 : (0 : ℝ) < 1 - t := by linarith
  have h2 : 1 - t ≤ 1 - τ := by linarith
  exact Real.sqrt_le_sqrt (inv_anti₀ h1 h2)

private lemma physicalScale_nonneg (t : ℝ) : 0 ≤ physicalScale t := Real.sqrt_nonneg _

private lemma similarityDeriv_measurable {W : ℝ → Space → Space}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) (s : ℝ) :
    Measurable (similarityDeriv W s) := by
  have hc : Continuous (fun p : Space × ℝ => W p.2 p.1) :=
    hW.continuous.comp continuous_swap
  have h2 := measurable_deriv_with_param (f := fun (y : Space) (σ : ℝ) => W σ y) hc
  have hA : Measurable (fun y : Space => deriv (fun σ => W σ y) s) :=
    h2.comp (measurable_id.prodMk measurable_const)
  have hWs := slice_contDiff hW s
  have h3 : Continuous (fderiv ℝ (W s)) := hWs.continuous_fderiv (by simp)
  have hB : Continuous (fun y => (1 / 2 : ℝ) • W s y) := by
    have := hWs.continuous
    fun_prop
  have hC : Continuous (fun y => (1 / 2 : ℝ) • fderiv ℝ (W s) y y) := by
    have := h3.clm_apply continuous_id
    fun_prop
  show Measurable (fun y => deriv (fun σ => W σ y) s + (1 / 2 : ℝ) • W s y
    + (1 / 2 : ℝ) • fderiv ℝ (W s) y y)
  exact (hA.add hB.measurable).add hC.measurable

private lemma div_cube_le_abs (K : ℝ) (y : Space) : K / (1 + ‖y‖) ^ 3 ≤ |K| := by
  have h1 : (1 : ℝ) ≤ (1 + ‖y‖) ^ 3 := one_le_pow₀ (by linarith [norm_nonneg y])
  calc K / (1 + ‖y‖) ^ 3 ≤ |K| / (1 + ‖y‖) ^ 3 :=
        div_le_div_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ |K| := div_le_self (abs_nonneg K) h1

theorem physicalPairingDeriv_holds (htime : PhysicalTimeDeriv) (hmom : PhysicalMomentum)
    (hbound : SimilarityDerivBound) : PhysicalPairingDeriv := by
  intro W q C h s₀ t ht φ hφ
  obtain ⟨K, hK⟩ := hbound W q C h
  have hD : ∀ τ, τ < 1 → ∀ x, HasDerivAt (fun τ' => physicalField W s₀ τ' x)
      (physicalScale τ ^ 3 • similarityDeriv W (physicalTime s₀ τ) (physicalScale τ • x)) τ :=
    fun τ hτ x => htime W h.smooth s₀ τ hτ x
  have htT : t < (t + 1) / 2 := by linarith
  have hT1 : (t + 1) / 2 < 1 := by linarith
  have hs : Iio ((t + 1) / 2) ∈ nhds t := Iio_mem_nhds htT
  have hφc : Continuous φ := hφ.1.continuous
  have hφi : Integrable (fun x => ‖φ x‖) := (hφc.integrable_of_hasCompactSupport hφ.2.1).norm
  have hmeas : ∀ᶠ τ in nhds t, AEStronglyMeasurable
      (fun x => inner ℝ (physicalField W s₀ τ x) (φ x)) volume :=
    Filter.Eventually.of_forall fun τ =>
      ((physicalField_continuous h.smooth s₀ τ).inner hφc).aestronglyMeasurable
  have hint : Integrable (fun x => inner ℝ (physicalField W s₀ t x) (φ x)) := by
    refine ((physicalField_continuous h.smooth s₀ t).inner hφc).integrable_of_hasCompactSupport
      (hφ.2.1.mono fun x hx => ?_)
    rw [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by simp [h0])
  have hmeas' : AEStronglyMeasurable (fun x => inner ℝ
      (physicalScale t ^ 3 • similarityDeriv W (physicalTime s₀ t) (physicalScale t • x))
      (φ x)) volume := by
    have hm : Measurable (fun x : Space =>
        physicalScale t ^ 3 • similarityDeriv W (physicalTime s₀ t) (physicalScale t • x)) := by
      have := similarityDeriv_measurable h.smooth (physicalTime s₀ t)
      fun_prop
    exact (hm.inner hφc.measurable).aestronglyMeasurable
  have hbd : ∀ᵐ x ∂(volume : Measure Space), ∀ τ ∈ Iio ((t + 1) / 2),
      ‖inner ℝ (physicalScale τ ^ 3 • similarityDeriv W (physicalTime s₀ τ) (physicalScale τ • x))
        (φ x)‖ ≤ physicalScale ((t + 1) / 2) ^ 3 * |K| * ‖φ x‖ := by
    refine Filter.Eventually.of_forall fun x τ hτ => ?_
    have hτ' : τ < (t + 1) / 2 := hτ
    have hsc : physicalScale τ ^ 3 ≤ physicalScale ((t + 1) / 2) ^ 3 :=
      pow_le_pow_left₀ (physicalScale_nonneg _) (physicalScale_le hτ'.le hT1) 3
    have hG : ‖similarityDeriv W (physicalTime s₀ τ) (physicalScale τ • x)‖ ≤ |K| :=
      (hK _ _).trans (div_cube_le_abs K _)
    calc _ ≤ ‖physicalScale τ ^ 3 • similarityDeriv W (physicalTime s₀ τ) (physicalScale τ • x)‖
            * ‖φ x‖ := norm_inner_le_norm _ _
      _ ≤ physicalScale ((t + 1) / 2) ^ 3 * |K| * ‖φ x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hp : (0 : ℝ) ≤ physicalScale τ ^ 3 := pow_nonneg (physicalScale_nonneg _) 3
        have hp' : (0 : ℝ) ≤ physicalScale ((t + 1) / 2) ^ 3 :=
          pow_nonneg (physicalScale_nonneg _) 3
        rw [norm_smul, Real.norm_of_nonneg hp]
        exact mul_le_mul hsc hG (norm_nonneg _) hp'
  have hdiff : ∀ᵐ x ∂(volume : Measure Space), ∀ τ ∈ Iio ((t + 1) / 2),
      HasDerivAt (fun τ' => inner ℝ (physicalField W s₀ τ' x) (φ x))
        (inner ℝ (physicalScale τ ^ 3 • similarityDeriv W (physicalTime s₀ τ)
          (physicalScale τ • x)) (φ x)) τ := by
    refine Filter.Eventually.of_forall fun x τ hτ => ?_
    have hτ' : τ < (t + 1) / 2 := hτ
    have h2 := (hD τ (hτ'.trans hT1) x).inner ℝ (hasDerivAt_const τ (φ x))
    rw [inner_zero_right, zero_add] at h2
    exact h2
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint hmeas' hbd
    (hφi.const_mul _) hdiff
  have heq : (fun x => inner ℝ (physicalScale t ^ 3 • similarityDeriv W (physicalTime s₀ t)
      (physicalScale t • x)) (φ x)) = fun x => inner ℝ (sumSecondPartialsAt (physicalField W s₀ t) x
        - advectionAt (physicalField W s₀ t) x - gradientAt (physicalPressure q s₀ t) x) (φ x) :=
    funext fun x => by rw [(hD t ht x).unique (hmom W q C h s₀ t ht x)]
  rw [heq] at hderiv
  exact hderiv

end Breakdown
