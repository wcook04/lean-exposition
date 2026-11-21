import Breakdown.CertCell.ShapeStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem partial_fderiv_eq {F : ℝ × Space → Space} (hF : ContDiff ℝ 1 F) (σ : ℝ) (y : Space) :
    fderiv ℝ (fun x : Space => F (σ, x)) y = (fderiv ℝ F (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hd : DifferentiableAt ℝ F (σ, y) := (hF.differentiable one_ne_zero) (σ, y)
  exact (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)).fderiv

theorem periodLIntegral_lt_top_of_bound (g : ℝ → Space → ℝ) (C R : ℝ) (hg : ∀ σ y, g σ y ≤ C)
    (hs : ∀ σ y, R < ‖y‖ → g σ y ≤ 0) : periodLIntegral g < ⊤ := by
  unfold periodLIntegral
  have hin : ∀ σ, (∫⁻ y, ENNReal.ofReal (g σ y)) ≤
      ENNReal.ofReal C * volume (Metric.closedBall (0 : Space) R) := by
    intro σ
    calc (∫⁻ y, ENNReal.ofReal (g σ y))
        ≤ ∫⁻ y, (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal C) y := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ Metric.closedBall (0 : Space) R
          · rw [Set.indicator_of_mem hy]
            exact ENNReal.ofReal_le_ofReal (hg σ y)
          · rw [Set.indicator_of_notMem hy]
            have hR : R < ‖y‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
            simp [ENNReal.ofReal_eq_zero.2 (hs σ y hR)]
      _ = ENNReal.ofReal C * volume (Metric.closedBall (0 : Space) R) :=
          lintegral_indicator_const Metric.isClosed_closedBall.measurableSet _
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (g σ y))
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal C * volume (Metric.closedBall (0 : Space) R) :=
        lintegral_mono fun σ => hin σ
    _ = ENNReal.ofReal C * volume (Metric.closedBall (0 : Space) R) * volume (Set.Icc (0 : ℝ) 1) :=
        setLIntegral_const _ _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top) ?_
        simp [Real.volume_Icc]

theorem le_of_le_div_one_add {a B n : ℝ} (ha : 0 ≤ a) (hn : 0 ≤ n) (k : ℕ) (h : a ≤ B / (1 + n) ^ k) :
    a ≤ B := by
  have hpos : 0 < (1 + n) ^ k := pow_pos (by linarith) k
  have hone : 1 ≤ (1 + n) ^ k := one_le_pow₀ (by linarith)
  rw [le_div_iff₀ hpos] at h
  nlinarith

theorem matSq_le (G : Space →L[ℝ] Space) :
    matSq G ≤ ‖G‖ ^ 2 * ∑ i : Fin 3, ‖unitVector i‖ ^ 2 := by
  unfold matSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (G.le_opNorm _) 2

theorem isWeakGradient_of_contDiff {v : Space → Space} (hv : ContDiff ℝ 1 v) :
    IsWeakGradient v (fun y => fderiv ℝ v y) := by
  have hvc : Continuous fun y => fderiv ℝ v y := hv.continuous_fderiv one_ne_zero
  refine ⟨hv.continuous.locallyIntegrable, hvc.locallyIntegrable, fun φ hφ j => ?_⟩
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hφ' : Continuous fun y => fderiv ℝ φ y (unitVector j) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hv' : Continuous fun y => fderiv ℝ v y (unitVector j) := hvc.clm_apply continuous_const
  have hi1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • v y) :=
    (hφ'.smul hv.continuous).integrable_of_hasCompactSupport
      ((hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)).smul_right)
  have hi2 : Integrable (fun y => φ y • fderiv ℝ v y (unitVector j)) :=
    (hφ.1.continuous.smul hv').integrable_of_hasCompactSupport hφ.2.smul_right
  have hi3 : Integrable (fun y => φ y • v y) :=
    (hφ.1.continuous.smul hv.continuous).integrable_of_hasCompactSupport hφ.2.smul_right
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hi1 hi2 hi3 (fun y _ => hφd y) (fun y _ => hvd y)]

theorem actuatorFacts_of_parts (m : ℕ) (S : Finset (ℤ × ℤ)) (f : ℝ → Space → Space)
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (hper : IsTimePeriodic f) (B R : ℝ)
    (hB : ∀ σ y, ‖f σ y‖ ≤ B / (1 + ‖y‖) ∧ ‖fderiv ℝ (f σ) y‖ ≤ B / (1 + ‖y‖) ^ 2)
    (hR : ∀ σ y, R < ‖y‖ → f σ y = 0)
    (hmodes : ∀ ξ σ y, modeVel ξ f σ y ≠ 0 → ∃ ι ∈ S, labelHarmonic m ι = ξ ∨ labelHarmonic m ι = -ξ)
    (hinv : ∀ σ y, f (σ + 1 / 2) (axialRot (Real.pi / m) y) = axialRot (Real.pi / m) (f σ y) ∧
      f σ (flipPoint y) = flipPoint (f σ y)) :
    Instance.ActuatorShapeFacts m S f := by
  have hsec : ∀ σ, ContDiff ℝ 1 (f σ) := fun σ =>
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hgradc : Continuous fun z : ℝ × Space => gradField f z.1 z.2 := by
    have he : (fun z : ℝ × Space => gradField f z.1 z.2) =
        fun z => (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
      funext z
      exact partial_fderiv_eq hF z.1 z.2
    rw [he]
    exact (hF.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have hval : ∀ σ y, ‖f σ y‖ ≤ B := fun σ y =>
    le_of_le_div_one_add (norm_nonneg _) (norm_nonneg y) 1 (by simpa using (hB σ y).1)
  have hgval : ∀ σ y, ‖gradField f σ y‖ ≤ B := fun σ y =>
    le_of_le_div_one_add (norm_nonneg _) (norm_nonneg y) 2 (hB σ y).2
  have hgzero : ∀ σ y, R < ‖y‖ → gradField f σ y = 0 := by
    intro σ y hy
    have hev : f σ =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with x hx
      exact hR σ x hx
    show fderiv ℝ (f σ) y = 0
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  refine ⟨hF.continuous.aestronglyMeasurable, hper, ⟨B, R, fun σ y => ⟨hval σ y, hR σ y⟩⟩, ?_,
    hgradc.aestronglyMeasurable, ?_, ?_, fun σ => isWeakGradient_of_contDiff (hsec σ),
    fun ξ σ y _ hne => hmodes ξ σ y hne, Filter.Eventually.of_forall fun z => hinv z.1 z.2⟩
  · refine periodLIntegral_lt_top_of_bound _ (B ^ 2) R
      (fun σ y => pow_le_pow_left₀ (norm_nonneg _) (hval σ y) 2) (fun σ y hy => ?_)
    rw [hR σ y hy, norm_zero]
    norm_num
  · intro σ y
    have he : f (σ + 1) = f σ := funext fun x => hper σ x
    show fderiv ℝ (f (σ + 1)) y = fderiv ℝ (f σ) y
    rw [he]
  · refine periodLIntegral_lt_top_of_bound _ (B ^ 2 * ∑ i : Fin 3, ‖unitVector i‖ ^ 2) R
      (fun σ y => (matSq_le _).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hgval σ y) 2) (Finset.sum_nonneg fun i _ => by positivity)))
      (fun σ y hy => ?_)
    rw [hgzero σ y hy]
    simp [matSq]

end Internal

open Internal

theorem actuatorShape_of (hsmooth : FieldJointSmooth) (hdecay : FieldDecay) (hsupp : CompactFieldSupport)
    (hclass : FieldClassInvariant) (hmodes : FieldModeFormula) : ActuatorShape := by
  intro P D tb hP hD
  obtain ⟨hF, hper, -, -⟩ := hsmooth P D hP hD.field
  obtain ⟨B, hB⟩ := hdecay P D hP hD.field
  obtain ⟨R, hR⟩ := hsupp P D tb hP hD
  obtain ⟨hflip, hturn, -⟩ := hclass P D hP hD.field
  refine actuatorFacts_of_parts _ _ _ hF hper B R (fun σ y => ⟨(hB σ y).1, (hB σ y).2.1⟩) hR
    (fun ξ σ y hne => ?_) (fun σ y => ⟨hturn σ y, hflip σ y⟩)
  rw [hmodes P D hP hD.field ξ σ y] at hne
  obtain ⟨κ, hκ, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hκD, hκξ⟩ := Finset.mem_filter.1 hκ
  exact ⟨κ.label, Finset.mem_image_of_mem _ hκD, Or.inl hκξ⟩

end GivenShape

end CertCell

end Breakdown
