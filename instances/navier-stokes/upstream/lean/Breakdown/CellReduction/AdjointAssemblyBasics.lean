import Breakdown.CellReduction.AdjointAssemblyStatements

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal

theorem slice_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (σ : ℝ) (y : Space) :
    HasFDerivAt (f σ)
      ((fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y := by
  have h := (hf.differentiable one_ne_zero (σ, y)).hasFDerivAt
  have hi : HasFDerivAt (fun x : Space => ((σ, x) : ℝ × Space)) (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    (hasFDerivAt_const σ y).prodMk (hasFDerivAt_id y)
  exact h.comp y hi

theorem slice_differentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (σ : ℝ) (y : Space) :
    DifferentiableAt ℝ (f σ) y :=
  (slice_hasFDerivAt hf σ y).differentiableAt

theorem slice_fderiv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (σ : ℝ) (y : Space) :
    fderiv ℝ (f σ) y =
      (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
  (slice_hasFDerivAt hf σ y).fderiv

theorem slice_fderiv_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (f z.1) z.2) := by
  have h : (fun z : ℝ × Space => fderiv ℝ (f z.1) z.2) =
      fun z => (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    funext z
    exact slice_fderiv_eq hf z.1 z.2
  rw [h]
  exact (hf.continuous_fderiv one_ne_zero).clm_comp continuous_const

theorem time_hasDerivAt {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (σ : ℝ) (y : Space) :
    HasDerivAt (fun s => f s y) (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (σ, y) (1, 0)) σ := by
  have h := (hf.differentiable one_ne_zero (σ, y)).hasFDerivAt
  have hi : HasDerivAt (fun s : ℝ => ((s, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) σ :=
    (hasDerivAt_id σ).prodMk (hasDerivAt_const σ y)
  exact h.comp_hasDerivAt σ hi

theorem timeDerivative_continuous {f : ℝ → Space → Space}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) :
    Continuous (fun z : ℝ × Space => timeDerivative f z.1 z.2) := by
  have h : (fun z : ℝ × Space => timeDerivative f z.1 z.2) =
      fun z => fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) z (1, 0) := by
    funext z
    exact (time_hasDerivAt hf z.1 z.2).deriv
  rw [h]
  exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem adjointField_mono {ζ : ℝ → Space → Space} {C C' γ : ℝ} (h : IsAdjointField ζ C γ) (hC : C ≤ C') :
    IsAdjointField ζ C' γ := by
  refine ⟨h.rate_gt, h.smooth, h.periodic, h.divergence_free, h.second_weak, fun σ y => ?_, fun σ => ?_,
    h.second_differentiable⟩
  · obtain ⟨h1, h2, h3⟩ := h.decay σ y
    have p1 : 0 < (1 + ‖y‖) ^ γ := by positivity
    have p2 : 0 < (1 + ‖y‖) ^ (γ + 1) := by positivity
    exact ⟨h1.trans (div_le_div_of_nonneg_right hC p1.le), h2.trans (div_le_div_of_nonneg_right hC p1.le),
      h3.trans (div_le_div_of_nonneg_right hC p2.le)⟩
  · filter_upwards [h.second_decay σ] with y hy
    have p1 : 0 < (1 + ‖y‖) ^ γ := by positivity
    exact hy.trans (div_le_div_of_nonneg_right hC p1.le)

theorem curlPotential_mono {ζ A : ℝ → Space → Space} {C C' β : ℝ} (h : IsCurlPotential ζ A C β) (hC : C ≤ C') :
    IsCurlPotential ζ A C' β := by
  refine ⟨h.rate_gt, h.smooth, h.periodic, h.curl_eq, fun σ y => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.decay σ y
  have p1 : 0 < (1 + ‖y‖) ^ β := by positivity
  have p2 : 0 < (1 + ‖y‖) ^ (β + 1) := by positivity
  exact ⟨h1.trans (div_le_div_of_nonneg_right hC p1.le), h2.trans (div_le_div_of_nonneg_right hC p1.le),
    h3.trans (div_le_div_of_nonneg_right hC p2.le)⟩

theorem residualField_mono {T : ℝ → Space → Space} {K : ℝ → Space → (Space →L[ℝ] Space)} {C C' γ : ℝ}
    (h : IsResidualField T K C γ) (hC : C ≤ C') : IsResidualField T K C' γ := by
  refine ⟨h.rate_gt, h.residual_measurable, h.flux_measurable, h.flux_weak, fun σ y => ?_, fun σ => ?_⟩
  · obtain ⟨h1, h2⟩ := h.decay σ y
    have p1 : 0 < (1 + ‖y‖) ^ γ := by positivity
    have p2 : 0 < (1 + ‖y‖) ^ (γ + 1) := by positivity
    exact ⟨h1.trans (div_le_div_of_nonneg_right hC p1.le), h2.trans (div_le_div_of_nonneg_right hC p2.le)⟩
  · filter_upwards [h.flux_div_decay σ] with y hy
    have p1 : 0 < (1 + ‖y‖) ^ γ := by positivity
    exact hy.trans (div_le_div_of_nonneg_right hC p1.le)

theorem potentialData_mono {p : PotentialData} {C C' : ℝ} (h : IsPotentialData p C) (hC : C ≤ C') :
    IsPotentialData p C' := by
  refine ⟨h.theta_smooth, h.phi_smooth, h.flux_measurable, h.pressure_measurable, h.theta_weak, h.phi_weak,
    h.flux_weak, h.pressure_weak, fun σ y => ?_, fun σ => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.value_decay σ y
    have q1 : 0 < (1 + ‖y‖) ^ 2 := by positivity
    have q2 : 0 < (1 + ‖y‖) ^ 3 := by positivity
    have q3 : 0 < 1 + ‖y‖ := by positivity
    exact ⟨h1.trans (div_le_div_of_nonneg_right hC q1.le), h2.trans (div_le_div_of_nonneg_right hC q2.le),
      h3.trans (div_le_div_of_nonneg_right hC q3.le), h4.trans (div_le_div_of_nonneg_right hC q1.le),
      h5.trans (div_le_div_of_nonneg_right hC q1.le), h6.trans (div_le_div_of_nonneg_right hC q1.le)⟩
  · filter_upwards [h.second_decay σ] with y hy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hy
    have q1 : 0 < (1 + ‖y‖) ^ 2 := by positivity
    have q2 : 0 < (1 + ‖y‖) ^ 3 := by positivity
    have q4 : 0 < (1 + ‖y‖) ^ 4 := by positivity
    exact ⟨h1.trans (div_le_div_of_nonneg_right hC q4.le), h2.trans (div_le_div_of_nonneg_right hC q2.le),
      h3.trans (div_le_div_of_nonneg_right hC q1.le), h4.trans hC, h5.trans hC⟩

theorem flowPiece_nonneg {W : ℝ → Space → Space} {D : ℝ} (h : IsFlowPiece W D) : 0 ≤ D :=
  (norm_nonneg _).trans (h.decay 0 0).1

theorem flowPiece_mono {W : ℝ → Space → Space} {D D' : ℝ} (h : IsFlowPiece W D) (hD : D ≤ D') :
    IsFlowPiece W D' := by
  refine ⟨h.smooth, h.periodic, h.divergence_free, fun σ y => ?_⟩
  obtain ⟨h1, h2⟩ := h.decay σ y
  have q : 0 < 1 + ‖y‖ := by positivity
  exact ⟨h1.trans hD, h2.trans (div_le_div_of_nonneg_right hD q.le)⟩

theorem flowPiece_congr {W W' : ℝ → Space → Space} {D : ℝ} (h : IsFlowPiece W D)
    (he : ∀ σ y, W σ y = W' σ y) : IsFlowPiece W' D := by
  have : W = W' := funext fun σ => funext fun y => he σ y
  exact this ▸ h

theorem flowPiece_zero : IsFlowPiece (fun _ _ => 0) 0 := by
  refine ⟨contDiff_const, fun _ _ => rfl, fun σ y => ?_, fun σ y => ?_⟩
  · simp [divergenceAt]
  · simp

theorem flowPiece_add {A B : ℝ → Space → Space} {D₁ D₂ : ℝ} (hA : IsFlowPiece A D₁) (hB : IsFlowPiece B D₂) :
    IsFlowPiece (fun σ y => A σ y + B σ y) (D₁ + D₂) := by
  refine ⟨hA.smooth.add hB.smooth, fun σ y => by simp [hA.periodic σ y, hB.periodic σ y], fun σ y => ?_,
    fun σ y => ?_⟩
  · have ha := slice_differentiableAt hA.smooth σ y
    have hb := slice_differentiableAt hB.smooth σ y
    have e : divergenceAt (fun y => A σ y + B σ y) y = divergenceAt (A σ) y + divergenceAt (B σ) y := by
      unfold divergenceAt
      rw [(show fderiv ℝ (fun y => A σ y + B σ y) y = fderiv ℝ (A σ) y + fderiv ℝ (B σ) y from
        (ha.hasFDerivAt.add hb.hasFDerivAt).fderiv), ← Finset.sum_add_distrib]
      rfl
    rw [e, hA.divergence_free, hB.divergence_free, add_zero]
  · have ha := slice_differentiableAt hA.smooth σ y
    have hb := slice_differentiableAt hB.smooth σ y
    obtain ⟨a1, a2⟩ := hA.decay σ y
    obtain ⟨b1, b2⟩ := hB.decay σ y
    refine ⟨(norm_add_le _ _).trans (add_le_add a1 b1), ?_⟩
    rw [(show fderiv ℝ (fun y => A σ y + B σ y) y = fderiv ℝ (A σ) y + fderiv ℝ (B σ) y from
        (ha.hasFDerivAt.add hb.hasFDerivAt).fderiv), add_div]
    exact (norm_add_le _ _).trans (add_le_add a2 b2)

theorem flowPiece_smul {A : ℝ → Space → Space} {D : ℝ} (hA : IsFlowPiece A D) (c : ℝ) :
    IsFlowPiece (fun σ y => c • A σ y) (|c| * D) := by
  refine ⟨hA.smooth.const_smul c, fun σ y => by simp [hA.periodic σ y], fun σ y => ?_, fun σ y => ?_⟩
  · have ha := slice_differentiableAt hA.smooth σ y
    have e : divergenceAt (fun y => c • A σ y) y = c * divergenceAt (A σ) y := by
      unfold divergenceAt
      rw [(show fderiv ℝ (fun y => c • A σ y) y = c • fderiv ℝ (A σ) y from
        (ha.hasFDerivAt.const_smul c).fderiv), Finset.mul_sum]
      rfl
    rw [e, hA.divergence_free, mul_zero]
  · have ha := slice_differentiableAt hA.smooth σ y
    obtain ⟨a1, a2⟩ := hA.decay σ y
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left a1 (abs_nonneg c)
    · rw [(show fderiv ℝ (fun y => c • A σ y) y = c • fderiv ℝ (A σ) y from
        (ha.hasFDerivAt.const_smul c).fderiv), norm_smul, Real.norm_eq_abs, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left a2 (abs_nonneg c)

theorem flowPiece_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → ℝ → Space → Space) {D : ℝ}
    (hf : ∀ i ∈ s, IsFlowPiece (f i) D) :
    IsFlowPiece (fun σ y => ∑ i ∈ s, c i • f i σ y) ((∑ i ∈ s, |c i|) * D) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using flowPiece_zero
  | insert a s ha ih =>
    have h1 := flowPiece_smul (hf a (Finset.mem_insert_self a s)) (c a)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine flowPiece_congr (flowPiece_mono (flowPiece_add h1 h2) (le_of_eq ?_)) (fun σ y => ?_)
    · rw [Finset.sum_insert ha, add_mul]
    · rw [Finset.sum_insert ha]

end Internal

end AdjointDefect

end Breakdown
