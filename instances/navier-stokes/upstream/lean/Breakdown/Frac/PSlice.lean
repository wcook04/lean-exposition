import Breakdown.Frac.PAxial
import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.VelocityRotate

open MeasureTheory Set Real Filter
open scoped ContDiff Topology

noncomputable section

namespace Breakdown

namespace FracInternal

namespace SliceBounds

theorem norm_iteratedFDeriv_pushForward (R : Space ≃ₗᵢ[ℝ] Space) (f : Space → Space) (y : Space)
    (j : ℕ) : ‖iteratedFDeriv ℝ j (pushForward R f) y‖ = ‖iteratedFDeriv ℝ j f (R.symm y)‖ := by
  have e : pushForward R f = R ∘ (f ∘ R.symm) := rfl
  rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]

theorem rpow_le_inv_pow {t r : ℝ} (n : ℕ) (ht : 1 ≤ t) (hr : (n : ℝ) ≤ r) :
    t ^ (-r) ≤ 1 / t ^ n := by
  have h := Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg hr)
  have h2 : t ^ (-(n : ℝ)) = 1 / t ^ n := by
    rw [Real.rpow_neg (by linarith), Real.rpow_natCast, one_div]
  exact h.trans h2.le

theorem profile_bounds {α a : ℝ} {U : Space → Space} {P : Space → ℝ} (hα : 1 < α)
    (h : IsRotatingProfile α a 1 U P) :
    ∃ C : ℝ, ∀ y, ‖U y‖ ≤ C / (1 + ‖y‖) ∧ ‖fderiv ℝ U y‖ ≤ C / (1 + ‖y‖) ^ 2 := by
  obtain ⟨C0, h0⟩ := h.decay 0
  obtain ⟨C1, h1⟩ := h.decay 1
  refine ⟨max C0 0 + max C1 0, fun y => ⟨?_, ?_⟩⟩
  · have ht : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have hb := (h0 y).1
    rw [norm_iteratedFDeriv_zero] at hb
    have hr := rpow_le_inv_pow 1 ht (r := 2 * α - 1 + ((0 : ℕ) : ℝ)) (by push_cast; linarith)
    have hp : 0 ≤ (1 + ‖y‖) ^ (-(2 * α - 1 + ((0 : ℕ) : ℝ))) := Real.rpow_nonneg (by linarith) _
    calc ‖U y‖ ≤ C0 * (1 + ‖y‖) ^ (-(2 * α - 1 + ((0 : ℕ) : ℝ))) := hb
      _ ≤ max C0 0 * (1 + ‖y‖) ^ (-(2 * α - 1 + ((0 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hp
      _ ≤ max C0 0 * (1 / (1 + ‖y‖) ^ 1) := mul_le_mul_of_nonneg_left hr (le_max_right _ _)
      _ ≤ (max C0 0 + max C1 0) / (1 + ‖y‖) := by
          rw [pow_one, mul_one_div]
          gcongr
          linarith [le_max_right C1 0]
  · have ht : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have hb := (h1 y).1
    rw [norm_iteratedFDeriv_one] at hb
    have hr := rpow_le_inv_pow 2 ht (r := 2 * α - 1 + ((1 : ℕ) : ℝ)) (by push_cast; linarith)
    have hp : 0 ≤ (1 + ‖y‖) ^ (-(2 * α - 1 + ((1 : ℕ) : ℝ))) := Real.rpow_nonneg (by linarith) _
    calc ‖fderiv ℝ U y‖ ≤ C1 * (1 + ‖y‖) ^ (-(2 * α - 1 + ((1 : ℕ) : ℝ))) := hb
      _ ≤ max C1 0 * (1 + ‖y‖) ^ (-(2 * α - 1 + ((1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hp
      _ ≤ max C1 0 * (1 / (1 + ‖y‖) ^ 2) := mul_le_mul_of_nonneg_left hr (le_max_right _ _)
      _ ≤ (max C0 0 + max C1 0) / (1 + ‖y‖) ^ 2 := by
          rw [mul_one_div]
          gcongr
          linarith [le_max_right C0 0]

theorem slice_bounds {α a : ℝ} {U : Space → Space} {P : Space → ℝ} (hα : 1 < α)
    (h : IsRotatingProfile α a 1 U P) :
    ∃ C : ℝ, ∀ s y, ‖rotatingSlice a U s y‖ ≤ C / (1 + ‖y‖) ∧
      ‖fderiv ℝ (rotatingSlice a U s) y‖ ≤ C / (1 + ‖y‖) ^ 2 := by
  obtain ⟨C, hC⟩ := profile_bounds hα h
  refine ⟨C, fun s y => ?_⟩
  simp only [rotatingSlice]
  have hn : ‖(axialRotation (-(a * s))).symm y‖ = ‖y‖ := (axialRotation (-(a * s))).symm.norm_map y
  have e0 := norm_iteratedFDeriv_pushForward (axialRotation (-(a * s))) U y 0
  have e1 := norm_iteratedFDeriv_pushForward (axialRotation (-(a * s))) U y 1
  rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero] at e0
  rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at e1
  have hb := hC ((axialRotation (-(a * s))).symm y)
  rw [hn] at hb
  rw [e0, e1]
  exact hb

theorem fderiv_pushForward_apply (R : Space ≃ₗᵢ[ℝ] Space) {W : Space → Space}
    (hW : Differentiable ℝ W) (y v : Space) :
    fderiv ℝ (pushForward R W) y v = R (fderiv ℝ W (R.symm y) (R.symm v)) := by
  have h1 : HasFDerivAt (fun y => R.symm y)
      ((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space) y :=
    (R.symm.toContinuousLinearEquiv).hasFDerivAt
  have h2 := (hW (R.symm y)).hasFDerivAt.comp y h1
  have h3 := ((R.toContinuousLinearEquiv : Space ≃L[ℝ] Space).hasFDerivAt
    (x := W (R.symm y))).comp y h2
  have h4 : HasFDerivAt (pushForward R W)
      (((R.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space).comp
        ((fderiv ℝ W (R.symm y)).comp
          ((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space))) y := h3
  rw [h4.fderiv]
  rfl

theorem divergence_pushForward (R : Space ≃ₗᵢ[ℝ] Space) {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hd : ∀ y, divergenceAt f y = 0) (y : Space) :
    divergenceAt (pushForward R f) y = 0 := by
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  unfold divergenceAt
  simp only [fderiv_pushForward_apply R hdf]
  rw [Freq.Internal.VelocityRotate.sum_rot R (fderiv ℝ f (R.symm y))]
  exact hd _

theorem slice_decayField {α a : ℝ} {U : Space → Space} {P : Space → ℝ} (hα : 1 < α)
    (h : IsRotatingProfile α a 1 U P) (s : ℝ) : IsDecayField (rotatingSlice a U s) := by
  obtain ⟨C, hC⟩ := slice_bounds hα h
  refine ⟨?_, fun y => ?_, C, hC s⟩
  · exact (axialRotation (-(a * s))).contDiff.comp (h.smooth.comp (axialRotation (-(a * s))).symm.contDiff)
  · exact divergence_pushForward _ h.smooth h.div y

theorem decay_sub {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g) :
    IsDecayField (f - g) := by
  obtain ⟨hfs, hfd, Cf, hCf⟩ := hf
  obtain ⟨hgs, hgd, Cg, hCg⟩ := hg
  have hdf : Differentiable ℝ f := hfs.differentiable (by simp)
  have hdg : Differentiable ℝ g := hgs.differentiable (by simp)
  refine ⟨hfs.sub hgs, fun y => ?_, Cf + Cg, fun y => ⟨?_, ?_⟩⟩
  · have h1 := hfd y
    have h2 := hgd y
    unfold divergenceAt at h1 h2 ⊢
    rw [fderiv_sub (hdf y) (hdg y)]
    simp only [sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib]
    rw [h1, h2, sub_zero]
  · calc ‖(f - g) y‖ ≤ ‖f y‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ Cf / (1 + ‖y‖) + Cg / (1 + ‖y‖) := add_le_add (hCf y).1 (hCg y).1
      _ = (Cf + Cg) / (1 + ‖y‖) := (add_div _ _ _).symm
  · rw [fderiv_sub (hdf y) (hdg y)]
    calc ‖fderiv ℝ f y - fderiv ℝ g y‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ g y‖ := norm_sub_le _ _
      _ ≤ Cf / (1 + ‖y‖) ^ 2 + Cg / (1 + ‖y‖) ^ 2 := add_le_add (hCf y).2 (hCg y).2
      _ = (Cf + Cg) / (1 + ‖y‖) ^ 2 := (add_div _ _ _).symm

theorem rot_apply_continuous (h1 : AxialRotationSpec) {c : ℝ → ℝ} {g : ℝ → Space}
    (hc : Continuous c) (hg : Continuous g) : Continuous (fun s => axialRotation (c s) (g s)) := by
  have hL : Continuous (fun θ : ℝ => ((axialRotation θ).toContinuousLinearEquiv : Space →L[ℝ] Space)) :=
    continuous_clm_apply.2 fun y => by simpa using h1.2.2.2.2.1 y
  have := (hL.comp hc).clm_apply hg
  simpa using this

theorem slice_fderiv_continuous (h1 : AxialRotationSpec) {U : Space → Space}
    (hU : ContDiff ℝ ∞ U) (a : ℝ) (y v : Space) :
    Continuous (fun s => fderiv ℝ (rotatingSlice a U s) y v) := by
  have hdU : Differentiable ℝ U := hU.differentiable (by simp)
  have e : (fun s => fderiv ℝ (rotatingSlice a U s) y v) = fun s =>
      axialRotation (-(a * s)) (fderiv ℝ U (axialRotation (a * s) y) (axialRotation (a * s) v)) := by
    funext s
    simp only [rotatingSlice]
    rw [fderiv_pushForward_apply _ hdU, h1.2.2.2.1, neg_neg]
  rw [e]
  have hc : Continuous (fun s : ℝ => a * s) := continuous_const.mul continuous_id
  have cy := rot_apply_continuous h1 hc (continuous_const (y := y))
  have cv := rot_apply_continuous h1 hc (continuous_const (y := v))
  have c2 : Continuous (fun s => fderiv ℝ U (axialRotation (a * s) y)) :=
    (hU.continuous_fderiv (by simp)).comp cy
  exact rot_apply_continuous h1 hc.neg (c2.clm_apply cv)

end SliceBounds

end FracInternal

open FracInternal.SliceBounds in
theorem rotatingSliceDecay : RotatingSliceDecay := by
  intro α hα _ a U P h s
  refine ⟨slice_decayField hα h s, fun j _ => ?_⟩
  obtain ⟨Cj, hj⟩ := h.decay j
  refine ⟨max Cj 0, fun y => ?_⟩
  simp only [rotatingSlice]
  rw [norm_iteratedFDeriv_pushForward]
  set z := (axialRotation (-(a * s))).symm y
  have hb := (hj z).1
  have ht : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hr := Real.rpow_le_one_of_one_le_of_nonpos ht (z := -(2 * α - 1 + (j : ℝ))) (by linarith)
  have hp := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ‖z‖) (-(2 * α - 1 + (j : ℝ)))
  calc ‖iteratedFDeriv ℝ j U z‖ ≤ Cj * (1 + ‖z‖) ^ (-(2 * α - 1 + (j : ℝ))) := hb
    _ ≤ max Cj 0 * (1 + ‖z‖) ^ (-(2 * α - 1 + (j : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hp
    _ ≤ max Cj 0 * 1 := mul_le_mul_of_nonneg_left hr (le_max_right _ _)
    _ = max Cj 0 := mul_one _

open FracInternal.SliceBounds in
theorem rotatingSliceContinuous (h1 : AxialRotationSpec) : RotatingSliceContinuous := by
  intro α hα _ a U P h
  have hEN := Freq.embedNormLinear_holds.1
  have hEL := Freq.embedNormLinear_holds.2
  obtain ⟨C, hC⟩ := slice_bounds hα h
  have hD := fun s => slice_decayField hα h s
  have hU := h.smooth
  have hdiff : ∀ s, Differentiable ℝ (rotatingSlice a U s) :=
    fun s => (hD s).1.differentiable (by simp)
  rw [continuous_iff_continuousAt]
  intro s₀
  have hsq : ∀ s, ‖Freq.embedX (rotatingSlice a U s) - Freq.embedX (rotatingSlice a U s₀)‖ ^ 2 =
      ∫ y, ∑ i : Fin 3,
        ‖fderiv ℝ (rotatingSlice a U s - rotatingSlice a U s₀) y (unitVector i)‖ ^ 2 := by
    intro s
    rw [← hEL.2.1 _ _ (hD s) (hD s₀)]
    exact hEN _ (decay_sub (hD s) (hD s₀))
  have hbd : ∀ s y (i : Fin 3),
      ‖fderiv ℝ (rotatingSlice a U s - rotatingSlice a U s₀) y (unitVector i)‖ ^ 2 ≤
        4 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
    intro s y i
    rw [fderiv_sub (hdiff s y) (hdiff s₀ y), sub_apply]
    have hb : ∀ t, ‖fderiv ℝ (rotatingSlice a U t) y (unitVector i)‖ ≤ C / (1 + ‖y‖) ^ 2 := by
      intro t
      calc ‖fderiv ℝ (rotatingSlice a U t) y (unitVector i)‖
          ≤ ‖fderiv ℝ (rotatingSlice a U t) y‖ * ‖unitVector i‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ (rotatingSlice a U t) y‖ := by simp [unitVector]
        _ ≤ C / (1 + ‖y‖) ^ 2 := (hC t y).2
    have hpos : 0 < 1 + ‖y‖ := by positivity
    have h2 : ‖fderiv ℝ (rotatingSlice a U s) y (unitVector i) -
        fderiv ℝ (rotatingSlice a U s₀) y (unitVector i)‖ ≤ 2 * (C / (1 + ‖y‖) ^ 2) := by
      calc _ ≤ ‖fderiv ℝ (rotatingSlice a U s) y (unitVector i)‖ +
            ‖fderiv ℝ (rotatingSlice a U s₀) y (unitVector i)‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hb s, hb s₀]
    have h3 : (1 + ‖y‖) ^ (-(4 : ℝ)) = 1 / (1 + ‖y‖) ^ 4 := by
      rw [Real.rpow_neg hpos.le, one_div]
      norm_cast
    calc _ ≤ (2 * (C / (1 + ‖y‖) ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = 4 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
        rw [h3]
        field_simp
        ring
  have key : ContinuousAt (fun s => ∫ y, ∑ i : Fin 3,
      ‖fderiv ℝ (rotatingSlice a U s - rotatingSlice a U s₀) y (unitVector i)‖ ^ 2) s₀ := by
    apply continuousAt_of_dominated (bound := fun y => 12 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)))
    · refine Filter.Eventually.of_forall (fun s => ?_)
      apply Continuous.aestronglyMeasurable
      have hc : Continuous (fderiv ℝ (rotatingSlice a U s - rotatingSlice a U s₀)) :=
        ((hD s).1.sub (hD s₀).1).continuous_fderiv (by simp)
      exact continuous_finsetSum _ (fun i _ =>
        (((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp hc).norm).pow 2)
    · refine Filter.Eventually.of_forall (fun s => Filter.Eventually.of_forall (fun y => ?_))
      rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => by positivity))]
      calc _ ≤ ∑ _i : Fin 3, 4 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) :=
            Finset.sum_le_sum (fun i _ => hbd s y i)
        _ = _ := by simp; ring
    · exact (integrable_one_add_norm (by simp; norm_num)).const_mul _
    · refine Filter.Eventually.of_forall (fun y => ?_)
      have e : (fun s => ∑ i : Fin 3,
          ‖fderiv ℝ (rotatingSlice a U s - rotatingSlice a U s₀) y (unitVector i)‖ ^ 2) =
          fun s => ∑ i : Fin 3, ‖fderiv ℝ (rotatingSlice a U s) y (unitVector i) -
            fderiv ℝ (rotatingSlice a U s₀) y (unitVector i)‖ ^ 2 := by
        funext s
        rw [fderiv_sub (hdiff s y) (hdiff s₀ y)]
        rfl
      rw [e]
      exact (continuous_finsetSum _ (fun i _ =>
        (((slice_fderiv_continuous h1 hU a y (unitVector i)).sub continuous_const).norm).pow
          2)).continuousAt
  have h0 : (∫ y, ∑ i : Fin 3,
      ‖fderiv ℝ (rotatingSlice a U s₀ - rotatingSlice a U s₀) y (unitVector i)‖ ^ 2) = 0 := by
    simp
  have ht := key.tendsto
  rw [h0] at ht
  have hsq' : Tendsto (fun s => ‖Freq.embedX (rotatingSlice a U s) -
      Freq.embedX (rotatingSlice a U s₀)‖ ^ 2) (𝓝 s₀) (𝓝 0) := by
    rw [funext hsq]
    exact ht
  have hs := (Real.continuous_sqrt.tendsto 0).comp hsq'
  rw [Real.sqrt_zero] at hs
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine hs.congr (fun s => ?_)
  simp [Function.comp, Real.sqrt_sq (norm_nonneg _)]

theorem rotatingSliceContinuous_holds : RotatingSliceContinuous :=
  rotatingSliceContinuous axialRotationSpec

end Breakdown
