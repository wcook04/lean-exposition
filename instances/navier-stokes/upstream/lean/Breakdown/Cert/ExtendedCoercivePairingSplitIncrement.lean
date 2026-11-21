import Breakdown.Cert.ExtendedCoerciveStatement
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.MeanValue

open scoped ContDiff Convolution
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.WeakIncrement

theorem eq_sum_basis (w : Space) : w = ∑ j : Fin 3, w j • unitVector j := by
  ext i
  simp [unitVector, Pi.single_apply]

theorem reflect_isTestFunction (φ : ContDiffBump (0 : Space)) (z : Space) :
    IsTestFunction (fun w => φ.normed volume (z - w)) :=
  ⟨φ.contDiff_normed.comp (contDiff_const.sub contDiff_id),
    φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft z)⟩

theorem reflect_fderiv (φ : ContDiffBump (0 : Space)) (z w e : Space) :
    fderiv ℝ (fun w' => φ.normed volume (z - w')) w e = -(fderiv ℝ (φ.normed volume) (z - w) e) := by
  have hd : DifferentiableAt ℝ (φ.normed volume) (z - w) :=
    (φ.contDiff_normed (n := 1)).differentiable one_ne_zero _
  have h : HasFDerivAt (fun w' => φ.normed volume (z - w'))
      ((fderiv ℝ (φ.normed volume) (z - w)).comp (0 - ContinuousLinearMap.id ℝ Space)) w :=
    hd.hasFDerivAt.comp w ((hasFDerivAt_const z w).sub (hasFDerivAt_id w))
  rw [h.fderiv]
  simp

theorem conv_apply_eq {f : Space → (Space →L[ℝ] Space)} (hf : Continuous f)
    (φ : ContDiffBump (0 : Space)) (z e u : Space) :
    ((fderiv ℝ (φ.normed volume) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL Space, volume] f) z) e u
      = ∫ w, fderiv ℝ (φ.normed volume) (z - w) e • f w u := by
  set L' := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space)).precompL Space
  have c1 : Continuous (fderiv ℝ (φ.normed volume)) :=
    (φ.contDiff_normed (n := 1)).continuous_fderiv one_ne_zero
  have c2 : Continuous (fun t : Space => f (z - t)) := hf.comp (continuous_const.sub continuous_id)
  have hA : Integrable (fun t => L' (fderiv ℝ (φ.normed volume) t) (f (z - t))) := by
    refine Continuous.integrable_of_hasCompactSupport ((L'.continuous.comp c1).clm_apply c2) ?_
    refine ((φ.hasCompactSupport_normed (μ := volume)).fderiv (𝕜 := ℝ)).mono ?_
    intro t ht
    rw [Function.mem_support] at ht ⊢
    intro h0
    apply ht
    rw [h0]
    simp
  have hAe : Integrable (fun t => L' (fderiv ℝ (φ.normed volume) t) (f (z - t)) e) :=
    hA.apply_continuousLinearMap e
  rw [convolution_def, ContinuousLinearMap.integral_apply hA, ContinuousLinearMap.integral_apply hAe]
  have e1 : ∀ t, L' (fderiv ℝ (φ.normed volume) t) (f (z - t)) e u
      = fderiv ℝ (φ.normed volume) t e • f (z - t) u := by
    intro t
    simp [L']
  simp only [e1]
  have h := integral_sub_left_eq_self (μ := (volume : Measure Space))
    (fun w => fderiv ℝ (φ.normed volume) (z - w) e • f w u) z
  simp only [sub_sub_cancel] at h
  exact h

variable {f : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}

theorem basis_apply_eq (hf : Continuous f)
    (hweak : ∀ j : Fin 3, IsWeakGradient (fun y => f y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (φ : ContDiffBump (0 : Space)) (z : Space) (i j : Fin 3) :
    ((fderiv ℝ (φ.normed volume) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL Space, volume] f) z)
        (unitVector i) (unitVector j)
      = ∫ w, φ.normed volume (z - w) • H w (unitVector i) (unitVector j) := by
  rw [conv_apply_eq hf φ z]
  have hw := (hweak j).2.2 _ (reflect_isTestFunction φ z) i
  simp only [ContinuousLinearMap.flip_apply, reflect_fderiv, neg_smul, integral_neg, neg_neg] at hw
  exact hw.symm

theorem integrable_basis
    (hweak : ∀ j : Fin 3, IsWeakGradient (fun y => f y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (φ : ContDiffBump (0 : Space)) (z : Space) (i j : Fin 3) :
    Integrable (fun w => φ.normed volume (z - w) • H w (unitVector i) (unitVector j)) := by
  have h := ((hweak j).2.1.integrable_smul_left_of_hasCompactSupport
    (reflect_isTestFunction φ z).1.continuous (reflect_isTestFunction φ z).2).apply_continuousLinearMap
    (unitVector i)
  simpa only [smul_apply, ContinuousLinearMap.flip_apply] using h

theorem deriv_apply_eq (hf : Continuous f)
    (hweak : ∀ j : Fin 3, IsWeakGradient (fun y => f y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (φ : ContDiffBump (0 : Space)) (z d u : Space) :
    ((fderiv ℝ (φ.normed volume) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL Space, volume] f) z) d u
      = ∫ w, φ.normed volume (z - w) • H w d u := by
  set T := (fderiv ℝ (φ.normed volume) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL Space, volume] f) z
  have hI := integrable_basis hweak φ z
  have e1 : T d u = ∑ i : Fin 3, ∑ j : Fin 3, (d i * u j) • T (unitVector i) (unitVector j) := by
    conv_lhs => rw [eq_sum_basis d, eq_sum_basis u]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have e2 : (fun w => φ.normed volume (z - w) • H w d u) = fun w =>
      ∑ i : Fin 3, ∑ j : Fin 3, (d i * u j) • (φ.normed volume (z - w) • H w (unitVector i) (unitVector j)) := by
    funext w
    conv_lhs => rw [eq_sum_basis d, eq_sum_basis u]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  have hIs : ∀ i j, Integrable (fun w => (d i * u j) •
      (φ.normed volume (z - w) • H w (unitVector i) (unitVector j))) := fun i j => Integrable.smul (d i * u j) (hI i j)
  rw [e1, e2, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hIs i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hIs i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul, basis_apply_eq hf hweak φ z i j]

theorem integral_reflect (φ : ContDiffBump (0 : Space)) (z : Space) :
    ∫ w, φ.normed volume (z - w) = 1 := by
  rw [integral_sub_left_eq_self (μ := (volume : Measure Space)) (fun w => φ.normed volume w) z]
  exact φ.integral_normed

theorem deriv_norm_le (hf : Continuous f)
    (hweak : ∀ j : Fin 3, IsWeakGradient (fun y => f y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (φ : ContDiffBump (0 : Space)) (z : Space) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w, ‖w - z‖ < φ.rOut → ‖H w‖ ≤ C) :
    ‖(fderiv ℝ (φ.normed volume) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL Space, volume] f) z‖ ≤ C := by
  have ht := reflect_isTestFunction φ z
  have hψi : Integrable (fun w => φ.normed volume (z - w)) :=
    ht.1.continuous.integrable_of_hasCompactSupport ht.2
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun d => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg d)) fun u => ?_
  rw [deriv_apply_eq hf hweak φ z d u]
  have hg : Integrable (fun w => C * ‖d‖ * ‖u‖ * φ.normed volume (z - w)) := hψi.const_mul _
  refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun w => ?_)).trans ?_
  · rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed _)]
    by_cases h0 : φ.normed volume (z - w) = 0
    · rw [h0]; simp
    · have hs : z - w ∈ Function.support (φ.normed volume) := h0
      rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at hs
      have hw : ‖w - z‖ < φ.rOut := by rwa [norm_sub_rev]
      have h1 : ‖H w d u‖ ≤ C * ‖d‖ * ‖u‖ :=
        ((H w).le_opNorm₂ d u).trans (by gcongr; exact hb w hw)
      have h2 := φ.nonneg_normed (μ := volume) (z - w)
      nlinarith
  · rw [integral_const_mul, integral_reflect, mul_one]

def shrinkingBump (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ContDiffBump (0 : Space) :=
  ⟨δ / (2 * ((n : ℝ) + 2)), δ / ((n : ℝ) + 2), by positivity, by
    apply div_lt_div_of_pos_left hδ (by positivity)
    linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]⟩

theorem shrinkingBump_rOut (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : (shrinkingBump δ hδ n).rOut = δ / ((n : ℝ) + 2) :=
  rfl

theorem shrinkingBump_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Filter.Tendsto (fun n => (shrinkingBump δ hδ n).rOut) Filter.atTop (nhds 0) := by
  simp only [shrinkingBump_rOut]
  have h : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  exact h.const_div_atTop δ

theorem increment_of_weakSecondDeriv (hf : Continuous f)
    (hweak : ∀ j : Fin 3, IsWeakGradient (fun y => f y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    (x x' : Space) (K : ℝ)
    (hK : ∀ ε > 0, ∃ δ > 0, ∀ z ∈ segment ℝ x x', ∀ w, ‖w - z‖ < δ → ‖H w‖ ≤ K + ε) :
    ‖f x' - f x‖ ≤ K * ‖x' - x‖ := by
  have step : ∀ ε > 0, ‖f x' - f x‖ ≤ (K + ε) * ‖x' - x‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := hK ε hε
    have hC : 0 ≤ K + ε :=
      (norm_nonneg _).trans (hb x (left_mem_segment ℝ x x') x (by simpa using hδ))
    have bound : ∀ n : ℕ, ‖((shrinkingBump δ hδ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x'
        - ((shrinkingBump δ hδ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x‖
        ≤ (K + ε) * ‖x' - x‖ := by
      intro n
      set φ := shrinkingBump δ hδ n
      have hr : φ.rOut < δ := by
        show δ / ((n : ℝ) + 2) < δ
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      have hd : ∀ z, HasFDerivAt (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)
          ((fderiv ℝ (φ.normed volume) ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL Space, volume] f) z) z :=
        fun z => (φ.hasCompactSupport_normed (μ := volume)).hasFDerivAt_convolution_left
          (ContinuousLinearMap.lsmul ℝ ℝ) (φ.contDiff_normed (n := 1)) hf.locallyIntegrable z
      exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun z _ => (hd z).hasFDerivWithinAt)
        (fun z hz => deriv_norm_le hf hweak φ z hC (fun w hw => hb z hz w (hw.trans hr)))
        (convex_segment x x') (left_mem_segment ℝ x x') (right_mem_segment ℝ x x')
    have t1 := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure Space))
      (shrinkingBump_tendsto δ hδ) hf x
    have t2 := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure Space))
      (shrinkingBump_tendsto δ hδ) hf x'
    exact le_of_tendsto' ((t2.sub t1).norm) bound
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hn : 0 < ‖x' - x‖ + 1 := by positivity
  have h := step (η / (‖x' - x‖ + 1)) (by positivity)
  have h2 : η / (‖x' - x‖ + 1) * ‖x' - x‖ ≤ η := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    nlinarith [norm_nonneg (x' - x)]
  nlinarith

end Internal.WeakIncrement

end CoerciveWeak

end Breakdown
