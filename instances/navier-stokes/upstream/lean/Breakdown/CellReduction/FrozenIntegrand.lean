import Breakdown.CellReduction.MatrixFacts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertReduction

namespace Internal

theorem frozen_first_pointwise (g x b f C : ℝ) (hg : 0 ≤ g) (hx : 0 ≤ x) (hb : 0 ≤ b)
    (hxC : x ≤ C) (hgf : g ^ 2 ≤ f) : g * x * b ≤ C * (f + b ^ 2) := by
  have hC : 0 ≤ C := hx.trans hxC
  have h1 : g * x * b ≤ g * C * b :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxC hg) hb
  have h2 : g * b ≤ g ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (g - b), mul_nonneg hg hb]
  calc g * x * b ≤ g * C * b := h1
    _ = C * (g * b) := by ring
    _ ≤ C * (g ^ 2 + b ^ 2) := mul_le_mul_of_nonneg_left h2 hC
    _ ≤ C * (f + b ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hC

theorem frozen_second_pointwise (d m b a C : ℝ) (hd : 0 ≤ d) (hm : 0 ≤ m) (ha : 0 ≤ a) (hda : d ≤ C * a) : d * m * b ≤ C ^ 2 * (a ^ 3 + m ^ 6) + b ^ 2 := by
  have h1 : d * m * b ≤ (d * m) ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (2 * (d * m) - b), sq_nonneg b]
  have h2 : d ^ 2 ≤ (C * a) ^ 2 := pow_le_pow_left₀ hd hda 2
  have h3 : a ^ 2 * m ^ 2 ≤ a ^ 3 + m ^ 6 := by
    have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
    have hk : 0 ≤ (a - m ^ 2) ^ 2 * (2 * a + m ^ 2) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    nlinarith [pow_nonneg ha 3, pow_nonneg hm 6]
  have h4 : (d * m) ^ 2 ≤ C ^ 2 * (a ^ 3 + m ^ 6) := by
    calc (d * m) ^ 2 = d ^ 2 * m ^ 2 := by ring
      _ ≤ (C * a) ^ 2 * m ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg m)
      _ = C ^ 2 * (a ^ 2 * m ^ 2) := by ring
      _ ≤ C ^ 2 * (a ^ 3 + m ^ 6) := mul_le_mul_of_nonneg_left h3 (sq_nonneg C)
  linarith

theorem trace_aestronglyMeasurable {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : ∀ j : Fin 3, AEStronglyMeasurable (fun y => (H y).flip (unitVector j)) volume) :
    AEStronglyMeasurable (fun y => secondDerivTrace (H y)) volume := by
  have h : ∀ j : Fin 3,
      AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector j)) volume := by
    intro j
    have h' := (hH j).apply_continuousLinearMap (unitVector j)
    simpa only [ContinuousLinearMap.flip_apply] using h'
  unfold secondDerivTrace
  exact Finset.aestronglyMeasurable_fun_sum _ (fun j _ => h j)

theorem columnSquareSum_continuous : Continuous (fun A : Space →L[ℝ] Space => matSq A) := by
  unfold matSq
  fun_prop

theorem apply_aestronglyMeasurable {A : Space → (Space →L[ℝ] Space)} {u : Space → Space}
    (hA : AEStronglyMeasurable A volume) (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (fun y => A y (u y)) volume :=
  (ContinuousLinearMap.apply ℝ Space).aestronglyMeasurable_comp₂ hu hA

theorem integrable_of_lintegral_lt {f : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (h0 : ∀ y, 0 ≤ f y) (hfin : ∫⁻ y, ENNReal.ofReal (f y) < ⊤) : Integrable f :=
  ⟨hf, (hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)).2 hfin⟩

theorem decay_cube (y : Space) :
    (((1 + ‖y‖) ^ 2)⁻¹) ^ 3 = (1 + ‖y‖) ^ (-(6 : ℝ)) := by
  have hx : 0 ≤ 1 + ‖y‖ := by positivity
  rw [Real.rpow_neg hx, inv_pow, ← pow_mul]
  norm_num

end Internal

theorem frozenIntegrand : FrozenIntegrandHolds := by
  intro Γ C W w G H hW hWb hdWb hP
  have hGm : AEStronglyMeasurable G volume := hP.weak_gradient.2.1.aestronglyMeasurable
  have hwm : AEStronglyMeasurable w volume := hP.weak_gradient.1.aestronglyMeasurable
  have hTm : AEStronglyMeasurable (fun y => secondDerivTrace (H y)) volume :=
    Internal.trace_aestronglyMeasurable (fun j => (hP.weak_secondDeriv j).2.1.aestronglyMeasurable)
  have hWc : Continuous W := hW.continuous
  have hdWc : Continuous (fun y => fderiv ℝ W y) := hW.continuous_fderiv (by simp)
  have hC : 0 ≤ C := by
    have h := hWb 0
    rw [norm_zero, add_zero, div_one] at h
    exact (norm_nonneg _).trans h
  have hF : Integrable (fun y => matSq (G y)) :=
    Internal.integrable_of_lintegral_lt
      (Internal.columnSquareSum_continuous.comp_aestronglyMeasurable hGm)
      (fun y => columnSquareSum_nonneg _) hP.gradient_finite
  have hT : Integrable (fun y => ‖secondDerivTrace (H y)‖ ^ 2) :=
    Internal.integrable_of_lintegral_lt (hTm.norm.pow 2) (fun y => sq_nonneg _)
      hP.sumSecondPartials_finite
  have hS : Integrable (fun y => ‖w y‖ ^ 6) :=
    Internal.integrable_of_lintegral_lt (hwm.norm.pow 6) (fun y => by positivity) hP.sixth_power
  have hD : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(6 : ℝ))) :=
    integrable_one_add_norm (by simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]; norm_num)
  constructor
  · have hB : Integrable (fun y => C * (matSq (G y) + ‖secondDerivTrace (H y)‖ ^ 2)) :=
      (hF.add hT).const_mul C
    refine hB.mono' ((Internal.apply_aestronglyMeasurable hGm hWc.aestronglyMeasurable).inner
      hTm.neg) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    have h1 := abs_real_inner_le_norm (G y (W y)) (-secondDerivTrace (H y))
    rw [norm_neg] at h1
    have h2 : ‖G y (W y)‖ ≤ ‖G y‖ * ‖W y‖ := (G y).le_opNorm _
    have h3 : ‖W y‖ ≤ C := (hWb y).trans (div_le_self hC (by linarith [norm_nonneg y]))
    have h5 := Internal.frozen_first_pointwise ‖G y‖ ‖W y‖ ‖secondDerivTrace (H y)‖ (matSq (G y)) C
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) h3 (operatorSquareBound (G y))
    calc |inner ℝ (G y (W y)) (-secondDerivTrace (H y))|
        ≤ ‖G y (W y)‖ * ‖secondDerivTrace (H y)‖ := h1
      _ ≤ ‖G y‖ * ‖W y‖ * ‖secondDerivTrace (H y)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ C * (matSq (G y) + ‖secondDerivTrace (H y)‖ ^ 2) := h5
  · have hB : Integrable (fun y => C ^ 2 * ((1 + ‖y‖) ^ (-(6 : ℝ)) + ‖w y‖ ^ 6)
        + ‖secondDerivTrace (H y)‖ ^ 2) :=
      ((hD.add hS).const_mul (C ^ 2)).add hT
    refine hB.mono' ((Internal.apply_aestronglyMeasurable hdWc.aestronglyMeasurable hwm).inner
      hTm.neg) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    have h1 := abs_real_inner_le_norm (fderiv ℝ W y (w y)) (-secondDerivTrace (H y))
    rw [norm_neg] at h1
    have h2 : ‖fderiv ℝ W y (w y)‖ ≤ ‖fderiv ℝ W y‖ * ‖w y‖ := (fderiv ℝ W y).le_opNorm _
    have ha : 0 ≤ ((1 + ‖y‖) ^ 2)⁻¹ := by positivity
    have hda : ‖fderiv ℝ W y‖ ≤ C * ((1 + ‖y‖) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact hdWb y
    have h5 := Internal.frozen_second_pointwise ‖fderiv ℝ W y‖ ‖w y‖ ‖secondDerivTrace (H y)‖
      ((1 + ‖y‖) ^ 2)⁻¹ C (norm_nonneg _) (norm_nonneg _) ha hda
    rw [Internal.decay_cube] at h5
    calc |inner ℝ (fderiv ℝ W y (w y)) (-secondDerivTrace (H y))|
        ≤ ‖fderiv ℝ W y (w y)‖ * ‖secondDerivTrace (H y)‖ := h1
      _ ≤ ‖fderiv ℝ W y‖ * ‖w y‖ * ‖secondDerivTrace (H y)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ C ^ 2 * ((1 + ‖y‖) ^ (-(6 : ℝ)) + ‖w y‖ ^ 6) + ‖secondDerivTrace (H y)‖ ^ 2 := h5

end CertReduction

end Breakdown
