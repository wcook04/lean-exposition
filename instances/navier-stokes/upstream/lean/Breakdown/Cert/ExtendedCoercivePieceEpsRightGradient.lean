import Breakdown.Cert.ExtendedCoercivePieceEpsAeSecondDeriv
import Breakdown.Cert.CoerciveSmoothEpsRightGradient

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.WeakRightGradient

open Coercive Coercive.Internal.SmoothRightGradient

theorem norm_fderiv_smoothRight_weak_le {P : ℝ} {W v : ℝ → Space → Space}
    (hV : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2)) (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2))
    (σ : ℝ) (y : Space) (hd : DifferentiableAt ℝ (fderiv ℝ (W σ)) y) :
    ‖fderiv ℝ (smoothRight P W v σ) y‖ ≤ ‖fderiv ℝ (transportPart P v σ) y‖
      + ‖negTrace‖ * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y‖
      + (‖fderiv ℝ (v σ) y‖ * ‖fderiv ℝ (W σ) y‖ + ‖fderiv ℝ (fderiv ℝ (v σ)) y‖ * ‖W σ y‖)
      + (‖fderiv ℝ (W σ) y‖ * ‖fderiv ℝ (v σ) y‖ + ‖fderiv ℝ (fderiv ℝ (W σ)) y‖ * ‖v σ y‖) := by
  have hs : ContDiff ℝ 3 (v σ) := contDiff_slice hV σ
  have hws : ContDiff ℝ 1 (W σ) := contDiff_slice hW σ
  have hv1 : ContDiff ℝ 2 (fderiv ℝ (v σ)) := hs.fderiv_right (m := 2) (by norm_num)
  have hv2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (v σ))) := hv1.fderiv_right (m := 1) (by norm_num)
  have htp : DifferentiableAt ℝ (transportPart P v σ) y := by
    rw [transportPart_eq (hV.differentiable (by norm_num)) σ]
    exact ((contDiff_transportJoint (P := P) (hV.of_le (by norm_num))).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) y
  have d1 := htp.hasFDerivAt
  have d2 : HasFDerivAt (fun x => negTrace (fderiv ℝ (fderiv ℝ (v σ)) x))
      (negTrace.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y)) y :=
    negTrace.hasFDerivAt.comp y ((hv2.differentiable (by norm_num)) y).hasFDerivAt
  have d3 := apply_hasFDerivAt (f := v σ) (g := W σ) ((hv1.differentiable (by norm_num)) y)
    ((hws.differentiable (by norm_num)) y)
  have d4 := apply_hasFDerivAt (f := W σ) (g := v σ) hd ((hs.differentiable (by norm_num)) y)
  have H := ((d1.add d2).add d3).add d4
  rw [smoothRight_eq P W v σ]
  refine (congrArg (fun L => ‖L‖) H.fderiv).trans_le ?_
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le _ _)))
    (norm_apply_deriv_le _ _ _ _))) (norm_apply_deriv_le _ _ _ _))

theorem periodLIntegral_lt_top_of_ae_le {f g : ℝ → Space → ℝ} (hfg : ∀ σ, ∀ᵐ y, f σ y ≤ g σ y)
    (h : periodLIntegral g < ⊤) : periodLIntegral f < ⊤ :=
  lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono_ae ((hfg σ).mono fun y hy =>
    ENNReal.ofReal_le_ofReal hy)) h

theorem gradField_smoothRight_sq_finite_weak {P : ℝ} {W v : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} (hv : IsSmoothPerturbation P v)
    (hW : IsWeakSecondDerivState W HW D) :
    periodLIntegral (fun σ y => matSq (gradField (smoothRight P W v) σ y)) < ⊤ := by
  have hV : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 3
  have hD0 : 0 ≤ D := by
    have h0 := (hW.decay 0 0).1
    rw [norm_zero, add_zero, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hy1 : ∀ y : Space, (1 : ℝ) ≤ 1 + ‖y‖ := fun y => le_add_of_nonneg_right (norm_nonneg y)
  have hW0 : ∀ σ y, ‖W σ y‖ ≤ D := fun σ y =>
    (hW.decay σ y).1.trans (div_le_self hD0 (hy1 y))
  have hW1 : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ D := fun σ y =>
    (hW.decay σ y).2.1.trans (div_le_self hD0 (one_le_pow₀ (hy1 y)))
  have hW2 : ∀ σ y, ‖HW σ y‖ * ‖v σ y‖ ≤ D * (‖v σ y‖ / (1 + ‖y‖)) := fun σ y => by
    have h := (hW.decay σ y).2.2
    have h3 : D / (1 + ‖y‖) ^ 3 ≤ D / (1 + ‖y‖) := by
      refine div_le_div_of_nonneg_left hD0 (by positivity) ?_
      exact le_self_pow₀ (hy1 y) (by norm_num)
    calc ‖HW σ y‖ * ‖v σ y‖ ≤ D / (1 + ‖y‖) * ‖v σ y‖ :=
          mul_le_mul_of_nonneg_right (h.trans h3) (norm_nonneg _)
      _ = D * (‖v σ y‖ / (1 + ‖y‖)) := by ring
  set c := ‖negTrace‖
  set b1 : ℝ → Space → ℝ := fun σ y => ‖fderiv ℝ (transportPart P v σ) y‖
  set b2 : ℝ → Space → ℝ := fun σ y => ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y‖
  set b3 : ℝ → Space → ℝ := fun σ y => ‖fderiv ℝ (fderiv ℝ (v σ)) y‖
  set b4 : ℝ → Space → ℝ := fun σ y => ‖fderiv ℝ (v σ) y‖
  set b5 : ℝ → Space → ℝ := fun σ y => ‖v σ y‖ / (1 + ‖y‖)
  have hpt : ∀ σ, ∀ᵐ y, matSq (gradField (smoothRight P W v) σ y) ≤
      15 * (b1 σ y ^ 2 + c ^ 2 * b2 σ y ^ 2 + D ^ 2 * b3 σ y ^ 2 + 4 * D ^ 2 * b4 σ y ^ 2
        + D ^ 2 * b5 σ y ^ 2) := fun σ => by
    filter_upwards [WeakGradientSlope.ae_hasFDerivAt_fderiv hW σ] with y hy
    have hn := norm_fderiv_smoothRight_weak_le (P := P) hV hW.smooth σ y hy.differentiableAt
    rw [hy.fderiv] at hn
    have e1 : ‖fderiv ℝ (v σ) y‖ * ‖fderiv ℝ (W σ) y‖ ≤ b4 σ y * D :=
      mul_le_mul_of_nonneg_left (hW1 σ y) (norm_nonneg _)
    have e2 : ‖fderiv ℝ (fderiv ℝ (v σ)) y‖ * ‖W σ y‖ ≤ b3 σ y * D :=
      mul_le_mul_of_nonneg_left (hW0 σ y) (norm_nonneg _)
    have e3 : ‖fderiv ℝ (W σ) y‖ * ‖fderiv ℝ (v σ) y‖ ≤ D * b4 σ y :=
      mul_le_mul_of_nonneg_right (hW1 σ y) (norm_nonneg _)
    have e4 := hW2 σ y
    have hsum : ‖gradField (smoothRight P W v) σ y‖ ≤
        b1 σ y + c * b2 σ y + D * b3 σ y + 2 * D * b4 σ y + D * b5 σ y := by
      show ‖fderiv ℝ (smoothRight P W v σ) y‖ ≤ _
      simp only [b1, b2, b3, b4, b5]
      linarith
    have h0 : 0 ≤ ‖gradField (smoothRight P W v) σ y‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ h0 hsum 2
    have h5 := sq_sum_five_le (b1 σ y) (c * b2 σ y) (D * b3 σ y) (2 * D * b4 σ y) (D * b5 σ y)
    have hf := matSq_le (gradField (smoothRight P W v) σ y)
    nlinarith [hsq, h5, hf]
  have hs : ∀ σ, ContDiff ℝ 3 (v σ) := contDiff_slice hV
  have cb1 : Continuous fun z : ℝ × Space => b1 z.1 z.2 ^ 2 := by
    have e : (fun z : ℝ × Space => b1 z.1 z.2) = fun z => ‖fderiv ℝ (fun y => transportJoint P v (z.1, y)) z.2‖ := by
      funext z
      simp only [b1]
      rw [transportPart_eq (hV.differentiable (by norm_num)) z.1]
    have hc : Continuous fun z : ℝ × Space => fderiv ℝ (fun y => transportJoint P v (z.1, y)) z.2 :=
      (contDiff_fderiv_param (F := fun σ y => transportJoint P v (σ, y)) (m := 0)
        (contDiff_transportJoint (hV.of_le (by norm_num))) (by norm_num)).continuous
    rw [show (fun z : ℝ × Space => b1 z.1 z.2 ^ 2) = fun z => (fun z : ℝ × Space => b1 z.1 z.2) z ^ 2 from rfl, e]
    exact hc.norm.pow 2
  have hDv : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    contDiff_fderiv_param (F := v) hV (by norm_num)
  have hD2v : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fderiv ℝ (v z.1)) z.2) :=
    contDiff_fderiv_param (F := fun σ x => fderiv ℝ (v σ) x) hDv (by norm_num)
  have hD3v : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fderiv ℝ (fderiv ℝ (v z.1))) z.2) :=
    contDiff_fderiv_param (F := fun σ x => fderiv ℝ (fderiv ℝ (v σ)) x) hD2v (by norm_num)
  have cb2 : Continuous fun z : ℝ × Space => c ^ 2 * b2 z.1 z.2 ^ 2 :=
    continuous_const.mul (hD3v.continuous.norm.pow 2)
  have cb3 : Continuous fun z : ℝ × Space => D ^ 2 * b3 z.1 z.2 ^ 2 :=
    continuous_const.mul (hD2v.continuous.norm.pow 2)
  have cb4 : Continuous fun z : ℝ × Space => 4 * D ^ 2 * b4 z.1 z.2 ^ 2 :=
    continuous_const.mul (hDv.continuous.norm.pow 2)
  have fin1 : periodLIntegral (fun σ y => b1 σ y ^ 2) < ⊤ := by
    refine periodLIntegral_lt_top_of_le (fun σ y => le_of_eq ?_) (hv.transport_finite 1)
    simp only [b1]
    rw [norm_iteratedFDeriv_one]
  have fin2 : periodLIntegral (fun σ y => c ^ 2 * b2 σ y ^ 2) < ⊤ := by
    refine periodLIntegral_const_mul_lt_top (by positivity) ?_
    refine periodLIntegral_lt_top_of_le (fun σ y => le_of_eq ?_) (hv.derivatives_finite 3 (by norm_num))
    simp only [b2]
    rw [norm_iteratedFDeriv_three_eq]
  have fin3 : periodLIntegral (fun σ y => D ^ 2 * b3 σ y ^ 2) < ⊤ := by
    refine periodLIntegral_const_mul_lt_top (by positivity) ?_
    refine periodLIntegral_lt_top_of_le (fun σ y => le_of_eq ?_) (hv.derivatives_finite 2 (by norm_num))
    simp only [b3]
    rw [norm_iteratedFDeriv_two_eq]
  have fin4 : periodLIntegral (fun σ y => 4 * D ^ 2 * b4 σ y ^ 2) < ⊤ := by
    refine periodLIntegral_const_mul_lt_top (by positivity) ?_
    refine periodLIntegral_lt_top_of_le (fun σ y => le_of_eq ?_) (hv.derivatives_finite 1 (by norm_num))
    simp only [b4]
    rw [norm_iteratedFDeriv_one]
  have fin5 : periodLIntegral (fun σ y => D ^ 2 * b5 σ y ^ 2) < ⊤ := by
    refine periodLIntegral_const_mul_lt_top (by positivity) ?_
    refine periodLIntegral_lt_top_of_le (fun σ y => le_of_eq ?_) hv.weighted_finite
    simp only [b5]
    rw [div_pow]
  have hsplit : periodLIntegral (fun σ y => b1 σ y ^ 2 + c ^ 2 * b2 σ y ^ 2 + D ^ 2 * b3 σ y ^ 2
      + 4 * D ^ 2 * b4 σ y ^ 2 + D ^ 2 * b5 σ y ^ 2) < ⊤ := by
    refine lt_of_le_of_lt (periodLIntegral_add_of_continuous (((cb1.add cb2).add cb3).add cb4)) ?_
    refine ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt (periodLIntegral_add_of_continuous ((cb1.add cb2).add cb3)) ?_, fin5⟩
    refine ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt (periodLIntegral_add_of_continuous (cb1.add cb2)) ?_, fin4⟩
    refine ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt (periodLIntegral_add_of_continuous cb1) ?_, fin3⟩
    exact ENNReal.add_lt_top.mpr ⟨fin1, fin2⟩
  exact periodLIntegral_lt_top_of_ae_le hpt (periodLIntegral_const_mul_lt_top (by norm_num) hsplit)

theorem continuous_smoothRight_weak {P : ℝ} {W v : ℝ → Space → Space} (hv : IsSmoothPerturbation P v)
    (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => smoothRight P W v z.1 z.2) := by
  have hV : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 3
  have hDv : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    contDiff_fderiv_param (F := v) hV (by norm_num)
  have hD2v : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fderiv ℝ (v z.1)) z.2) :=
    contDiff_fderiv_param (F := fun σ x => fderiv ℝ (v σ) x) hDv (by norm_num)
  have hDW : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    contDiff_fderiv_param (F := W) hW (by norm_num)
  have e : (fun z : ℝ × Space => smoothRight P W v z.1 z.2) = fun z =>
      transportJoint P v z + negTrace (fderiv ℝ (fderiv ℝ (v z.1)) z.2)
        + fderiv ℝ (v z.1) z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2) := by
    funext z
    rw [smoothRight_eq P W v z.1, transportPart_eq (hV.differentiable (by norm_num)) z.1]
  rw [e]
  exact ((((contDiff_transportJoint (hV.of_le (by norm_num))).continuous.add
    (negTrace.continuous.comp hD2v.continuous)).add
    (hDv.continuous.clm_apply hW.continuous)).add (hDW.continuous.clm_apply hV.continuous))

theorem rightGradient_finite_of_weak {P : ℝ} {W v : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} (hv : IsSmoothPerturbation P v)
    (hW : IsWeakSecondDerivState W HW D) :
    AEStronglyMeasurable (fun z : ℝ × Space => gradField (smoothRight P W v) z.1 z.2) volume ∧
      IsTimePeriodic (gradField (smoothRight P W v)) ∧
      periodLIntegral (fun σ y => matSq (gradField (smoothRight P W v) σ y)) < ⊤ := by
  have hc := continuous_smoothRight_weak (P := P) hv hW.smooth
  have hm : Measurable (fun z : ℝ × Space => fderiv ℝ (smoothRight P W v z.1) z.2) :=
    measurable_fderiv_with_param ℝ (f := fun σ y => smoothRight P W v σ y) hc
  have hper : IsTimePeriodic (gradField (smoothRight P W v)) := by
    intro σ y
    have e : smoothRight P W v (σ + 1) = smoothRight P W v σ :=
      funext (smoothRight_periodic hv.periodic hW.periodic σ)
    unfold gradField
    rw [e]
  exact ⟨hm.aestronglyMeasurable, hper, gradField_smoothRight_sq_finite_weak hv hW⟩

end Internal.WeakRightGradient

end CoerciveWeak

end Breakdown
