import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace FrequencySeminorm

namespace Internal

def radialDamp (y : Space) : ℝ := (1 + ‖y‖ ^ 2)⁻¹

def radialField (j : Fin 3) (y : Space) : ℝ := y j * radialDamp y

theorem one_add_norm_sq_pos (y : Space) : 0 < 1 + ‖y‖ ^ 2 := by positivity

theorem norm_sq_eq_sum (y : Space) : ‖y‖ ^ 2 = ∑ j : Fin 3, y j ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

theorem fderiv_radialDamp_apply (j : Fin 3) (y : Space) :
    fderiv ℝ radialDamp y (unitVector j) = -(2 * y j) * radialDamp y ^ 2 := by
  have h0 : HasFDerivAt (fun x : Space => 1 + ‖x‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_add 1
  have h1 := HasFDerivAt.comp y (hasFDerivAt_inv (𝕜 := ℝ) (one_add_norm_sq_pos y).ne') h0
  rw [show radialDamp = (fun t : ℝ => t⁻¹) ∘ (fun x : Space => 1 + ‖x‖ ^ 2) from rfl, h1.fderiv]
  simp [unitVector, EuclideanSpace.inner_single_right]
  ring

theorem hasFDerivAt_coord (j : Fin 3) (y : Space) :
    HasFDerivAt (fun x : Space => x j) (EuclideanSpace.proj j : Space →L[ℝ] ℝ) y :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt

theorem contDiff_radialDamp : ContDiff ℝ ∞ radialDamp := by
  unfold radialDamp
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).inv fun y => (one_add_norm_sq_pos y).ne'

theorem fderiv_radialField (j : Fin 3) (y : Space) :
    fderiv ℝ (radialField j) y (unitVector j) = radialDamp y - 2 * y j ^ 2 * radialDamp y ^ 2 := by
  have hc := hasFDerivAt_coord j y
  have hd : DifferentiableAt ℝ radialDamp y := contDiff_radialDamp.differentiable (by simp) y
  have e : radialField j = fun x : Space => x j * radialDamp x := rfl
  rw [e, fderiv_fun_mul hc.differentiableAt hd, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, fderiv_radialDamp_apply, hc.fderiv]
  simp [unitVector]
  ring

theorem contDiff_radialField (j : Fin 3) : ContDiff ℝ ∞ (radialField j) :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.mul contDiff_radialDamp

theorem radialDiv_ge (y : Space) :
    radialDamp y ≤ ∑ j : Fin 3, fderiv ℝ (radialField j) y (unitVector j) := by
  simp only [fderiv_radialField]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← norm_sq_eq_sum]
  have hp := one_add_norm_sq_pos y
  have hw : radialDamp y * (1 + ‖y‖ ^ 2) = 1 := by
    unfold radialDamp
    field_simp
  have hw0 : 0 ≤ radialDamp y := by unfold radialDamp; positivity
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have h3 : ‖y‖ ^ 2 * radialDamp y ^ 2 = radialDamp y - radialDamp y ^ 2 := by
    have : ‖y‖ ^ 2 * radialDamp y = 1 - radialDamp y := by linarith
    calc ‖y‖ ^ 2 * radialDamp y ^ 2 = (‖y‖ ^ 2 * radialDamp y) * radialDamp y := by ring
      _ = _ := by rw [this]; ring
  nlinarith [mul_nonneg hw0 hw0]

theorem integrable_of_vanish {u : Space → ℝ} (hc : HasCompactSupport u) {F : Space → ℝ}
    (hF : Continuous F) (h : ∀ y, y ∉ tsupport u → F y = 0) : Integrable F :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hc h)

theorem weighted_sq_le_grad_smooth {u : Space → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ∫ y, u y ^ 2 * radialDamp y ≤ 4 * ∫ y, ∑ j : Fin 3, fderiv ℝ u y (unitVector j) ^ 2 := by
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have hcu : Continuous u := hu.continuous
  have hcd : ∀ j : Fin 3, Continuous (fun y => fderiv ℝ u y (unitVector j)) := fun j =>
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcb : ∀ j : Fin 3, Continuous (radialField j) := fun j => (contDiff_radialField j).continuous
  have hcdb : ∀ j : Fin 3, Continuous (fun y => fderiv ℝ (radialField j) y (unitVector j)) := fun j =>
    ((contDiff_radialField j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hcw : Continuous radialDamp := contDiff_radialDamp.continuous
  have hz : ∀ y, y ∉ tsupport u → u y = 0 ∧ ∀ j : Fin 3, fderiv ℝ u y (unitVector j) = 0 := by
    intro y hy
    refine ⟨?_, fun j => ?_⟩
    · by_contra h
      exact hy (subset_tsupport u h)
    · rw [fderiv_of_notMem_tsupport ℝ hy]
      rfl
  have hfd : ∀ j : Fin 3, ∀ y, fderiv ℝ (fun x => u x * u x) y (unitVector j) =
      2 * u y * fderiv ℝ u y (unitVector j) := by
    intro j y
    rw [fderiv_fun_mul (hdu y) (hdu y)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have key : ∀ j : Fin 3, ∫ y, u y ^ 2 * fderiv ℝ (radialField j) y (unitVector j) =
      ∫ y, -(2 * u y * fderiv ℝ u y (unitVector j) * radialField j y) := by
    intro j
    have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun x => u x * u x) (g := radialField j) (v := unitVector j)
      (by
        simp only [hfd]
        exact integrable_of_vanish hc (((continuous_const.mul hcu).mul (hcd j)).mul (hcb j))
          fun y hy => by simp [(hz y hy).1])
      (integrable_of_vanish hc ((hcu.mul hcu).mul (hcdb j)) fun y hy => by simp [(hz y hy).1])
      (integrable_of_vanish hc ((hcu.mul hcu).mul (hcb j)) fun y hy => by simp [(hz y hy).1])
      (fun x _ => (hdu x).mul (hdu x))
      (fun x _ => (contDiff_radialField j).differentiable (by simp) x)
    simp only [hfd] at ibp
    rw [integral_neg]
    simp only [sq]
    exact ibp
  have iI : Integrable (fun y => u y ^ 2 * radialDamp y) :=
    integrable_of_vanish hc ((hcu.pow 2).mul hcw) fun y hy => by simp [(hz y hy).1]
  have iDiv : Integrable (fun y => u y ^ 2 * ∑ j : Fin 3, fderiv ℝ (radialField j) y (unitVector j)) :=
    integrable_of_vanish hc ((hcu.pow 2).mul (continuous_finsetSum _ fun j _ => hcdb j))
      fun y hy => by simp [(hz y hy).1]
  have iT : ∀ j : Fin 3, Integrable (fun y => u y ^ 2 * fderiv ℝ (radialField j) y (unitVector j)) :=
    fun j => integrable_of_vanish hc ((hcu.pow 2).mul (hcdb j)) fun y hy => by simp [(hz y hy).1]
  have iS : ∀ j : Fin 3, Integrable (fun y => -(2 * u y * fderiv ℝ u y (unitVector j) * radialField j y)) :=
    fun j => integrable_of_vanish hc ((((continuous_const.mul hcu).mul (hcd j)).mul (hcb j)).neg)
      fun y hy => by simp [(hz y hy).1]
  have iD : Integrable (fun y => ∑ j : Fin 3, fderiv ℝ u y (unitVector j) ^ 2) :=
    integrable_of_vanish hc (continuous_finsetSum _ fun j _ => (hcd j).pow 2)
      fun y hy => by simp [(hz y hy).2]
  have s1 : ∫ y, u y ^ 2 * radialDamp y ≤
      ∫ y, u y ^ 2 * ∑ j : Fin 3, fderiv ℝ (radialField j) y (unitVector j) :=
    integral_mono iI iDiv fun y => mul_le_mul_of_nonneg_left (radialDiv_ge y) (sq_nonneg _)
  have s2 : ∫ y, u y ^ 2 * ∑ j : Fin 3, fderiv ℝ (radialField j) y (unitVector j) =
      ∫ y, ∑ j : Fin 3, -(2 * u y * fderiv ℝ u y (unitVector j) * radialField j y) := by
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ fun j _ => iT j, integral_finsetSum _ fun j _ => iS j]
    exact Finset.sum_congr rfl fun j _ => key j
  have hpt : ∀ y, ∑ j : Fin 3, -(2 * u y * fderiv ℝ u y (unitVector j) * radialField j y) ≤
      1 / 2 * (u y ^ 2 * radialDamp y) + 2 * ∑ j : Fin 3, fderiv ℝ u y (unitVector j) ^ 2 := by
    intro y
    have hw0 : 0 ≤ radialDamp y := by unfold radialDamp; positivity
    have hw : radialDamp y * (1 + ‖y‖ ^ 2) = 1 := by
      unfold radialDamp
      field_simp
    have hterm : ∀ j : Fin 3, -(2 * u y * fderiv ℝ u y (unitVector j) * radialField j y) ≤
        2 * fderiv ℝ u y (unitVector j) ^ 2 + 1 / 2 * (u y * y j * radialDamp y) ^ 2 := by
      intro j
      unfold radialField
      nlinarith [sq_nonneg (2 * fderiv ℝ u y (unitVector j) + u y * y j * radialDamp y)]
    have hsum : ∑ j : Fin 3, (u y * y j * radialDamp y) ^ 2 = u y ^ 2 * radialDamp y ^ 2 * ‖y‖ ^ 2 := by
      rw [norm_sq_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hle : u y ^ 2 * radialDamp y ^ 2 * ‖y‖ ^ 2 ≤ u y ^ 2 * radialDamp y := by
      have : radialDamp y * ‖y‖ ^ 2 ≤ 1 := by nlinarith
      calc u y ^ 2 * radialDamp y ^ 2 * ‖y‖ ^ 2 = (u y ^ 2 * radialDamp y) * (radialDamp y * ‖y‖ ^ 2) := by ring
        _ ≤ (u y ^ 2 * radialDamp y) * 1 :=
          mul_le_mul_of_nonneg_left this (mul_nonneg (sq_nonneg _) hw0)
        _ = _ := mul_one _
    calc _ ≤ ∑ j : Fin 3, (2 * fderiv ℝ u y (unitVector j) ^ 2 + 1 / 2 * (u y * y j * radialDamp y) ^ 2) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = 2 * ∑ j : Fin 3, fderiv ℝ u y (unitVector j) ^ 2 + 1 / 2 * ∑ j : Fin 3, (u y * y j * radialDamp y) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by rw [hsum]; linarith
  have s3 : ∫ y, ∑ j : Fin 3, -(2 * u y * fderiv ℝ u y (unitVector j) * radialField j y) ≤
      ∫ y, (1 / 2 * (u y ^ 2 * radialDamp y) + 2 * ∑ j : Fin 3, fderiv ℝ u y (unitVector j) ^ 2) :=
    integral_mono (integrable_finsetSum _ fun j _ => iS j) ((iI.const_mul _).add (iD.const_mul _)) hpt
  rw [integral_add (iI.const_mul _) (iD.const_mul _), integral_const_mul, integral_const_mul] at s3
  linarith

end Internal

end FrequencySeminorm

end Coercive

end Breakdown
