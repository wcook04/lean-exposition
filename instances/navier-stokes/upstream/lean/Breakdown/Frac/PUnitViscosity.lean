import Breakdown.Frac.StProfile
import Breakdown.Frac.OpCovariance

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown

namespace FracInternal

private theorem axialTurn_smul (r : ℝ) (y : Space) : axialTurn (r • y) = r • axialTurn y := by
  ext i
  fin_cases i <;> simp [axialTurn]

private theorem fderiv_scaled {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space → F)
    (hf : Differentiable ℝ f) (c l : ℝ) (y : Space) :
    fderiv ℝ (fun x => c • f (l • x)) y = (c * l) • fderiv ℝ f (l • y) := by
  have hs : HasFDerivAt (fun x : Space => l • x) (l • ContinuousLinearMap.id ℝ Space) y :=
    (hasFDerivAt_id y).const_smul l
  have h := ((hf (l • y)).hasFDerivAt.comp y hs).const_smul c
  refine (h.fderiv : fderiv ℝ (fun x => c • f (l • x)) y = _).trans ?_
  ext v
  simp [smul_smul]

private theorem norm_iteratedFDeriv_scaled {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) (hf : ContDiff ℝ ∞ f) (c l : ℝ) (j : ℕ) (y : Space) :
    ‖iteratedFDeriv ℝ j (fun x => c • f (l • x)) y‖ =
      |c| * |l| ^ j * ‖iteratedFDeriv ℝ j f (l • y)‖ := by
  have hj : ContDiff ℝ j f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hc : ContDiff ℝ j (fun x => f (l • x)) := hj.comp (contDiff_const_smul l)
  rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt,
    congrFun (iteratedFDeriv_comp_const_smul l hj) y, norm_smul, norm_smul, norm_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc]

private theorem decay_scaled (l : ℝ) (hl : 0 < l) (e : ℝ) (he : 0 ≤ e) (y : Space) :
    (1 + ‖l • y‖) ^ (-e) ≤ (min 1 l) ^ (-e) * (1 + ‖y‖) ^ (-e) := by
  have hm : 0 < min 1 l := lt_min one_pos hl
  have hn : ‖l • y‖ = l * ‖y‖ := by rw [norm_smul, Real.norm_of_nonneg hl.le]
  have hy := norm_nonneg y
  have hle : min 1 l * (1 + ‖y‖) ≤ 1 + ‖l • y‖ := by
    rw [hn]
    have h1 : min 1 l ≤ 1 := min_le_left _ _
    have h2 : min 1 l ≤ l := min_le_right _ _
    nlinarith
  rw [← Real.mul_rpow hm.le (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (neg_nonpos.mpr he)

private theorem profile_scaled (α a ν : ℝ) (hα : 1 < α) (U : Space → Space) (P : Space → ℝ)
    (h : IsRotatingProfile α a ν U P) (l c d : ℝ) (hl : 0 < l) (hcl : c * l = 1)
    (hd : d = c * c) (hlν : l ^ (2 * α) = ν) :
    IsRotatingProfile α a 1 (fun y => c • U (l • y)) (fun y => d * P (l • y)) := by
  have hU2 : ContDiff ℝ 2 U := h.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
  have hUd : Differentiable ℝ U := h.smooth.differentiable (by simp)
  have hPd : Differentiable ℝ P := h.smooth_pressure.differentiable (by simp)
  have hPfun : (fun y => d * P (l • y)) = fun y => d • P (l • y) := rfl
  have hDU : ∀ y, fderiv ℝ (fun x => c • U (l • x)) y = fderiv ℝ U (l • y) := by
    intro y
    rw [fderiv_scaled U hUd, hcl, one_smul]
  have hDP : ∀ y, fderiv ℝ (fun x => d * P (l • x)) y = c • fderiv ℝ P (l • y) := by
    intro y
    rw [hPfun, fderiv_scaled P hPd, hd]
    congr 1
    calc c * c * l = c * (c * l) := by ring
      _ = c := by rw [hcl, mul_one]
  have hA : ∀ y, fractionalPowerAt α (fun x => c • U (l • x)) y =
      (c * ν) • fractionalPowerAt α U (l • y) := by
    intro y
    have hc2 : ContDiff ℝ 2 (fun x => U (l • x)) := hU2.comp (contDiff_const_smul l)
    rw [fractionalPowerAt_const_smul α (fun x => U (l • x)) hc2 c y,
      fractionalPowerAt_comp_smul α U hU2 l hl y, hlν, smul_smul]
  have hAfun : fractionalPowerAt α (fun x => c • U (l • x)) =
      fun y => (c * ν) • fractionalPowerAt α U (l • y) := funext hA
  have hm : 0 < min 1 l := lt_min one_pos hl
  refine ⟨one_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (h.smooth.comp (contDiff_const_smul l)).const_smul c
  · exact contDiff_const.mul (h.smooth_pressure.comp (contDiff_const_smul l))
  · rw [hAfun]
    exact (h.smooth_power.comp (contDiff_const_smul l)).const_smul _
  · intro y
    have hadv : advectionAt (fun x => c • U (l • x)) y = c • advectionAt U (l • y) := by
      unfold advectionAt
      rw [hDU, map_smul]
    have hgrad : gradientAt (fun x => d * P (l • x)) y = c • gradientAt P (l • y) := by
      unfold gradientAt
      rw [hDP, Finset.smul_sum]
      simp [smul_smul]
    have e1 : fderiv ℝ U (l • y) y = c • fderiv ℝ U (l • y) (l • y) := by
      rw [map_smul, smul_smul, hcl, one_smul]
    have e2 : fderiv ℝ U (l • y) (axialTurn y) =
        c • fderiv ℝ U (l • y) (axialTurn (l • y)) := by
      rw [axialTurn_smul, map_smul, smul_smul, hcl, one_smul]
    have e3 : axialTurn (c • U (l • y)) = c • axialTurn (U (l • y)) := axialTurn_smul c _
    calc rotatingProfileResidual α a 1 (fun x => c • U (l • x)) (fun x => d * P (l • x)) y
        = c • rotatingProfileResidual α a ν U P (l • y) := by
          unfold rotatingProfileResidual
          rw [hadv, hgrad, hA, hDU, e1, e2, e3]
          module
      _ = 0 := by rw [h.residual, smul_zero]
  · intro y
    unfold divergenceAt
    rw [hDU]
    exact h.div (l • y)
  · obtain ⟨y₀, hy₀⟩ := h.nonzero
    refine ⟨l⁻¹ • y₀, ?_⟩
    have hc : c ≠ 0 := by
      rintro rfl
      simp at hcl
    simp only [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
    exact smul_ne_zero hc hy₀
  · intro j
    obtain ⟨C, hC⟩ := h.decay j
    have hC0 : 0 ≤ C := by
      have h0 := (hC 0).1
      simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h0
      exact (norm_nonneg _).trans h0
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have e₁ : 0 ≤ 2 * α - 1 + j := by linarith
    have e₂ : 0 ≤ 4 * α - 1 + j := by linarith
    set K₁ := |c| * |l| ^ j * (min 1 l) ^ (-(2 * α - 1 + j))
    set K₂ := |d| * |l| ^ (j + 1) * (min 1 l) ^ (-(4 * α - 1 + j))
    set K₃ := |c * ν| * |l| ^ j * (min 1 l) ^ (-(4 * α - 1 + j))
    have hK₁ : 0 ≤ K₁ := by positivity
    have hK₂ : 0 ≤ K₂ := by positivity
    have hK₃ : 0 ≤ K₃ := by positivity
    refine ⟨C * (K₁ + K₂ + K₃), fun y => ⟨?_, ?_, ?_⟩⟩
    · rw [norm_iteratedFDeriv_scaled U h.smooth]
      have hb := (hC (l • y)).1
      have hq := decay_scaled l hl _ e₁ y
      have hp : 0 ≤ (1 + ‖y‖) ^ (-(2 * α - 1 + j)) := by positivity
      calc |c| * |l| ^ j * ‖iteratedFDeriv ℝ j U (l • y)‖
          ≤ |c| * |l| ^ j * (C * ((min 1 l) ^ (-(2 * α - 1 + j)) *
              (1 + ‖y‖) ^ (-(2 * α - 1 + j)))) := by
            gcongr
            exact hb.trans (mul_le_mul_of_nonneg_left hq hC0)
        _ = C * K₁ * (1 + ‖y‖) ^ (-(2 * α - 1 + j)) := by ring
        _ ≤ C * (K₁ + K₂ + K₃) * (1 + ‖y‖) ^ (-(2 * α - 1 + j)) := by
            gcongr
            linarith
    · rw [hPfun, norm_iteratedFDeriv_scaled P h.smooth_pressure]
      have hb := (hC (l • y)).2.1
      have hq := decay_scaled l hl _ e₂ y
      have hp : 0 ≤ (1 + ‖y‖) ^ (-(4 * α - 1 + j)) := by positivity
      calc |d| * |l| ^ (j + 1) * ‖iteratedFDeriv ℝ (j + 1) P (l • y)‖
          ≤ |d| * |l| ^ (j + 1) * (C * ((min 1 l) ^ (-(4 * α - 1 + j)) *
              (1 + ‖y‖) ^ (-(4 * α - 1 + j)))) := by
            gcongr
            exact hb.trans (mul_le_mul_of_nonneg_left hq hC0)
        _ = C * K₂ * (1 + ‖y‖) ^ (-(4 * α - 1 + j)) := by ring
        _ ≤ C * (K₁ + K₂ + K₃) * (1 + ‖y‖) ^ (-(4 * α - 1 + j)) := by
            gcongr
            linarith
    · rw [hAfun, norm_iteratedFDeriv_scaled _ h.smooth_power]
      have hb := (hC (l • y)).2.2
      have hq := decay_scaled l hl _ e₂ y
      have hp : 0 ≤ (1 + ‖y‖) ^ (-(4 * α - 1 + j)) := by positivity
      calc |c * ν| * |l| ^ j * ‖iteratedFDeriv ℝ j (fractionalPowerAt α U) (l • y)‖
          ≤ |c * ν| * |l| ^ j * (C * ((min 1 l) ^ (-(4 * α - 1 + j)) *
              (1 + ‖y‖) ^ (-(4 * α - 1 + j)))) := by
            gcongr
            exact hb.trans (mul_le_mul_of_nonneg_left hq hC0)
        _ = C * K₃ * (1 + ‖y‖) ^ (-(4 * α - 1 + j)) := by ring
        _ ≤ C * (K₁ + K₂ + K₃) * (1 + ‖y‖) ^ (-(4 * α - 1 + j)) := by
            gcongr
            linarith

end FracInternal

theorem unitViscosity : UnitViscosity := by
  intro α hα _ a ν U P h
  have hν := h.pos
  have hα0 : (2 * α) ≠ 0 := by positivity
  have hl : 0 < ν ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hν _
  refine FracInternal.profile_scaled α a ν hα U P h (ν ^ (1 / (2 * α))) (ν ^ (-(1 / (2 * α))))
    (ν ^ (-(1 / α))) hl ?_ ?_ ?_
  · rw [← Real.rpow_add hν]
    simp
  · rw [← Real.rpow_add hν]
    congr 1
    field_simp
    ring
  · rw [← Real.rpow_mul hν.le]
    rw [show 1 / (2 * α) * (2 * α) = 1 by field_simp, Real.rpow_one]

end Breakdown
