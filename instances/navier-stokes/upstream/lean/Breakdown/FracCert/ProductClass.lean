import Breakdown.FracCert.LinearSolveCore
import Breakdown.FracCert.HeldLimit

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace ProductClassInternal

theorem equivariant_everywhere {W : Space → Space} (hW : Continuous W) (L : Space ≃ₗᵢ[ℝ] Space)
    (h : ∀ᵐ y ∂volume, W (L y) = L (W y)) : ∀ y, W (L y) = L (W y) := by
  have hc1 : Continuous (fun y => W (L y)) := hW.comp L.continuous
  have hc2 : Continuous (fun y => L (W y)) := L.continuous.comp hW
  have he : (fun y => W (L y)) = fun y => L (W y) := (hc1.ae_eq_iff_eq volume hc2).1 h
  exact fun y => congrFun he y

theorem deriv_equivariant {W : Space → Space} (hW : ContDiff ℝ 1 W) (L : Space ≃ₗᵢ[ℝ] Space)
    (h : ∀ y, W (L y) = L (W y)) (y w : Space) :
    fderiv ℝ W (L y) (L w) = L (fderiv ℝ W y w) := by
  have hd : Differentiable ℝ W := hW.differentiable one_ne_zero
  have h1 : HasFDerivAt (fun z => W (L z))
      ((fderiv ℝ W (L y)).comp (L.toContinuousLinearEquiv : Space →L[ℝ] Space)) y :=
    (hd (L y)).hasFDerivAt.comp y L.toContinuousLinearEquiv.hasFDerivAt
  have h2 : HasFDerivAt (fun z => L (W z))
      ((L.toContinuousLinearEquiv : Space →L[ℝ] Space).comp (fderiv ℝ W y)) y :=
    L.toContinuousLinearEquiv.hasFDerivAt.comp y (hd y).hasFDerivAt
  have hf : (fun z => W (L z)) = fun z => L (W z) := funext h
  rw [hf] at h1
  have := congrArg (fun T : Space →L[ℝ] Space => T w) (h1.unique h2)
  simpa using this

theorem product_at (W v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (L : Space ≃ₗᵢ[ℝ] Space) (y : Space) (hWy : W (L y) = L (W y)) (hv : v (L y) = L (v y))
    (hG : ∀ w, G (L y) (L w) = L (G y w)) (hD : ∀ w, fderiv ℝ W (L y) (L w) = L (fderiv ℝ W y w)) :
    symProduct W (fun z => fderiv ℝ W z) v G (L y) = L (symProduct W (fun z => fderiv ℝ W z) v G y) := by
  simp only [symProduct, hWy, hv, hG, hD, map_smul, map_add]

theorem turn_coe (m : ℕ) : ⇑(LinearSolveCore.turnStepIsometry m) = turnStep m := rfl

theorem mirror_coe : ⇑LinearSolveCore.mirrorIsometry = mirror := rfl

end ProductClassInternal

open ProductClassInternal

theorem productClass : ProductClassStatement := by
  intro m W v G H hW hWc hs
  obtain ⟨hGt, hGm⟩ := gradientClass_holds m v G hs.measurable_velocity hs.velocity_six
    hs.measurable_gradient hs.gradient_two hs.weak_gradient hs.symmetric
  have hWt := equivariant_everywhere hW.continuous (LinearSolveCore.turnStepIsometry m)
    (by simpa only [turn_coe] using hWc.1)
  have hWm := equivariant_everywhere hW.continuous LinearSolveCore.mirrorIsometry
    (by simpa only [mirror_coe] using hWc.2)
  have hDt := deriv_equivariant hW _ hWt
  have hDm := deriv_equivariant hW _ hWm
  simp only [turn_coe] at hWt hDt
  simp only [mirror_coe] at hWm hDm
  constructor
  · filter_upwards [hs.symmetric.1, hGt] with y hv hG
    have := product_at W v G (LinearSolveCore.turnStepIsometry m) y
    simp only [turn_coe] at this
    exact this (hWt y) hv hG (hDt y)
  · filter_upwards [hs.symmetric.2, hGm] with y hv hG
    have := product_at W v G LinearSolveCore.mirrorIsometry y
    simp only [mirror_coe] at this
    exact this (hWm y) hv hG (hDm y)

end SteadyCert

end Breakdown
