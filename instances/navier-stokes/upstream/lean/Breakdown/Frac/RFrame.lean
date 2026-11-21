import Breakdown.Frac.StRealize
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Freq

theorem fracBilinX_symm (α τ : ℝ) (u v : X) : fracBilinX α τ u v = fracBilinX α τ v u := by
  unfold fracBilinX
  split_ifs with h
  · apply ext_inner_right ℝ
    intro ψ
    rw [h.2.choose_spec u v ψ, h.2.choose_spec v u ψ]
    unfold fracBilinForm
    ring
  · rfl

theorem fracBilinX_opNorm_le (α : ℝ) (hα : 1 < α) (hB : FracBilinBound α) (τ : ℝ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) : ‖fracBilinX α τ‖ ≤ hB.choose * τ ^ (-(3 / 4 : ℝ)) := by
  have hC := hB.choose_spec.1
  have h1 : ‖fracBilinX α τ‖ ≤ hB.choose * τ ^ (-(3 / (4 * α))) :=
    ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg hC (Real.rpow_nonneg hτ.le _))
      (hB.choose_spec.2 τ hτ)
  have hexp : -(3 / 4 : ℝ) ≤ -(3 / (4 * α)) := by
    have h4 : (0 : ℝ) < 4 := by norm_num
    have : 3 / (4 * α) ≤ 3 / 4 := by
      apply div_le_div_of_nonneg_left (by norm_num) h4
      linarith
    linarith
  have h2 : τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hτ hτ1 hexp
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hC)

def fracFrameOf (α : ℝ) (hα : 1 < α) (hH : FracHeatSemigroup α) (hD : FracDilationAlgebra α)
    (hDc : FracDilationContinuous α) (hB : FracBilinBound α) (hBc : FracBilinContinuous α)
    (hBs : FracBilinShift α) (hBd : FracBilinDilate α) (hK : FracBilinCompact α) :
    ScaledMildFramework X (dilExponent α) where
  G := fracHeatX α
  G_zero := hH.1
  G_add := hH.2.1
  G_norm := hH.2.2.1
  G_cont := hH.2.2.2.1
  K := fracBilinX α
  K_symm := fracBilinX_symm α
  CK := hB.choose
  K_bound := fun τ hτ hτ1 => fracBilinX_opNorm_le α hα hB τ hτ hτ1
  K_cont := hBc
  K_shift := hBs
  D := fracDilX α
  D_norm := hD.1
  D_one := hD.2.1
  D_mul := hD.2.2.1
  D_cont := hDc
  D_G := hD.2.2.2.1
  D_K := hBd
  compact := ⟨testSpan, testDense_holds.2, hK⟩

theorem fracFramework_of (α : ℝ) (hα : 1 < α) (hH : FracHeatSemigroup α)
    (hD : FracDilationAlgebra α) (hDc : FracDilationContinuous α) (hE : FracBilinExists α)
    (hB : FracBilinBound α) (hBc : FracBilinContinuous α) (hBs : FracBilinShift α)
    (hBd : FracBilinDilate α) (hK : FracBilinCompact α) (hR : FracRotationAlgebra α)
    (hBr : FracBilinRotate α) : FracFrameworkSpec α ∧ FracCommutes α := by
  refine ⟨⟨fracFrameOf α hα hH hD hDc hB hBc hBs hBd hK, rfl, rfl, rfl⟩, ?_⟩
  intro F hG hKF hDF R
  obtain ⟨G, _, _, _, _, K, _, _, _, _, _, D, _, _, _, _, _, _, _⟩ := F
  subst hG hKF hDF
  exact ⟨(hR R).1, hBr R, (hR R).2⟩

end Breakdown.Freq
