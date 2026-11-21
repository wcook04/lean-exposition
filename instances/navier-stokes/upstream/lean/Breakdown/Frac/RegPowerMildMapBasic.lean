import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegLocalAuxSymm

open scoped ContDiff ENNReal FourierTransform Topology ComplexConjugate
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace PowerInternal

private theorem conjVec_apply' (z : CSpace) (i : Fin 3) : conjVec z i = star (z i) := rfl

private theorem freqVec_apply' (ξ : Space) (i : Fin 3) : freqVec ξ i = ((ξ i : ℝ) : ℂ) := rfl

private def conjVecIsom : CSpace →ₗᵢ[ℝ] CSpace where
  toLinearMap := conjVec.toLinearMap
  norm_map' z := by
    simp only [ContinuousLinearMap.coe_coe, EuclideanSpace.norm_eq, conjVec_apply', norm_star]

private theorem inner_freqVec' (ξ : Space) (w : CSpace) :
    inner ℂ (freqVec ξ) w = ∑ i, ((ξ i : ℝ) : ℂ) * w i := by
  simp [PiLp.inner_apply, freqVec_apply', Complex.conj_ofReal, mul_comm]

private theorem powerHeatSymbol_neg (α τ : ℝ) (ξ : Space) :
    powerHeatSymbol α τ (-ξ) = powerHeatSymbol α τ ξ := by
  simp only [powerHeatSymbol, norm_neg]

end PowerInternal

open PowerInternal

theorem powerMildMap_self (α a : ℝ) (F₀ : Space → CSpace) (G : ℝ → Space → CSpace) :
    powerMildMap α a F₀ G a = F₀ := by
  funext ξ
  simp [powerMildMap, powerHeatSymbol]

theorem powerMildMap_solenoidal (α : ℝ) {a : ℝ} {F₀ : Space → CSpace} {G : ℝ → Space → CSpace}
    {t : ℝ} (h0 : IsSolenoidalSymbol F₀)
    (hG : ∀ s ∈ uIcc a t, ∀ᵐ η ∂volume, G s (-η) = conjVec (G s η)) :
    IsSolenoidalSymbol (powerMildMap α a F₀ G t) := by
  have hr : ∀ r : ℝ, star ((r : ℂ)) = r := fun r => Complex.conj_ofReal r
  intro ξ
  constructor
  · rw [← inner_freqVec']
    simp only [powerMildMap, inner_add_right, inner_smul_right]
    rw [inner_freqVec', (h0 ξ).1, mul_zero, zero_add]
    by_cases hi : IntervalIntegrable
        (fun s => ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (G s) ξ) volume a t
    · have hc := (innerSL ℂ (freqVec ξ)).intervalIntegral_comp_comm hi
      change (innerSL ℂ (freqVec ξ)) _ = 0
      rw [← hc]
      simp [inner_freqVec', nonlinSymbol_div]
    · rw [intervalIntegral.integral_undef hi, inner_zero_right]
  · simp only [powerMildMap, powerHeatSymbol_neg, map_add]
    congr 1
    · rw [(h0 ξ).2]
      ext i
      simp only [conjVec_apply', PiLp.smul_apply, smul_eq_mul, star_mul', hr]
    · have : ∀ s ∈ uIcc a t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) •
          nonlinSymbol (G s) (-ξ) = conjVecIsom (((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) •
          nonlinSymbol (G s) ξ) := by
        intro s hs
        rw [nonlinSymbol_neg (hG s hs)]
        ext i
        change _ = conjVec _ i
        simp only [conjVec_apply', PiLp.smul_apply, smul_eq_mul, star_mul', hr]
      rw [intervalIntegral.integral_congr this, LinearIsometry.intervalIntegral_comp_comm]
      rfl

theorem powerMildMapBasic (α : ℝ) : PowerMildMapBasicStatement α :=
  ⟨powerMildMap_self α, fun _ _ _ _ h0 hG => powerMildMap_solenoidal α h0 hG⟩

end Breakdown.SmoothFlow
