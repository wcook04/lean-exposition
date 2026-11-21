import Breakdown.Uniqueness.RegLocalAuxFix

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem exists_local_varConst (m : ℕ) (hm : 3 ≤ m) (R : ℝ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ (a : ℝ) (F₀ : Space → CSpace), AEStronglyMeasurable F₀ volume → IsSolenoidalSymbol F₀ →
      hsNormSq m F₀ ≤ ENNReal.ofReal R →
      ∃ F : ℝ → Space → CSpace, F a = F₀ ∧ IsHsCurve m F a (a + δ) ∧
        IsVarConstSymbol F a (a + δ) ∧ ∀ t ∈ Icc a (a + δ), IsSolenoidalSymbol (F t) := by
  obtain ⟨δ, hδ, hfix⟩ := exists_varConst_fixedPoint m hm R
  refine ⟨δ, hδ, fun a F₀ hmeas hsol hR => ?_⟩
  obtain ⟨G, hGc, hGfix, hGconj⟩ := hfix a F₀ hmeas hsol hR
  have hFG : ∀ t ∈ Icc a (a + δ), varConstMap a F₀ G t =ᵐ[volume] G t :=
    fun t ht => (hGfix t ht).symm
  have hsub : ∀ t ∈ Icc a (a + δ), ∀ s ∈ uIcc a t, s ∈ Icc a (a + δ) := by
    intro t ht s hs
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  refine ⟨varConstMap a F₀ G, varConstMap_self a F₀ G, isHsCurve_congr hGc hFG, ?_, ?_⟩
  · intro t ht ξ
    rw [varConstMap_self a F₀ G]
    conv_lhs => rw [varConstMap]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [nonlinSymbol_congr_ae (hFG s (hsub t ht s hs))]
  · intro t ht
    exact varConstMap_solenoidal hsol fun s hs => hGconj s (hsub t ht s hs)

end Breakdown.SmoothFlow
