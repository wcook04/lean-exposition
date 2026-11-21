import Breakdown.Uniqueness.RegPhysAux

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem isSolutionOn_physField {T : ℝ} (hT : 0 < T) {F : ℝ → Space → CSpace}
    (hF : ∀ m, IsHsCurve m F 0 T) (hd : IsVarConstSymbol F 0 T)
    (hs : ∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) :
    IsSolutionOn T (fun t => physField (F t)) (fun t => physScalar (pressureSymbol (F t))) := by
  refine ⟨smooth_physField_curve hT hF hd hs, smooth_pressure_curve hT hF hd hs, ?_, ?_⟩
  · intro t ht x
    have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
    obtain ⟨h1, h2, h3, h4⟩ := integrable_symbols_curve hT hF hd hs htc
    rw [(hasDerivAt_physField_curve hT hF hd hs ht x).deriv, advectionAt_physField_curve hF hs htc x,
      sumSecondPartialsAt_physField_curve hF htc x, gradientAt_pressure_curve hT hF hd hs htc x,
      ← physField_add h1 h2, ← physField_sub h3 h4]
    congr 1
    funext ξ
    exact timeDerivSymbol_add_advectionSymbol _ ξ
  · intro t ht x
    exact divergenceAt_physField_curve hF hs ht x

end Breakdown.SmoothFlow
