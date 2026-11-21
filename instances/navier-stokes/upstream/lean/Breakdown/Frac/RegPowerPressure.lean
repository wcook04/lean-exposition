import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegPhysAuxPressure

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem powerPressureCurve_of (α : ℝ) (hα : 1 < α) (h1 : PowerWeightCurveStatement α) :
    PowerPressureCurveStatement α := by
  intro T hT F hF hd hs k n
  obtain ⟨B, hB⟩ := exists_bilin_pressureSingle k
  have hmem : ∀ t ∈ Icc 0 T, MemLp (F t) 1 (weightL1Measure k) := fun t ht =>
    memLp_weight_of_curve hF ht k
  have hc := (h1 T hT F hF hd hs).2 k n
  refine ContDiffOn.congr (B.isBoundedBilinearMap.contDiff.comp_contDiffOn (hc.prodMk hc)) ?_
  intro t ht
  have hp : MemLp (fun ξ => pressureSymbol (F t) ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) 1
      (weightL1Measure k) :=
    memLp_pressureSymbol_single (fun m => memLp_weight_of_curve hF ht m) (hs t ht) k
  obtain ⟨h, hh⟩ := hB (F t) (F t) (hmem t ht) (hmem t ht)
  have hh' : B ((hmem t ht).toLp (F t)) ((hmem t ht).toLp (F t)) = h.toLp _ := hh
  show toWeightL1 k _ = B (toWeightL1 k (F t)) (toWeightL1 k (F t))
  unfold toWeightL1
  rw [dif_pos hp, dif_pos (hmem t ht)]
  have hae : (fun ξ => pressureSymbol (F t) ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ))
      =ᵐ[weightL1Measure k]
      (fun ξ => pressureBilinSymbol (F t) (F t) ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) := by
    refine (PressureSingle.Internal.weighted_ac k).ae_le ?_
    filter_upwards [PressureSingle.Internal.pressureSymbol_ae_eq
      (memLp_weight_of_curve hF ht 1) (hs t ht)] with ξ hξ
    rw [hξ]
  exact (MemLp.toLp_congr hp h hae).trans hh'.symm

end Breakdown.SmoothFlow
