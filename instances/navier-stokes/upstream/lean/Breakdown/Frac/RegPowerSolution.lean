import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegPhysAuxProduct

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem physField_neg_apply (g : Space → CSpace) (x : Space) :
    physField (fun ξ => -g ξ) x = -physField g x := by
  simp only [physField, Real.fourierInv_eq, smul_neg, integral_neg, map_neg]

private theorem nonlin_add_advection (f : Space → CSpace) (ξ : Space) :
    nonlinSymbol f ξ + advectionSymbol f ξ = -gradPressureSymbol f ξ := by
  have h := timeDerivSymbol_add_advectionSymbol f ξ
  simp only [timeDerivSymbol, sspSymbol] at h
  rw [add_assoc, sub_eq_add_neg] at h
  exact add_left_cancel h

private theorem powerTimeDeriv_add_advection_add_power (α : ℝ) (f : Space → CSpace) (ξ : Space) :
    powerTimeDerivSymbol α f ξ + advectionSymbol f ξ + powerSymbol α f ξ =
      -gradPressureSymbol f ξ := by
  simp only [powerTimeDerivSymbol]
  rw [add_assoc (-powerSymbol α f ξ), nonlin_add_advection]
  abel

theorem powerSolutionOn_of (α : ℝ) (_hα : 1 < α) (h1 : PowerPhysCurveStatement α) :
    PowerSolutionOnStatement α := by
  intro T hT F hF hd hs
  obtain ⟨hsv, hsp, hder, hint, hpow, hgrad⟩ := h1 T hT F hF hd hs
  refine ⟨hsv, hsp, ?_, ?_⟩
  · intro t ht x
    have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
    obtain ⟨i1, i2, i3, _⟩ := hint t htc
    rw [(hder t ht x).deriv, advectionAt_physField (fun k => memLp_weight_of_curve hF htc k) (hs t htc) x,
      hpow t htc x, hgrad t htc x, ← physField_add i1 i2, ← physField_add (f := fun ξ => powerTimeDerivSymbol α (F t) ξ + advectionSymbol (F t) ξ) (i1.add i2) i3,
      ← physField_neg_apply]
    congr 1
    funext ξ
    exact powerTimeDeriv_add_advection_add_power α (F t) ξ
  · intro t ht x
    exact divergenceAt_physField (memLp_weight_of_curve hF ht 1) (fun ξ => ((hs t ht) ξ).1) x

end Breakdown.SmoothFlow
