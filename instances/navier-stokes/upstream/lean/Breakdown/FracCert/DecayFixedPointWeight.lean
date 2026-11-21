import Breakdown.FracCert.WeakRegular
import Breakdown.FracCert.WeakSymbolL1
import Breakdown.FracCert.InverseSquare
import Breakdown.Weak.VelocityWeakGradient

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow Breakdown.SteadyCert

namespace DecayWeightInternal

def gradOf (U : X) (y : Space) : Space →L[ℝ] Space :=
  ∑ j : Fin 3, ContinuousLinearMap.smulRightL ℝ Space Space (EuclideanSpace.proj (𝕜 := ℝ) j)
    ((partialX j U : Space → Space) y)

theorem gradOf_apply (U : X) (y : Space) (j : Fin 3) :
    gradOf U y (unitVector j) = (partialX j U : Space → Space) y := by
  simp [gradOf, unitVector, PiLp.single_apply]

theorem gradOf_aesm (U : X) : AEStronglyMeasurable (gradOf U) volume := by
  have t : ∀ j : Fin 3, AEStronglyMeasurable (fun y => ContinuousLinearMap.smulRightL ℝ Space Space
      (EuclideanSpace.proj (𝕜 := ℝ) j) ((partialX j U : Space → Space) y)) volume := fun j =>
    (ContinuousLinearMap.smulRightL ℝ Space Space (EuclideanSpace.proj (𝕜 := ℝ) j)).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable _)
  have e : gradOf U = fun y => ContinuousLinearMap.smulRightL ℝ Space Space (EuclideanSpace.proj (𝕜 := ℝ) 0)
      ((partialX 0 U : Space → Space) y) + ContinuousLinearMap.smulRightL ℝ Space Space
      (EuclideanSpace.proj (𝕜 := ℝ) 1) ((partialX 1 U : Space → Space) y) +
      ContinuousLinearMap.smulRightL ℝ Space Space (EuclideanSpace.proj (𝕜 := ℝ) 2)
      ((partialX 2 U : Space → Space) y) := by
    funext y
    simp only [gradOf, Fin.sum_univ_three]
  rw [e]
  exact ((t 0).add (t 1)).add (t 2)

theorem gradOf_entrySq (U : X) : Integrable (fun y => entrySq (gradOf U y)) := by
  have t : ∀ i : Fin 3, Integrable (fun y => ‖(partialX i U : Space → Space) y‖ ^ 2) := fun i =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  have e : (fun y => entrySq (gradOf U y)) = fun y => ∑ i : Fin 3, ‖(partialX i U : Space → Space) y‖ ^ 2 := by
    funext y
    simp only [entrySq, gradOf_apply]
  rw [e]
  exact integrable_finsetSum _ fun i _ => t i

theorem gradOf_weak (U : X) : IsWeakGradientOf (velocity U : Space → Space) (gradOf U) := by
  intro φ hφ j
  have h := WeakProfile.velocityWeakGradient_holds U φ hφ j
  simp_rw [gradOf_apply]
  rw [h, neg_neg]

end DecayWeightInternal

open DecayWeightInternal in
theorem profileInverseWeight : VelocityInverseWeightStatement := by
  intro U hM
  have hv6 : MemLp (velocity U : Space → Space) 6 volume := Lp.memLp _
  obtain ⟨hI, -⟩ := inverseSquareBound _ (gradOf U) (Lp.aestronglyMeasurable _) hv6 (gradOf_entrySq U)
    (gradOf_weak U)
  have hae : physField (symbolX U) =ᵐ[volume] (velocity U : Space → Space) := ((symbolL1OfMoments U hM).2).symm
  have hc : Continuous (physField (symbolX U)) := by
    have h0 := (symbolL1OfMoments U hM).1 0
    simp only [pow_zero, one_mul] at h0
    exact WeakRegularInternal.continuous_physField_of
      ((integrable_norm_iff (WeakRegularInternal.aesm_symbolX U)).1 h0)
  have hcs : Continuous (fun y : Space => (1 + ‖y‖)⁻¹ • physField (symbolX U) y) :=
    ((continuous_const.add continuous_norm : Continuous fun y : Space => (1 : ℝ) + ‖y‖).inv₀
      (fun y => (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)).ne')).smul hc
  rw [memLp_two_iff_integrable_sq_norm hcs.aestronglyMeasurable]
  have h0 : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]
    simp
  refine hI.mono' (hcs.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [hae, h0] with y hy hy0
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy0
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_smul, norm_inv,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖y‖), hy, mul_pow, inv_pow, ← div_eq_inv_mul]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ hy'.le (by linarith) 2)

end Breakdown.FracCert
