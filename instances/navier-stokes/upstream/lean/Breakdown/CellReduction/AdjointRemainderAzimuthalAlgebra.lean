import Breakdown.CellReduction.AdjointRemainderAzimuthalParts
import Breakdown.CellReduction.AdjointEntryDefs

open scoped ENNReal ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace AzimuthalParts

namespace Internal

open CellCert.Reduction

def componentMap (c : Fin 3) : Space →L[ℝ] Space :=
  if c = 0 then
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 0)
      + (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 1)
  else if c = 1 then
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 0)
      - (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 1)
  else (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 0)

theorem componentMap_coords (c : Fin 3) (x : Space) :
    (componentMap c x) 0 = (if c = 2 then x 2 else x 0) ∧
      (componentMap c x) 1 = (if c = 0 then x 1 else if c = 1 then -x 1 else 0) ∧
      (componentMap c x) 2 = 0 := by
  fin_cases c <;> simp [componentMap, unitVector]

theorem horizontal_componentMap (c : Fin 3) (W : Space → Space) :
    horizontalPart (fun y => componentMap c (W y)) = fun y => complexComponent c (W y) := by
  funext y
  obtain ⟨h0, h1, -⟩ := componentMap_coords c (W y)
  simp only [horizontalPart, h0, h1]
  fin_cases c <;> simp [complexComponent] <;> ring

theorem componentMap_norm_sq (c : Fin 3) (x : Space) :
    ‖componentMap c x‖ ^ 2 = ‖complexComponent c x‖ ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := componentMap_coords c x
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, h0, h1, h2, Complex.sq_norm]
  fin_cases c <;> simp [complexComponent, Complex.normSq_apply] <;> ring

theorem weighted_norm_sq (x : Space) :
    ∑ c : Fin 3, componentWeight c * ‖componentMap c x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [componentMap_norm_sq]
  simp [complexComponent, componentWeight, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem weighted_squareSum (M : Space →L[ℝ] Space) :
    ∑ c : Fin 3, componentWeight c * matSq ((componentMap c).comp M) = matSq M := by
  unfold matSq
  simp only [ContinuousLinearMap.comp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => weighted_norm_sq _

theorem inner_components (x r : Space) :
    inner ℝ x r = ∑ c : Fin 3, componentWeight c *
      (starRingEnd ℂ (complexComponent c x) * complexComponent c r).re := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, complexComponent, componentWeight, Complex.mul_re]
  ring

theorem locallyIntegrable_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : Space → E}
    (hf : LocallyIntegrable f volume) : LocallyIntegrable (fun y => L (f y)) volume := by
  rw [locallyIntegrable_iff] at hf ⊢
  exact fun k hk => L.integrable_comp (hf k hk)

theorem weakGradient_comp (L : Space →L[ℝ] Space) {V : Space → Space}
    {D : Space → (Space →L[ℝ] Space)} (h : IsWeakGradient V D) :
    IsWeakGradient (fun y => L (V y)) (fun y => L.comp (D y)) := by
  obtain ⟨hV, hD, hI⟩ := h
  refine ⟨locallyIntegrable_clm L hV, locallyIntegrable_clm (ContinuousLinearMap.compL ℝ Space Space Space L) hD,
    fun φ hφ i => ?_⟩
  have hDi : LocallyIntegrable (fun y => D y (unitVector i)) volume :=
    locallyIntegrable_clm (ContinuousLinearMap.apply ℝ Space (unitVector i)) hD
  have i1 : Integrable (fun y => φ y • D y (unitVector i)) volume :=
    hDi.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have hdφ : Continuous (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsφ : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφ.2.fderiv ℝ).comp_left (g := fun M : Space →L[ℝ] ℝ => M (unitVector i)) (by simp)
  have i2 : Integrable (fun y => fderiv ℝ φ y (unitVector i) • V y) volume :=
    hV.integrable_smul_left_of_hasCompactSupport hdφ hsφ
  have e1 : (fun y => φ y • (L.comp (D y)) (unitVector i)) = fun y => L (φ y • D y (unitVector i)) := by
    funext y
    simp
  have e2 : (fun y => fderiv ℝ φ y (unitVector i) • L (V y)) = fun y => L (fderiv ℝ φ y (unitVector i) • V y) := by
    funext y
    simp
  rw [e1, e2, L.integral_comp_comm i1, L.integral_comp_comm i2, hI φ hφ i, map_neg]

theorem ringPoint_rotation (ρ θ z : ℝ) : axisRotation θ (ringPoint ρ 0 z) = ringPoint ρ θ z := by
  ext i
  fin_cases i <;> simp [axisRotation, ringPoint, unitVector] <;> ring

end Internal

end AzimuthalParts

end AdjointDefect

end Breakdown
