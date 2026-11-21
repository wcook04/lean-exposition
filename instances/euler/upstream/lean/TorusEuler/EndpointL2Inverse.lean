import TorusEuler.EndpointL2Coercivity
import TorusEuler.EndpointPrimitiveAdjoint
import TorusEuler.ProjectedHilbertInverse

open MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "TimeL2" T => Lp E 2 (volume.restrict (Ioc (0 : ℝ) T))

/-- The operator from (4.9) at a fixed label, before projection onto paths of zero time mean. -/
noncomputable def endpointL2Operator {T : ℝ} (hT : 0 ≤ T) (F M : ℝ → E →L[ℝ] E)
    (cF : ContinuousOn F (Icc 0 T)) (cM : ContinuousOn M (Icc 0 T)) :
    (TimeL2 T) →L[ℝ] (TimeL2 T) :=
  (endpointTimeMultiplier F cF).adjoint.comp (endpointTimeMultiplier F cF) -
    (endpointPrimitiveLp hT).comp (endpointTimeMultiplier (fun t => endpointSkew (F t) (M t))
      (continuousOn_endpointSkew cF cM))

theorem inner_endpointL2Operator_self {T : ℝ} (hT : 0 ≤ T) (F M : ℝ → E →L[ℝ] E)
    (cF : ContinuousOn F (Icc 0 T)) (cM : ContinuousOn M (Icc 0 T))
    (v : TimeL2 T) (hv : endpointIntegral T v = 0) :
    ⟪endpointL2Operator hT F M cF cM v, v⟫_ℝ = endpointL2Energy hT F M cF cM v := by
  unfold endpointL2Operator endpointL2Energy
  rw [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, inner_sub_left,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    endpointPrimitiveLp_inner_eq_neg_inner hT _ v hv, sub_neg_eq_add]

/-- The time-projected weak equation at one label has a unique solution.
    The spatial divergence-free constraint is part of the torus inverse. -/
theorem exists_endpointLabelL2Solution {T D L : ℝ} {F G M Mt : ℝ → E →L[ℝ] E}
    (hT : 0 < T) (hT1 : T ≤ 1) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (cF : ContinuousOn F (Icc 0 T)) (cM : ContinuousOn M (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (hM : ∀ t ∈ Icc 0 T, HasDerivWithinAt M (Mt t) (Icc 0 T) t)
    (hMt : ContinuousOn Mt (Icc 0 T))
    (hGF : ∀ t ∈ Icc 0 T, (G t).comp (F t) = ContinuousLinearMap.id ℝ E)
    (hGbound : ∀ t ∈ Icc 0 T, ‖G t‖ ≤ D) (hMbound : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ L)
    (hupper : ∀ t ∈ Icc 0 T, ∀ x : E, ⟪endpointHessian (M t) (Mt t) x, x⟫_ℝ ≤ ‖x‖ ^ 2)
    (f : TimeL2 T) :
    let H := (endpointIntegral (E := E) T).ker
    let A := endpointL2Operator hT.le F M cF cM
    let c : ℝ := 1 / (2 * D ^ 2 * (1 + L) ^ 2)
    ∃ v : H, (∀ w : H, ⟪A (v : TimeL2 T), (w : TimeL2 T)⟫_ℝ = ⟪f, (w : TimeL2 T)⟫_ℝ) ∧
      ‖v‖ ≤ ‖f‖ / c ∧
      ∀ u : H, (∀ w : H, ⟪A (u : TimeL2 T), (w : TimeL2 T)⟫_ℝ = ⟪f, (w : TimeL2 T)⟫_ℝ) → u = v := by
  dsimp only
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  apply exists_projectedHilbertSolution _ (endpointIntegral T).isClosed_ker _ (by positivity)
  intro v
  rw [inner_endpointL2Operator_self _ _ _ _ _ _ v.property]
  exact endpointL2Energy_coercive hT hT1 hD hL cF cM hF hM hMt hGF hGbound hMbound hupper v v.property

end TorusEuler
