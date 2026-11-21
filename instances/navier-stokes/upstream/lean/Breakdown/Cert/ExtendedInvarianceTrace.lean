import Breakdown.Cert.Invariance
import Breakdown.Cert.ProductPairing
import Breakdown.Cert.CoerciveModeDerivative

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

namespace Internal.ExtendedInvarianceTrace

open Internal.Invariance

theorem coord_rot_eq (R : Space ≃ₗᵢ[ℝ] Space) (j k : Fin 3) :
    (R (unitVector j)) k = (R.symm (unitVector k)) j := by
  have e1 : (R (unitVector j)) k = inner ℝ (unitVector k) (R (unitVector j)) := by
    simp [unitVector, EuclideanSpace.inner_single_left]
  have e2 : (R.symm (unitVector k)) j = inner ℝ (unitVector j) (R.symm (unitVector k)) := by
    simp [unitVector, EuclideanSpace.inner_single_left]
  rw [e1, e2, ← R.symm.inner_map_map (unitVector k) (R (unitVector j)),
    LinearIsometryEquiv.symm_apply_apply, real_inner_comm]

theorem sum_coord_rot_mul (R : Space ≃ₗᵢ[ℝ] Space) (k l : Fin 3) :
    ∑ j : Fin 3, (R (unitVector j)) k * (R (unitVector j)) l = if k = l then 1 else 0 := by
  simp only [coord_rot_eq R]
  rw [sum_coord_rot R.symm (unitVector k) l]
  by_cases h : k = l
  · subst h; simp [unitVector]
  · simp [unitVector, h, Ne.symm h]

theorem bilin_expand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : Space →L[ℝ] Space →L[ℝ] F) (x x' : Space) :
    H x x' = ∑ k : Fin 3, ∑ l : Fin 3, (x k * x' l) • H (unitVector k) (unitVector l) := by
  conv_lhs => rw [vec_eq_sum x, vec_eq_sum x']
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem bilin_trace_rot {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : Space →L[ℝ] Space →L[ℝ] F) (R : Space ≃ₗᵢ[ℝ] Space) :
    ∑ j : Fin 3, H (R (unitVector j)) (R (unitVector j)) =
      ∑ j : Fin 3, H (unitVector j) (unitVector j) := by
  simp only [bilin_expand H (R _) (R _)]
  rw [Finset.sum_comm]
  have e : ∀ k : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
      ((R (unitVector j)) k * (R (unitVector j)) l) • H (unitVector k) (unitVector l) =
      H (unitVector k) (unitVector k) := by
    intro k
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, sum_coord_rot_mul R k, ite_smul, one_smul, zero_smul]
    simp
  simp only [e]

theorem trace_rot (H : Space →L[ℝ] Space →L[ℝ] Space) (R : Space ≃ₗᵢ[ℝ] Space) :
    ∑ j : Fin 3, H (R (unitVector j)) (R (unitVector j)) = secondDerivTrace H :=
  bilin_trace_rot H R

theorem secondDerivTrace_pushForward {W0 : Space → Space}
    {H0 H1 : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (R : Space ≃ₗᵢ[ℝ] Space)
    (hW : Differentiable ℝ W0)
    (h0 : ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ W0 y (unitVector j))
      (fun y => (H0 y).flip (unitVector j)))
    (h1 : ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ (pushForward R W0) y (unitVector j))
      (fun y => (H1 y).flip (unitVector j))) :
    ∀ᵐ y, secondDerivTrace (H1 y) = R (secondDerivTrace (H0 (R.symm y))) := by
  let Rc : Space →L[ℝ] Space := R.toContinuousLinearEquiv.toContinuousLinearMap
  let Rs : Space →L[ℝ] Space := R.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hj : ∀ j : Fin 3, ∀ᵐ y, H1 y (unitVector j) (unitVector j) =
      R (H0 (R.symm y) (R.symm (unitVector j)) (R.symm (unitVector j))) := by
    intro j
    have hc := Coercive.ModeDerivative.Internal.weakGradient_column_apply h0 (R.symm (unitVector j))
    have hr := Coercive.ModeDerivative.Internal.weakGradient_rotate hc R.symm
      (f' := fun y => fderiv ℝ (pushForward R W0) y (unitVector j))
      (g' := fun y => Rc.comp (((H0 (R.symm y)).flip (R.symm (unitVector j))).comp Rs))
      (fun y => by rw [fderiv_pushForward R hW]; simp)
      (fun y u => by simp [Rc, Rs])
    filter_upwards [Internal.ProductPairing.weakGradient_unique (h1 j) hr] with y hy
    have := congrArg (fun L : Space →L[ℝ] Space => L (unitVector j)) hy
    simpa [Rc, Rs] using this
  filter_upwards [ae_all_iff.2 hj] with y hy
  rw [← trace_rot (H0 (R.symm y)) R.symm]
  simp only [secondDerivTrace, hy, map_sum]

end Internal.ExtendedInvarianceTrace

end Breakdown.Cert
