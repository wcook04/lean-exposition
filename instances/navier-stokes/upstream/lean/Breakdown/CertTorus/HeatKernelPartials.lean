import Breakdown.CertTorus.KernelStatements

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

namespace Internal.HeatPartials

theorem hasFDerivAt_normSq (x : Space) :
    HasFDerivAt (fun z : Space => ‖z‖ ^ 2)
      (∑ k : Fin 3, (2 * x k) • (EuclideanSpace.proj k : Space →L[ℝ] ℝ)) x := by
  refine ((hasFDerivAt_id x).norm_sq).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp [Fin.sum_univ_three, PiLp.inner_apply]
  ring

theorem heatKernel_eq (τ : ℝ) (z : Space) :
    heatKernel τ z = (4 * π * τ) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2) * (1 / (4 * τ))) := by
  simp only [heatKernel, mul_one_div]

theorem hasFDerivAt_heat {τ : ℝ} (hτ : 0 < τ) (x : Space) :
    HasFDerivAt (heatKernel τ)
      (∑ k : Fin 3, (-(x k / (2 * τ)) * heatKernel τ x) • (EuclideanSpace.proj k : Space →L[ℝ] ℝ)) x := by
  have h := (((hasFDerivAt_normSq x).neg.mul_const (1 / (4 * τ))).exp).const_mul
    ((4 * π * τ) ^ (-(3 / 2 : ℝ)))
  have h' : HasFDerivAt (heatKernel τ) _ x :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => heatKernel_eq τ z)
  refine h'.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  have hτ0 : τ ≠ 0 := hτ.ne'
  rw [heatKernel_eq τ x]
  simp [Fin.sum_univ_three]
  field_simp
  ring

theorem proj_unitVector (i k : Fin 3) :
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ) (unitVector i) = if k = i then 1 else 0 := by
  simp [unitVector, PiLp.single_apply]

theorem heatGradient_unitVector {τ : ℝ} (x : Space) (i : Fin 3) :
    (∑ k : Fin 3, (-(x k / (2 * τ)) * heatKernel τ x) • (EuclideanSpace.proj k : Space →L[ℝ] ℝ))
      (unitVector i) = -(x i / (2 * τ)) * heatKernel τ x := by
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, proj_unitVector, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem fderiv_weighted_unitVector {τ : ℝ} (hτ : 0 < τ) (x : Space) (i j k : Fin 3) :
    fderiv ℝ (fun z : Space =>
        (z j * z k / (4 * τ ^ 2) - (if j = k then 1 / (2 * τ) else 0)) * heatKernel τ z) x
        (unitVector i) =
      (x j * x k / (4 * τ ^ 2) - (if j = k then 1 / (2 * τ) else 0)) *
          (-(x i / (2 * τ)) * heatKernel τ x) +
        heatKernel τ x * ((x j * (if k = i then 1 else 0) + x k * (if j = i then 1 else 0)) *
          (1 / (4 * τ ^ 2))) := by
  have hj : HasFDerivAt (fun z : Space => z j) (EuclideanSpace.proj j : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt
  have hk : HasFDerivAt (fun z : Space => z k) (EuclideanSpace.proj k : Space →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt
  have hp := (((hj.mul hk).mul_const (1 / (4 * τ ^ 2))).sub_const
    (if j = k then 1 / (2 * τ) else 0)).mul (hasFDerivAt_heat hτ x)
  have hp' : HasFDerivAt (fun z : Space =>
      (z j * z k / (4 * τ ^ 2) - (if j = k then 1 / (2 * τ) else 0)) * heatKernel τ z) _ x :=
    hp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by
      simp only [Pi.mul_apply, mul_one_div])
  rw [hp'.fderiv]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, heatGradient_unitVector, proj_unitVector,
    Pi.mul_apply, mul_one_div]
  ring

end Internal.HeatPartials

theorem heatKernelPartials_holds : HeatKernelPartials := by
  intro τ hτ x
  refine ⟨Internal.HeatPartials.hasFDerivAt_heat hτ x, fun i j k => ?_⟩
  rw [Internal.HeatPartials.fderiv_weighted_unitVector hτ x i j k, heatKernelThird]
  have hτ0 : τ ≠ 0 := hτ.ne'
  split_ifs <;> subst_vars <;> (try contradiction) <;> field_simp <;> ring

end Breakdown.FarField
