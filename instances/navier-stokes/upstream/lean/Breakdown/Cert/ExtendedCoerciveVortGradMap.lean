import Breakdown.Cert.ExtendedCoerciveNodes

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.VortGradMap

def curlLinear : (Space →L[ℝ] Space) →ₗ[ℝ] Space where
  toFun := curlVec
  map_add' G H := by
    simp only [curlVec, add_apply, PiLp.add_apply, mul_add,
      Finset.sum_add_distrib, add_smul]
  map_smul' c G := by
    simp only [curlVec, smul_apply, PiLp.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.smul_sum, smul_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring

def curlCLM : (Space →L[ℝ] Space) →L[ℝ] Space := LinearMap.toContinuousLinearMap curlLinear

theorem curlCLM_apply (G : Space →L[ℝ] Space) : curlCLM G = curlVec G := rfl

theorem unitVector_apply (i k : Fin 3) : unitVector i k = if k = i then 1 else 0 := by
  simp [unitVector]

theorem apply_eq_sum (A : Space →L[ℝ] Space →L[ℝ] Space) (u : Space) :
    A u = ∑ m : Fin 3, u m • A (unitVector m) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr u]
  simp [unitVector, map_sum, map_smul]

theorem vortGradMap_apply (A : Space →L[ℝ] Space →L[ℝ] Space) (u : Space) :
    vortGradMap A u = curlVec (A u) := by
  rw [apply_eq_sum A u]
  ext k
  simp only [vortGradMap, vortGrad, curlVec, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, PiLp.smul_apply, smul_eq_mul,
    WithLp.ofLp_sum, smul_apply, unitVector_apply]
  simp [Fin.sum_univ_three, unitVector, EuclideanSpace.inner_single_left]
  ring

end Internal.VortGradMap

open Internal.VortGradMap in
theorem vortGradMapSecondDerivFieldHolds_proof : VortGradMapSecondDerivFieldHolds := by
  intro W hW σ y
  have hσ : ContDiff ℝ 2 (W σ) := hW.comp (contDiff_const.prodMk contDiff_id)
  have hd : Differentiable ℝ (fderiv ℝ (W σ)) :=
    (hσ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hcomp : fderiv ℝ (fun x => curlVec (fderiv ℝ (W σ) x)) y
      = curlCLM.comp (secondDerivField W σ y) :=
    (curlCLM.hasFDerivAt.comp y (hd y).hasFDerivAt).fderiv
  rw [hcomp]
  ext1 u
  rw [vortGradMap_apply]
  rfl

end CoerciveWeak

end Breakdown
