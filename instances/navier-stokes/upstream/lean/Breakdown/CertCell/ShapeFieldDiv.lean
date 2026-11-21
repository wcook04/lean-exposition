import Breakdown.CertCell.ShapeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem realPartVec_apply (w : Fin 3 → ℂ) (i : Fin 3) : realPartVec w i = (w i).re := rfl

theorem keyVector_differentiable (h1 : TypeOneKeySmooth) (h2 : TypeTwoKeySmooth) (P : ShapeParams)
    (D : TimeFieldData) (hP : IsShapeParams P) (hD : IsTimeFieldData D) (σ : ℝ) (κ : FieldKey)
    (hκ : κ ∈ D.keys) : Differentiable ℝ (keyVector P κ (D.amp κ) σ) := by
  by_cases h0 : κ.label.1 = 0
  · exact (h2 P D κ σ hP hD hκ h0).smooth.differentiable one_ne_zero
  · exact (h1 P D κ σ hP hD hκ h0).smooth.differentiable one_ne_zero

end Internal

theorem fieldDivergenceFree_of (h1 : TypeOneKeySmooth) (h2 : TypeTwoKeySmooth) (hdiv : KeyDivergenceFree) :
    FieldDivergenceFree := by
  intro P D hP hD σ y
  have hsum : HasFDerivAt (complexField P D σ)
      (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y) y := by
    have := HasFDerivAt.fun_sum (u := D.keys) (A := fun κ => keyVector P κ (D.amp κ) σ)
      (A' := fun κ => fderiv ℝ (keyVector P κ (D.amp κ) σ) y) (x := y)
      (fun κ hκ => (Internal.keyVector_differentiable h1 h2 P D hP hD σ κ hκ y).hasFDerivAt)
    exact this
  have hcomp : HasFDerivAt (shapeInfoField P D σ)
      (realPartVec.comp (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y)) y :=
    realPartVec.hasFDerivAt.comp y hsum
  unfold divergenceAt
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Internal.realPartVec_apply, FunLike.coe_sum,
    Finset.sum_apply]
  have hre : ∀ i : Fin 3, (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y (unitVector i) i).re =
      ∑ κ ∈ D.keys, (fderiv ℝ (keyVector P κ (D.amp κ) σ) y (unitVector i) i).re := fun i => Complex.re_sum _ _
  simp only [hre]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun κ hκ => ?_
  have h := hdiv P D κ σ y hP hD hκ
  unfold complexDivergence at h
  rw [← Complex.re_sum, h, Complex.zero_re]

end GivenShape

end CertCell

end Breakdown
