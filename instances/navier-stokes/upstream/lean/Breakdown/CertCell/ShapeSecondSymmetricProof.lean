import Breakdown.CertCell.ShapeSecondSymmetric

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem secondDeriv_symmetric_of_contDiff_one {f : Space → Fin 3 → ℂ} (hf : ContDiff ℝ 1 f) (y u w : Space) :
    fderiv ℝ (fun x => fderiv ℝ f x) y u w = fderiv ℝ (fun x => fderiv ℝ f x) y w u := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  by_cases h : DifferentiableAt ℝ (fun x => fderiv ℝ f x) y
  · exact second_derivative_symmetric (fun x => (hd x).hasFDerivAt) h.hasFDerivAt u w
  · rw [fderiv_zero_of_not_differentiableAt h]
    rfl

theorem keySecondDeriv_symmetric_of_smooth (h1 : TypeOneKeySmooth) (h2 : TypeTwoKeySmooth) (P : ShapeParams)
    (D : TimeFieldData) (hP : IsShapeParams P) (hD : IsTimeFieldData D) (κ : FieldKey) (hκ : κ ∈ D.keys)
    (σ : ℝ) (y u w : Space) :
    keyHess P κ (D.amp κ) σ y u w = keyHess P κ (D.amp κ) σ y w u := by
  have hs : IsKeyFieldSmooth (keyVector P κ (D.amp κ) σ) := by
    by_cases hl : κ.label.1 = 0
    · exact h2 P D κ σ hP hD hκ hl
    · exact h1 P D κ σ hP hD hκ hl
  exact secondDeriv_symmetric_of_contDiff_one hs.smooth y u w

end Internal

theorem fieldSecondSymmetric_of_smooth (h1 : TypeOneKeySmooth) (h2 : TypeTwoKeySmooth) :
    FieldSecondSymmetric := by
  intro P D hP hD σ y u w
  simp only [shapeHess, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  rw [Internal.keySecondDeriv_symmetric_of_smooth h1 h2 P D hP hD κ hκ σ y u w]

end GivenShape

end CertCell

end Breakdown
