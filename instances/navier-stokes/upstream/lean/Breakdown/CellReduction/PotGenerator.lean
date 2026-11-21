import Breakdown.CellReduction.PotentialShape
import Breakdown.CertCell.CellLayerClosed

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect

namespace Internal

theorem weakGradient_congr_ae {f : Space → Space} {g g' : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f g) (hg : g =ᵐ[volume] g') : IsWeakGradient f g' := by
  refine ⟨h.1, h.2.1.congr hg, fun φ hφ i => ?_⟩
  refine Eq.trans ?_ (h.2.2 φ hφ i)
  refine integral_congr_ae ?_
  filter_upwards [hg] with y hy
  rw [hy]

theorem fieldGradient_eq_keySum (P : ShapeParams) (D : TimeFieldData) (σ : ℝ)
    (hf : ∀ κ ∈ D.keys, IsKeyFieldSmooth (keyVector P κ (D.amp κ) σ)) (y : Space) :
    fderiv ℝ (shapeInfoField P D σ) y =
      ∑ κ ∈ D.keys, ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec
        (fderiv ℝ (keyVector P κ (D.amp κ) σ) y) := by
  have hs : HasFDerivAt (fun x => ∑ κ ∈ D.keys, keyVector P κ (D.amp κ) σ x)
      (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y) y :=
    HasFDerivAt.fun_sum fun κ hκ => (((hf κ hκ).smooth.differentiable one_ne_zero) y).hasFDerivAt
  have hc : HasFDerivAt (shapeInfoField P D σ)
      (realPartVec.comp (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y)) y :=
    realPartVec.hasFDerivAt.comp y hs
  rw [hc.fderiv, ← map_sum]
  rfl

theorem secondDeriv_ae_eq_givenSecond (P : ShapeParams) (D : TimeFieldData) (σ : ℝ)
    (hf : ∀ κ ∈ D.keys, IsKeyFieldSmooth (keyVector P κ (D.amp κ) σ)) :
    ∀ᵐ y, DifferentiableAt ℝ (fun x => fderiv ℝ (shapeInfoField P D σ) x) y ∧
      secondDeriv (shapeInfoField P D σ) y = shapeHess P D σ y := by
  have hG : (fun x => fderiv ℝ (shapeInfoField P D σ) x) = fun x =>
      ∑ κ ∈ D.keys, ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec
        (fderiv ℝ (keyVector P κ (D.amp κ) σ) x) :=
    funext (fieldGradient_eq_keySum P D σ hf)
  have hall : ∀ᵐ y ∂(volume : Measure Space), ∀ κ ∈ D.keys,
      DifferentiableAt ℝ (fderiv ℝ (keyVector P κ (D.amp κ) σ)) y :=
    (Filter.eventually_all_finset D.keys).2 fun κ hκ =>
      Internal.ae_differentiableAt_of_ball_slopeBound (hf κ hκ).gradient_slope_bound
  filter_upwards [hall] with y hy
  have hd : HasFDerivAt (fun x => ∑ κ ∈ D.keys, ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec
        (fderiv ℝ (keyVector P κ (D.amp κ) σ) x))
      (∑ κ ∈ D.keys, (ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec).comp
        (keyHess P κ (D.amp κ) σ y)) y :=
    HasFDerivAt.fun_sum fun κ hκ =>
      (ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec).hasFDerivAt.comp y (hy κ hκ).hasFDerivAt
  refine ⟨?_, ?_⟩
  · rw [hG]
    exact hd.differentiableAt
  · show fderiv ℝ (fun x => fderiv ℝ (shapeInfoField P D σ) x) y = shapeHess P D σ y
    rw [hG, hd.fderiv]
    rfl

theorem keysSmooth_of_data (P : ShapeParams) (D : TimeFieldData) (σ : ℝ) (hP : IsShapeParams P)
    (hD : IsTimeFieldData D) : ∀ κ ∈ D.keys, IsKeyFieldSmooth (keyVector P κ (D.amp κ) σ) := by
  intro κ hκ
  by_cases h0 : κ.label.1 = 0
  · exact typeTwoKeySmooth_closed P D κ σ hP hD hκ h0
  · exact typeOneKeySmooth_closed P D κ σ hP hD hκ h0

end Internal

theorem compactFieldSecondRegular_holds : CompactFieldSecondRegular := by
  intro P D tb hP hD
  have hT : IsTimeFieldData D := hD.field
  have hae := fun σ => Internal.secondDeriv_ae_eq_givenSecond P D σ (Internal.keysSmooth_of_data P D σ hP hT)
  obtain ⟨B, hB⟩ := shapeParts_closed.field_decay P D hP hT
  have hB0 : 0 ≤ B := by
    have h := (hB 0 0).1
    rw [norm_zero, add_zero, div_one] at h
    exact (norm_nonneg _).trans h
  refine ⟨fun σ j => ?_, fun σ => ?_, B, fun σ => ?_⟩
  · refine Internal.weakGradient_congr_ae (shapeParts_closed.field_weak_hessian P D hP hT σ j) ?_
    filter_upwards [hae σ] with y hy
    rw [hy.2]
  · filter_upwards [hae σ] with y hy
    exact hy.1
  · filter_upwards [hae σ] with y hy
    rw [hy.2]
    refine (hB σ y).2.2.trans ?_
    exact div_le_self hB0 (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg y)))

end PotentialShape

end Breakdown
