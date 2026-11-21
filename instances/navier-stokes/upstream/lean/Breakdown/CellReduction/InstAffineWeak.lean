import Breakdown.CellReduction.InstanceStatements
import Breakdown.CertCell.CellLayerClosed

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

theorem weakGradient_zero :
    IsWeakGradient (fun _ => (0 : Space)) (fun _ => (0 : Space →L[ℝ] Space)) := by
  refine ⟨locallyIntegrable_zero, locallyIntegrable_zero, fun φ _ i => ?_⟩
  simp

theorem weakGradient_add {f f' : Space → Space} {g g' : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f g) (h' : IsWeakGradient f' g') :
    IsWeakGradient (fun y => f y + f' y) (fun y => g y + g' y) := by
  refine ⟨h.1.add h'.1, h.2.1.add h'.2.1, fun φ hφ i => ?_⟩
  have hc : Continuous φ := hφ.1.continuous
  have hd : Continuous (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector i)) := hφ.2.fderiv_apply (𝕜 := ℝ) _
  have i1 : Integrable (fun y => φ y • g y (unitVector i)) := by
    have := (h.2.1.integrable_smul_left_of_hasCompactSupport hc hφ.2).apply_continuousLinearMap
      (unitVector i)
    simpa using this
  have i2 : Integrable (fun y => φ y • g' y (unitVector i)) := by
    have := (h'.2.1.integrable_smul_left_of_hasCompactSupport hc hφ.2).apply_continuousLinearMap
      (unitVector i)
    simpa using this
  have j1 : Integrable (fun y => fderiv ℝ φ y (unitVector i) • f y) :=
    h.1.integrable_smul_left_of_hasCompactSupport hd hds
  have j2 : Integrable (fun y => fderiv ℝ φ y (unitVector i) • f' y) :=
    h'.1.integrable_smul_left_of_hasCompactSupport hd hds
  simp only [add_apply, smul_add]
  rw [integral_add i1 i2, integral_add j1 j2, h.2.2 φ hφ i, h'.2.2 φ hφ i, neg_add]

theorem weakGradient_smul (c : ℝ) {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f g) : IsWeakGradient (fun y => c • f y) (fun y => c • g y) := by
  refine ⟨h.1.smul c, h.2.1.smul c, fun φ hφ i => ?_⟩
  have e1 : ∀ y, φ y • (c • g y) (unitVector i) = c • (φ y • g y (unitVector i)) := fun y => by
    rw [smul_apply, smul_comm]
  have e2 : ∀ y, fderiv ℝ φ y (unitVector i) • c • f y = c • (fderiv ℝ φ y (unitVector i) • f y) :=
    fun y => smul_comm _ _ _
  simp only [e1, e2, integral_smul, h.2.2 φ hφ i, smul_neg]

theorem weakGradient_sum {ι : Type*} (s : Finset ι) {f : ι → Space → Space}
    {g : ι → Space → (Space →L[ℝ] Space)} (h : ∀ i ∈ s, IsWeakGradient (f i) (g i)) :
    IsWeakGradient (fun y => ∑ i ∈ s, f i y) (fun y => ∑ i ∈ s, g i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weakGradient_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact weakGradient_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem slice_differentiableAt {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2))
    (σ : ℝ) (y : Space) : DifferentiableAt ℝ (F σ) y := by
  have h2 : ContDiff ℝ 1 (fun y : Space => F σ y) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  exact (h2.differentiable one_ne_zero) y

theorem shapeField_differentiableAt (Q : ShapeParams) (D : TimeFieldData) (hQ : IsShapeParams Q)
    (hD : IsTimeFieldData D) (σ : ℝ) (y : Space) : DifferentiableAt ℝ (shapeInfoField Q D σ) y :=
  slice_differentiableAt (F := shapeInfoField Q D) (shapeParts_closed.field_smooth Q D hQ hD).1 σ y

theorem withOrigin_valid (P : ShapeParams) (g : OriginProfile) (hP : IsShapeParams P)
    (hg : IsOriginProfile g) : IsShapeParams (withOrigin P g) :=
  ⟨hP.chartLength_pos, hP.azimuthOrder_pos, hP.phase, hg⟩

end Internal

theorem affineFieldWeakSecondDeriv_holds : AffineFieldWeakSecondDerivHolds := by
  intro k P g centre gt tangent q hP hg hgt hc ht σ j
  have hPg := Internal.withOrigin_valid P g hP hg
  have hPi : ∀ i, IsShapeParams (withOrigin P (gt i)) := fun i => Internal.withOrigin_valid P (gt i) hP (hgt i)
  have hfd : ∀ y, fderiv ℝ (affineField P g centre gt tangent q σ) y =
      fderiv ℝ (shapeInfoField (withOrigin P g) centre σ) y +
        ∑ i, q i • fderiv ℝ (shapeInfoField (withOrigin P (gt i)) (tangent i) σ) y := by
    intro y
    have H : HasFDerivAt (fun y => shapeInfoField (withOrigin P g) centre σ y +
        ∑ i, q i • shapeInfoField (withOrigin P (gt i)) (tangent i) σ y)
        (fderiv ℝ (shapeInfoField (withOrigin P g) centre σ) y +
          ∑ i, q i • fderiv ℝ (shapeInfoField (withOrigin P (gt i)) (tangent i) σ) y) y :=
      (Internal.shapeField_differentiableAt _ _ hPg hc σ y).hasFDerivAt.fun_add
        (HasFDerivAt.fun_sum fun i _ =>
          (Internal.shapeField_differentiableAt _ _ (hPi i) (ht i) σ y).hasFDerivAt.fun_const_smul (q i))
    exact H.fderiv
  have hsum := Internal.weakGradient_add (shapeParts_closed.field_weak_hessian _ _ hPg hc σ j)
    (Internal.weakGradient_sum Finset.univ fun i _ =>
      Internal.weakGradient_smul (q i) (shapeParts_closed.field_weak_hessian _ _ (hPi i) (ht i) σ j))
  convert hsum using 1
  · funext y
    rw [hfd y]
    simp
  · funext y
    ext v : 1
    simp [affineSecondDeriv]

end Instantiation

end CellReduction

end Breakdown
