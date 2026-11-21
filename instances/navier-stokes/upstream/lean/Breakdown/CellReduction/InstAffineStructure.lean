import Breakdown.CellReduction.InstanceStatements
import Breakdown.CertCell.CellLayerClosed

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown
namespace CellReduction
namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

theorem withOrigin_valid {P : ShapeParams} {g : OriginProfile} (hP : IsShapeParams P)
    (hg : IsOriginProfile g) : IsShapeParams (withOrigin P g) :=
  ⟨hP.chartLength_pos, hP.azimuthOrder_pos, hP.phase, hg⟩

def traceOp : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ j : Fin 3, (EuclideanSpace.proj j).comp (ContinuousLinearMap.apply ℝ Space (unitVector j))

theorem traceOp_apply (A : Space →L[ℝ] Space) :
    traceOp A = ∑ j : Fin 3, (A (unitVector j)) j := by
  simp [traceOp]

theorem divergenceAt_eq_traceOp {v : Space → Space} {A : Space →L[ℝ] Space} {y : Space}
    (h : HasFDerivAt v A y) : divergenceAt v y = traceOp A := by
  rw [traceOp_apply, divergenceAt, h.fderiv]

theorem slice_hasFDerivAt {F : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (σ : ℝ) (y : Space) :
    HasFDerivAt (F σ) (fderiv ℝ (F σ) y) y := by
  have h : ContDiff ℝ 1 (fun x : Space => F σ x) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  exact (h.differentiable one_ne_zero y).hasFDerivAt

theorem affineField_hasFDerivAt {k : ℕ} (P : ShapeParams) (g : OriginProfile) (centre : TimeFieldData)
    (gt : Fin k → OriginProfile) (tangent : Fin k → TimeFieldData) (q : Fin k → ℝ)
    (h0 : ContDiff ℝ 1 (fun z : ℝ × Space => shapeInfoField (withOrigin P g) centre z.1 z.2))
    (hi : ∀ i, ContDiff ℝ 1 (fun z : ℝ × Space => shapeInfoField (withOrigin P (gt i)) (tangent i) z.1 z.2))
    (σ : ℝ) (y : Space) :
    HasFDerivAt (affineField P g centre gt tangent q σ)
      (fderiv ℝ (shapeInfoField (withOrigin P g) centre σ) y +
        ∑ i, q i • fderiv ℝ (shapeInfoField (withOrigin P (gt i)) (tangent i) σ) y) y := by
  have hs := (slice_hasFDerivAt h0 σ y).add
    (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (slice_hasFDerivAt (hi i) σ y).const_smul (q i))
  exact hs

end Internal

open _root_.Breakdown.CellReduction.Instantiation.Internal

theorem affineFieldStructure_holds : AffineFieldStructureHolds := by
  intro k P g centre gt tangent q hP hg hgt hc ht
  have hP0 : IsShapeParams (withOrigin P g) := withOrigin_valid hP hg
  have hPi : ∀ i, IsShapeParams (withOrigin P (gt i)) := fun i => withOrigin_valid hP (hgt i)
  have s0 := shapeParts_closed.field_smooth _ _ hP0 hc
  have si := fun i => shapeParts_closed.field_smooth _ _ (hPi i) (ht i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ y
    simp only [affineField, s0.2.1 σ y, fun i => (si i).2.1 σ y]
  · intro σ y
    rw [divergenceAt_eq_traceOp (affineField_hasFDerivAt P g centre gt tangent q s0.1 (fun i => (si i).1) σ y),
      map_add, map_sum]
    have e0 : traceOp (fderiv ℝ (shapeInfoField (withOrigin P g) centre σ) y) = 0 := by
      rw [← divergenceAt_eq_traceOp (slice_hasFDerivAt s0.1 σ y)]
      exact shapeParts_closed.field_divergence _ _ hP0 hc σ y
    have ei : ∀ i, traceOp (q i • fderiv ℝ (shapeInfoField (withOrigin P (gt i)) (tangent i) σ) y) = 0 := by
      intro i
      rw [map_smul, ← divergenceAt_eq_traceOp (slice_hasFDerivAt (si i).1 σ y),
        shapeParts_closed.field_divergence _ _ (hPi i) (ht i) σ y, smul_zero]
    rw [e0, Finset.sum_eq_zero fun i _ => ei i, add_zero]
  · exact s0.2.2.1.add (Finset.aestronglyMeasurable_fun_sum _ fun i _ => ((si i).2.2.1.const_smul (q i)))
  · intro σ y
    simp only [affineSecondDeriv, s0.2.2.2 σ y, fun i => (si i).2.2.2 σ y]

end Instantiation
end CellReduction
end Breakdown
