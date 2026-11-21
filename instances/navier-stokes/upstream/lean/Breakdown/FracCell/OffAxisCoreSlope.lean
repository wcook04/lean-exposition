import Breakdown.FracCell.OffAxisCoreSlopeSt
import Breakdown.FracCell.OffAxisCoreGrad

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.OffAxisCoreSlope

theorem coord_integral {f : Space → Space} (hf : Integrable f) (i : Fin 3) :
    (∫ y, f y) i = ∫ y, f y i :=
  ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm hf).symm

theorem weak_of_slopeBound {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {K : NNReal}
    (hv : LipschitzWith K v) (hG : ∀ᵐ y ∂(volume : Measure Space), HasFDerivAt v (G y) y) :
    IsWeakGradientOf v G := by
  intro φ hφ j
  obtain ⟨hφs, hφc⟩ := hφ
  have hφd : Differentiable ℝ φ := hφs.differentiable (by simp)
  obtain ⟨C, hφL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφs (by simp)
  have hc1 : Continuous fun y => fderiv ℝ φ y (unitVector j) :=
    (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hL : Integrable fun y => fderiv ℝ φ y (unitVector j) • v y :=
    (hc1.smul hv.continuous).integrable_of_hasCompactSupport
      ((hφc.fderiv_apply (𝕜 := ℝ) (unitVector j)).smul_right)
  have hRae : (fun y => φ y • G y (unitVector j)) =ᵐ[volume]
      fun y => φ y • fderiv ℝ v y (unitVector j) := by
    filter_upwards [hG] with y hy
    rw [hy.fderiv]
  have hbd : MemLp (fun y => fderiv ℝ v y (unitVector j)) ⊤ volume := by
    refine memLp_top_of_bound (measurable_fderiv_apply_const ℝ v (unitVector j)).aestronglyMeasurable
      (K * ‖unitVector j‖) (Filter.Eventually.of_forall fun y => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hv) (norm_nonneg _))
  have hR : Integrable fun y => φ y • fderiv ℝ v y (unitVector j) :=
    (hφs.continuous.integrable_of_hasCompactSupport hφc).smul_of_top_left hbd
  rw [integral_congr_ae hRae]
  ext i
  rw [coord_integral hL i, PiLp.neg_apply, coord_integral hR i]
  have hvi : LipschitzWith _ (fun y => v y i) := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).lipschitz.comp hv
  have key := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume) hvi hφL hφc (unitVector j)
  have e1 : ∀ x, lineDeriv ℝ φ x (-unitVector j) = -(fderiv ℝ φ x (unitVector j)) := fun x => by
    rw [(hφd x).lineDeriv_eq_fderiv, map_neg]
  have e2 : (fun x => lineDeriv ℝ (fun y => v y i) x (unitVector j) * φ x) =ᵐ[volume]
      fun x => (fderiv ℝ v x (unitVector j)) i * φ x := by
    filter_upwards [hG] with x hx
    have hxi : HasFDerivAt (fun y => v y i) ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (G x)) x :=
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x hx
    rw [hxi.differentiableAt.lineDeriv_eq_fderiv, hxi.fderiv, hx.fderiv]
    rfl
  rw [integral_congr_ae e2] at key
  simp only [e1, neg_mul, integral_neg] at key
  have e3 : (∫ y, (φ y • fderiv ℝ v y (unitVector j)) i) = ∫ x, (fderiv ℝ v x (unitVector j)) i * φ x := by
    congr 1
    funext y
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have e4 : (∫ y, (fderiv ℝ φ y (unitVector j) • v y) i) = ∫ x, fderiv ℝ φ x (unitVector j) * v x i := by
    congr 1
  rw [e3, e4, key]
  ring

end Internal.OffAxisCoreSlope

theorem shapeWeak_of_parts (hL : ShapeSlopeStatement) (hD : ShapeDerivStatement) : ShapeWeakStatement := by
  intro g Q hRin hR hZ hZ0 hQc hQ0 hQ1 hQ2 hQ3
  obtain ⟨K, hK⟩ := hL g Q hRin hR hZ hZ0 hQc hQ0 hQ1 hQ2 hQ3
  exact Internal.OffAxisCoreSlope.weak_of_slopeBound hK (hD g Q hRin hR hZ hZ0 hQc hQ0 hQ1 hQ2 hQ3)

theorem offAxisCore_of_parts (h : RectOffStatement) (hL : ShapeSlopeStatement) (hD : ShapeDerivStatement) :
    OffAxisCoreStatement :=
  offAxisCore_of_weak h (shapeWeak_of_parts hL hD)

end Spectral

end CellCert

end Breakdown
