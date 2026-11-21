import Breakdown.CellReduction.InstanceStatements

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

namespace Internal

theorem clm_apply_coordSum (L : Space →L[ℝ] ℝ) (w : Space) :
    L w = ∑ i : Fin 3, w i * L (unitVector i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  rfl

theorem fderiv_coord_apply {v : Space → Space} (hv : Differentiable ℝ v) (i : Fin 3)
    (y u : Space) : fderiv ℝ (fun x => v x i) y u = fderiv ℝ v y u i := by
  have h := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y (hv y).hasFDerivAt
  have he : (fun x => v x i) = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ v := rfl
  rw [he, h.fderiv]
  rfl

end Internal

open Internal

theorem classicalDivergenceWeak_holds : ClassicalDivergenceWeakHolds := by
  intro v hv hdiv φ hφ
  obtain ⟨hφs, hφc⟩ := hφ
  have hvd : Differentiable ℝ v := hv.differentiable (by simp)
  have hvc : Continuous v := hv.continuous
  have hv' : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
  have hφd : Differentiable ℝ φ := hφs.differentiable (by simp)
  have hφ' : Continuous (fderiv ℝ φ) := hφs.continuous_fderiv (by simp)
  have hcoord : ∀ i : Fin 3, Continuous fun y => v y i := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hvc
  have hcoordd : ∀ i : Fin 3, Differentiable ℝ fun y => v y i := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).differentiable.comp hvd
  have hdcoord : ∀ i : Fin 3, Continuous fun y => fderiv ℝ v y (unitVector i) i := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp (hv'.clm_apply continuous_const)
  have hintA : ∀ i : Fin 3, Integrable (fun y => v y i * fderiv ℝ φ y (unitVector i)) :=
    fun i => ((hcoord i).mul (hφ'.clm_apply continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (f := fun y => v y i) (hφc.fderiv_apply (𝕜 := ℝ) (unitVector i)))
  have hintB : ∀ i : Fin 3, Integrable (fun y => fderiv ℝ v y (unitVector i) i * φ y) :=
    fun i => ((hdcoord i).mul hφs.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (f := fun y => fderiv ℝ v y (unitVector i) i) hφc)
  have hterm : ∀ i : Fin 3,
      ∫ y, v y i * fderiv ℝ φ y (unitVector i) = - ∫ y, fderiv ℝ v y (unitVector i) i * φ y := by
    intro i
    have h1 : Integrable (fun y => fderiv ℝ (fun x => v x i) y (unitVector i) * φ y) := by
      simp_rw [fderiv_coord_apply hvd i]
      exact hintB i
    have h3 : Integrable (fun y => v y i * φ y) :=
      ((hcoord i).mul hφs.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_left (f := fun y => v y i) hφc)
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 (hintA i) h3
      (fun x _ => hcoordd i x) (fun x _ => hφd x)
    simpa only [fderiv_coord_apply hvd i] using this
  have hexp : ∀ y, fderiv ℝ φ y (v y) = ∑ i : Fin 3, v y i * fderiv ℝ φ y (unitVector i) :=
    fun y => clm_apply_coordSum _ _
  calc ∫ y, fderiv ℝ φ y (v y) = ∑ i : Fin 3, ∫ y, v y i * fderiv ℝ φ y (unitVector i) := by
        simp_rw [hexp]
        exact integral_finsetSum _ fun i _ => hintA i
    _ = - ∑ i : Fin 3, ∫ y, fderiv ℝ v y (unitVector i) i * φ y := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => hterm i
    _ = - ∫ y, divergenceAt v y * φ y := by
        rw [← integral_finsetSum _ fun i _ => hintB i]
        congr 2
        ext y
        simp only [divergenceAt, Finset.sum_mul]
    _ = 0 := by simp [hdiv]

end Instantiation

end CellReduction

end Breakdown
