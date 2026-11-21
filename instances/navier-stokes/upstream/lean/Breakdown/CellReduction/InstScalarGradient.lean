import Breakdown.CellReduction.InstanceStatements

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

namespace Internal

theorem slice_vanish_outside {φ : ℝ → Space → Space}
    (hc : HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2)) :
    ∃ R : ℝ, ∀ σ y, R < ‖y‖ → φ σ y = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  refine ⟨R, fun σ y hy => ?_⟩
  have hnot : ((σ, y) : ℝ × Space) ∉ tsupport (fun z : ℝ × Space => φ z.1 z.2) := by
    intro hm
    have h1 := hR hm
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : ‖y‖ ≤ ‖((σ, y) : ℝ × Space)‖ := by
      exact norm_snd_le ((σ, y) : ℝ × Space)
    linarith
  exact image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => φ z.1 z.2) hnot

theorem expand_unit (v : Space) : v = ∑ i : Fin 3, v i • unitVector i := by
  simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v).symm

theorem inner_gradient_expand (g : Space → ℝ) (v y : Space) :
    inner ℝ (gradient g y) v = ∑ i : Fin 3, fderiv ℝ g y (unitVector i) * v i := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  conv_lhs => rw [expand_unit v]
  simp [map_sum, map_smul, mul_comm]

theorem component_fderiv {ψ : Space → Space} {y : Space} (hψ : DifferentiableAt ℝ ψ y) (i : Fin 3)
    (v : Space) : fderiv ℝ (fun x => ψ x i) y v = (fderiv ℝ ψ y v) i := by
  have h := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y hψ.hasFDerivAt).fderiv
  have e : (fun x => ψ x i) = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ ψ := by
    funext x
    simp
  rw [e, h]
  simp

theorem slice_integral_zero (g : Space → ℝ) {K : NNReal} (hg : LipschitzWith K g)
    (ψ : Space → Space) (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ)
    (hd : ∀ y, divergenceAt ψ y = 0) :
    ∫ y, inner ℝ (gradient g y) (ψ y) = 0 := by
  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hcomp : ∀ i : Fin 3, ContDiff ℝ ∞ (fun y => ψ y i) := by
    intro i
    have := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hψ
    simpa [Function.comp_def] using this
  have hsupp : ∀ i : Fin 3, HasCompactSupport (fun y => ψ y i) := by
    intro i
    have := hs.comp_left (g := fun v : Space => v i) (by simp)
    simpa [Function.comp_def] using this
  have hint : ∀ i : Fin 3, Integrable (fun y => fderiv ℝ g y (unitVector i) * ψ y i) := by
    intro i
    refine Integrable.bdd_mul (c := K) ((hcomp i).continuous.integrable_of_hasCompactSupport (hsupp i))
      (measurable_fderiv_apply_const ℝ g (unitVector i)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    calc ‖fderiv ℝ g y (unitVector i)‖ ≤ ‖fderiv ℝ g y‖ * ‖unitVector i‖ := (fderiv ℝ g y).le_opNorm _
      _ ≤ K * 1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ hg
        · simp [unitVector]
      _ = K := mul_one _
  have hterm : ∀ i : Fin 3, ∫ y, fderiv ℝ g y (unitVector i) * ψ y i =
      ∫ y, -((fderiv ℝ ψ y (unitVector i)) i * g y) := by
    intro i
    obtain ⟨D, hD⟩ : ∃ D, LipschitzWith D (fun y => ψ y i) :=
      ContDiff.lipschitzWith_of_hasCompactSupport (hsupp i) (hcomp i) (by simp)
    have h1 : ∫ y, fderiv ℝ g y (unitVector i) * ψ y i =
        ∫ y, lineDeriv ℝ g y (unitVector i) * ψ y i := by
      refine integral_congr_ae ?_
      filter_upwards [hg.ae_differentiableAt (μ := volume)] with y hy
      rw [hy.lineDeriv_eq_fderiv]
    rw [h1, hg.integral_lineDeriv_mul_eq hD (hsupp i) (unitVector i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [((hcomp i).differentiable (by simp) y).lineDeriv_eq_fderiv, component_fderiv (hdiff y)]
    simp
  have hint2 : ∀ i : Fin 3, Integrable (fun y => -((fderiv ℝ ψ y (unitVector i)) i * g y)) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have hc : Continuous (fun y => fderiv ℝ ψ y) := hψ.continuous_fderiv (by simp)
      have hc2 : Continuous (fun y => (fderiv ℝ ψ y (unitVector i)) i) :=
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp (hc.clm_apply continuous_const)
      exact (hc2.mul hg.continuous).neg
    · have h0 := (hs.fderiv (𝕜 := ℝ)).comp_left (g := fun A : Space →L[ℝ] Space => (A (unitVector i)) i)
        (by simp)
      have h1 := h0.mul_right (f' := g)
      exact h1.neg
  calc ∫ y, inner ℝ (gradient g y) (ψ y)
      = ∫ y, ∑ i : Fin 3, fderiv ℝ g y (unitVector i) * ψ y i := by
        simp_rw [inner_gradient_expand]
    _ = ∑ i : Fin 3, ∫ y, fderiv ℝ g y (unitVector i) * ψ y i :=
        integral_finsetSum _ fun i _ => hint i
    _ = ∑ i : Fin 3, ∫ y, -((fderiv ℝ ψ y (unitVector i)) i * g y) := by
        simp_rw [hterm]
    _ = ∫ y, ∑ i : Fin 3, -((fderiv ℝ ψ y (unitVector i)) i * g y) :=
        (integral_finsetSum _ fun i _ => hint2 i).symm
    _ = ∫ y, -(divergenceAt ψ y * g y) := by
        simp_rw [divergenceAt, Finset.sum_mul, Finset.sum_neg_distrib]
    _ = 0 := by simp [hd]

end Internal

theorem scalarGradientOrthogonal_holds : ScalarGradientOrthogonalHolds := by
  intro p hp hloc
  refine ⟨?_, fun φ hφ => ?_⟩
  · have hm : Measurable (fun z : ℝ × Space => fderiv ℝ (p z.1) z.2) :=
      measurable_fderiv_with_param ℝ hp
    exact ((InnerProductSpace.toDual ℝ Space).symm.continuous.measurable.comp hm).aestronglyMeasurable
  · obtain ⟨hsm, hcs, hdiv⟩ := hφ
    obtain ⟨R, hR⟩ := Internal.slice_vanish_outside hcs
    have hslice : ∀ σ, ∫ y, inner ℝ (gradient (p σ) y) (φ σ y) = 0 := by
      intro σ
      obtain ⟨L, hL⟩ := hloc σ (R + 1)
      obtain ⟨g, hg, hpg⟩ := hL.extend_real
      have heq : ∀ y, inner ℝ (gradient (p σ) y) (φ σ y) = inner ℝ (gradient g y) (φ σ y) := by
        intro y
        by_cases hy : ‖y‖ < R + 1
        · have hev : p σ =ᶠ[nhds y] g := by
            filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)] with x hx
            exact hpg (Metric.ball_subset_closedBall hx)
          rw [gradient, gradient, hev.fderiv_eq]
        · rw [hR σ y (by linarith), inner_zero_right, inner_zero_right]
      have hsl : ContDiff ℝ ∞ (φ σ) := hsm.comp (contDiff_const.prodMk contDiff_id)
      have hcsl : HasCompactSupport (φ σ) :=
        HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy => by
          refine hR σ y ?_
          rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
          exact hy
      rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
      exact Internal.slice_integral_zero g hg (φ σ) hsl hcsl (hdiv σ)
    by_cases hi : Integrable (fun z : ℝ × Space => inner ℝ (gradient (p z.1) z.2) (φ z.1 z.2))
    · rw [Measure.volume_eq_prod] at hi ⊢
      rw [integral_prod _ hi]
      simp only [hslice, integral_zero]
    · exact integral_undef hi

end Instantiation

end CellReduction

end Breakdown
