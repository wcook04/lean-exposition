import Breakdown.CertCell.ShapeStatements
import Breakdown.FracCell.GivenToolkit

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem locallyIntegrable_of_ball_bound {E : Type*} [NormedAddCommGroup E] {F : Space → E}
    (hF : AEStronglyMeasurable F volume) (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ y : Space, ‖y‖ ≤ R → ‖F y‖ ≤ C) :
    LocallyIntegrable F volume := by
  intro x
  obtain ⟨C, hC⟩ := hb (‖x‖ + 1)
  refine ⟨Metric.closedBall 0 (‖x‖ + 1), Metric.closedBall_mem_nhds_of_mem ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    linarith
  · refine Measure.integrableOn_of_bounded (M := C) measure_closedBall_lt_top.ne hF ?_
    refine (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).2 (Filter.Eventually.of_forall fun y hy => ?_)
    exact hC y (mem_closedBall_zero_iff.1 hy)

theorem ball_bound_sum {ι E : Type*} [NormedAddCommGroup E] (s : Finset ι) (F : ι → Space → E)
    (h : ∀ i ∈ s, ∀ R : ℝ, ∃ C : ℝ, ∀ y : Space, ‖y‖ ≤ R → ‖F i y‖ ≤ C) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ y : Space, ‖y‖ ≤ R → ‖∑ i ∈ s, F i y‖ ≤ C := by
  classical
  intro R
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun y _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨C1, h1⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨C2, h2⟩ := h a (Finset.mem_insert_self a s) R
    refine ⟨C2 + C1, fun y hy => ?_⟩
    rw [Finset.sum_insert ha]
    exact (norm_add_le _ _).trans (add_le_add (h2 y hy) (h1 y hy))

theorem ae_differentiableAt_of_ball_slopeBound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {g : Space → F}
    (hg : ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L g (Metric.closedBall 0 R)) :
    ∀ᵐ y ∂(volume : Measure Space), DifferentiableAt ℝ g y := by
  have hn : ∀ n : ℕ, ∀ᵐ y ∂(volume : Measure Space), y ∈ Metric.ball (0 : Space) n → DifferentiableAt ℝ g y := by
    intro n
    obtain ⟨L, hL⟩ := hg n
    have hLb : LipschitzOnWith L g (Metric.ball 0 n) := hL.mono Metric.ball_subset_closedBall
    filter_upwards [hLb.ae_differentiableWithinAt_of_mem (μ := volume)] with y hy hyb
    exact (hy hyb).differentiableAt (Metric.isOpen_ball.mem_nhds hyb)
  filter_upwards [ae_all_iff.2 hn] with y hy
  obtain ⟨n, hn'⟩ := exists_nat_gt ‖y‖
  exact hy n (mem_ball_zero_iff.2 hn')

theorem fderiv_norm_bound_of_ball_slopeBound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : Space → F}
    (hg : ∀ R : ℝ, ∃ L : NNReal, LipschitzOnWith L g (Metric.closedBall 0 R)) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ y : Space, ‖y‖ ≤ R → ‖fderiv ℝ g y‖ ≤ C := by
  intro R
  obtain ⟨L, hL⟩ := hg (R + 1)
  refine ⟨L, fun y hy => norm_fderiv_le_of_lipschitzOn ℝ (Metric.closedBall_mem_nhds_of_mem ?_) hL⟩
  rw [mem_ball_zero_iff]
  linarith

theorem weakSecondDeriv_of_keys {s : Finset FieldKey} {f : FieldKey → Space → Fin 3 → ℂ}
    (hf : ∀ κ ∈ s, IsKeyFieldSmooth (f κ)) (j : Fin 3) :
    IsWeakGradient (fun y => fderiv ℝ (fun x => realPartVec (∑ κ ∈ s, f κ x)) y (unitVector j))
      (fun y => (∑ κ ∈ s, (ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec).comp
          (fderiv ℝ (fun x => fderiv ℝ (f κ) x) y)).flip (unitVector j)) := by
  have hLapp : ∀ X : Space →L[ℝ] (Fin 3 → ℂ),
      ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec X = realPartVec.comp X := fun X => rfl
  generalize ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec = L at hLapp ⊢
  have hW : ∀ y, fderiv ℝ (fun x => realPartVec (∑ κ ∈ s, f κ x)) y = ∑ κ ∈ s, L (fderiv ℝ (f κ) y) := by
    intro y
    have hs : HasFDerivAt (fun x => ∑ κ ∈ s, f κ x) (∑ κ ∈ s, fderiv ℝ (f κ) y) y :=
      HasFDerivAt.fun_sum fun κ hκ => (((hf κ hκ).smooth.differentiable one_ne_zero) y).hasFDerivAt
    rw [← map_sum, hLapp]
    exact (realPartVec.hasFDerivAt.comp y hs).fderiv
  set G : Space → (Space →L[ℝ] Space) := fun y => ∑ κ ∈ s, L (fderiv ℝ (f κ) y) with hGdef
  set H : Space → (Space →L[ℝ] Space →L[ℝ] Space) :=
    fun y => ∑ κ ∈ s, L.comp (fderiv ℝ (fun x => fderiv ℝ (f κ) x) y) with hHdef
  have hGL : ∀ R : ℝ, ∃ C : NNReal, LipschitzOnWith C G (Metric.closedBall 0 R) := by
    have h := FracInternal.slopeOn_finset_sum s (fun _ => (1 : ℝ)) (fun κ y => L (fderiv ℝ (f κ) y))
      fun κ hκ R => by
        obtain ⟨C, hC⟩ := (hf κ hκ).gradient_slope_bound R
        exact ⟨‖L‖₊ * C, L.lipschitz.comp_lipschitzOnWith hC⟩
    simpa only [one_smul] using h
  have hae : fderiv ℝ G =ᵐ[volume] H := by
    have hall : ∀ᵐ y ∂(volume : Measure Space), ∀ κ ∈ s, DifferentiableAt ℝ (fderiv ℝ (f κ)) y :=
      (Filter.eventually_all_finset s).2 fun κ hκ =>
        ae_differentiableAt_of_ball_slopeBound (hf κ hκ).gradient_slope_bound
    filter_upwards [hall] with y hy
    have hd : HasFDerivAt G (∑ κ ∈ s, L.comp (fderiv ℝ (fun x => fderiv ℝ (f κ) x) y)) y :=
      HasFDerivAt.fun_sum fun κ hκ => L.hasFDerivAt.comp y (hy κ hκ).hasFDerivAt
    exact hd.fderiv
  obtain ⟨hw2, -⟩ := FracInternal.weakSecond_of_slopeOn hGL
  have hGc : Continuous G :=
    continuous_finsetSum s fun κ hκ => L.continuous.comp ((hf κ hκ).smooth.continuous_fderiv one_ne_zero)
  have hunit : ‖unitVector j‖ = 1 := by simp [unitVector]
  have hHb : ∀ R : ℝ, ∃ C : ℝ, ∀ y : Space, ‖y‖ ≤ R → ‖H y‖ ≤ C := by
    refine ball_bound_sum s (fun κ y => L.comp (fderiv ℝ (fun x => fderiv ℝ (f κ) x) y)) fun κ hκ R => ?_
    obtain ⟨C, hC⟩ := fderiv_norm_bound_of_ball_slopeBound (hf κ hκ).gradient_slope_bound R
    refine ⟨‖L‖ * C, fun y hy => ?_⟩
    exact (L.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (hC y hy) (norm_nonneg _))
  have hcomp : Continuous fun X : Space →L[ℝ] Space →L[ℝ] (Fin 3 → ℂ) => L.comp X :=
    continuous_const.clm_comp continuous_id
  have hHm : AEStronglyMeasurable H volume :=
    Finset.aestronglyMeasurable_fun_sum s fun κ _ =>
      (hcomp.measurable.comp (measurable_fderiv ℝ (fderiv ℝ (f κ)))).aestronglyMeasurable
  have hflip : Continuous fun A : Space →L[ℝ] Space →L[ℝ] Space => A.flip (unitVector j) :=
    (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous.comp
      (ContinuousLinearMap.flipₗᵢ ℝ Space Space Space).continuous
  refine ⟨?_, ?_, fun φ hφ i => ?_⟩
  · simp only [hW]
    exact (hGc.clm_apply continuous_const).locallyIntegrable
  · refine locallyIntegrable_of_ball_bound (hflip.comp_aestronglyMeasurable hHm) fun R => ?_
    obtain ⟨C, hC⟩ := hHb R
    refine ⟨C, fun y hy => ?_⟩
    calc ‖(H y).flip (unitVector j)‖ ≤ ‖(H y).flip‖ * ‖unitVector j‖ := (H y).flip.le_opNorm _
      _ = ‖H y‖ := by rw [ContinuousLinearMap.opNorm_flip, hunit, mul_one]
      _ ≤ C := hC y hy
  · simp only [hW, ContinuousLinearMap.flip_apply]
    rw [hw2 φ hφ j i, neg_neg]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hy]

end Internal

theorem fieldWeakSecondDeriv_of (hone : TypeOneKeySmooth) (htwo : TypeTwoKeySmooth) : FieldWeakHessian := by
  intro P D hP hD σ j
  have hf : ∀ κ ∈ D.keys, IsKeyFieldSmooth (keyVector P κ (D.amp κ) σ) := by
    intro κ hκ
    by_cases h0 : κ.label.1 = 0
    · exact htwo P D κ σ hP hD hκ h0
    · exact hone P D κ σ hP hD hκ h0
  exact Internal.weakSecondDeriv_of_keys (f := fun κ => keyVector P κ (D.amp κ) σ) hf j

end GivenShape

end CertCell

end Breakdown
