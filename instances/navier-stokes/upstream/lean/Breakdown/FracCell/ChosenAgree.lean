import Breakdown.FracCell.StClauses

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

namespace ChosenAgreeInternal

theorem map_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A B : Space →L[ℝ] E} (h : ∀ j, A (unitVector j) = B (unitVector j)) : A = B := by
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun j => ?_
  simpa [unitVector] using h j

theorem column_local (G : Space → (Space →L[ℝ] Space)) (hm : AEStronglyMeasurable G volume)
    (h2 : Integrable (fun y => entrySq (G y))) (j : Fin 3) :
    LocallyIntegrable (fun y => G y (unitVector j)) volume := by
  have hmj := hm.apply_continuousLinearMap (unitVector j)
  have hL : MemLp (fun y => G y (unitVector j)) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hmj).2 (h2.mono' (hmj.norm.pow 2) (ae_of_all _ fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  exact hL.locallyIntegrable (by norm_num)

theorem entry_local (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hm : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2))
    (i j : Fin 3) : LocallyIntegrable (fun y => H y (unitVector i) (unitVector j)) volume := by
  have hmj := (hm.apply_continuousLinearMap (unitVector i)).apply_continuousLinearMap (unitVector j)
  have hL : MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hmj).2 (h2.mono' (hmj.norm.pow 2) (ae_of_all _ fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc ‖H y (unitVector i) (unitVector j)‖ ^ 2
        ≤ ∑ b : Fin 3, ‖H y (unitVector i) (unitVector b)‖ ^ 2 :=
          Finset.single_le_sum (f := fun b => ‖H y (unitVector i) (unitVector b)‖ ^ 2)
            (fun b _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖H y (unitVector a) (unitVector b)‖ ^ 2 :=
          Finset.single_le_sum (f := fun a => ∑ b : Fin 3, ‖H y (unitVector a) (unitVector b)‖ ^ 2)
            (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ i)
  exact hL.locallyIntegrable (by norm_num)

end ChosenAgreeInternal

open ChosenAgreeInternal in
theorem chosenAgree : ChosenAgreeStatement := by
  intro m v G H hS
  have hex : ∃ G H, IsSecondOrderField m v G H := ⟨G, H, hS⟩
  have hS' : IsSecondOrderField m v (FracCellData.chosenGrad m v) (FracCellData.chosenSecond m v) := by
    rw [FracCellData.chosenGrad, FracCellData.chosenSecond, dif_pos hex, dif_pos hex]
    exact hex.choose_spec.choose_spec
  have hcol : ∀ j : Fin 3, (fun y => FracCellData.chosenGrad m v y (unitVector j)) =ᵐ[volume]
      fun y => G y (unitVector j) := fun j =>
    ae_eq_of_integral_contDiff_smul_eq (column_local _ hS'.measurable_gradient hS'.gradient_two j)
      (column_local _ hS.measurable_gradient hS.gradient_two j) fun g hg hgc => by
        have h1 := hS'.weak_gradient g ⟨hg, hgc⟩ j
        have h2 := hS.weak_gradient g ⟨hg, hgc⟩ j
        rw [h1] at h2
        exact neg_injective h2
  have hGe : FracCellData.chosenGrad m v =ᵐ[volume] G := by
    filter_upwards [ae_all_iff.2 hcol] with y hy
    exact map_ext fun j => hy j
  refine ⟨hGe, ?_⟩
  have hent : ∀ j i : Fin 3, (fun y => FracCellData.chosenSecond m v y (unitVector j) (unitVector i)) =ᵐ[volume]
      fun y => H y (unitVector j) (unitVector i) := fun j i =>
    ae_eq_of_integral_contDiff_smul_eq (entry_local _ hS'.measurable_second hS'.second_two j i)
      (entry_local _ hS.measurable_second hS.second_two j i) fun g hg hgc => by
        have h1 := hS'.weak_second g ⟨hg, hgc⟩ i j
        have h2 := hS.weak_second g ⟨hg, hgc⟩ i j
        have h3 : (∫ y, fderiv ℝ g y (unitVector j) • FracCellData.chosenGrad m v y (unitVector i)) =
            ∫ y, fderiv ℝ g y (unitVector j) • G y (unitVector i) := by
          refine integral_congr_ae ?_
          filter_upwards [hGe] with y hy
          rw [hy]
        rw [h1, h2] at h3
        exact neg_injective h3
  have hall : ∀ᵐ y ∂volume, ∀ j i : Fin 3,
      FracCellData.chosenSecond m v y (unitVector j) (unitVector i) = H y (unitVector j) (unitVector i) := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    exact fun i => hent j i
  filter_upwards [hall] with y hy
  exact map_ext fun j => map_ext fun i => hy j i

end CellCert

end Breakdown
