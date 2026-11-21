import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.FracCell.AngularFrame
import Breakdown.FracCell.CircleWeak

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open CellCert.CellEnergy.Internal.AngularFrame

theorem localAngularFrame : LocalAngularFrameStatement := by
  intro m v G H hF K hK n a b
  have locG : ∀ i, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i =>
    locInt_vec (meas_G hF.measurable_gradient i) hF.gradient_two fun y => G_sq_le (G y) i
  have locH : ∀ j i, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume := fun j i =>
    locInt_vec (meas_H hF.measurable_second j i) hF.second_two fun y => H_sq_le (H y) j i
  have locf : ∀ i l, LocallyIntegrable (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) volume :=
    fun i l => locInt_sq ((meas_G hF.measurable_gradient i).inner aestronglyMeasurable_const)
      hF.gradient_two fun y => (inner_sq_le _ l).trans (G_sq_le (G y) i)
  have locs : ∀ j i l, LocallyIntegrable (fun y => inner ℝ (H y (unitVector j) (unitVector i)) (unitVector l))
      volume := fun j i l => locInt_sq ((meas_H hF.measurable_second j i).inner aestronglyMeasurable_const)
      hF.second_two fun y => (inner_sq_le _ l).trans (H_sq_le (H y) j i)
  have locg : ∀ i l, LocallyIntegrable (fun y => gv (H y) i l) volume := by
    intro i l
    unfold gv
    refine locallyIntegrable_finsetSum Finset.univ fun j _ => ?_
    exact locallyIntegrable_iff.2 fun C hC => ((locs j i l).integrableOn_isCompact hC).smul_const _
  have hweak : ∀ i l, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l) =
        -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
    intro i l φ hφ j
    have hw := hF.weak_second φ hφ i j
    have hcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
    have hi1 := (locG i).integrable_smul_left_of_hasCompactSupport hcont hsupp
    have hi2 := (locH j i).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    set Λ : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    calc ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l)
        = ∫ y, Λ (fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp [Λ, innerSL_apply_apply, real_inner_comm]
      _ = Λ (∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := Λ.integral_comp_comm hi1
      _ = -Λ (∫ y, φ y • H y (unitVector j) (unitVector i)) := by rw [hw, map_neg]
      _ = -∫ y, Λ (φ y • H y (unitVector j) (unitVector i)) := by rw [Λ.integral_comp_comm hi2]
      _ = -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [gv_inner]
          simp [Λ, innerSL_apply_apply, real_inner_comm]
  have hKer := fun i l => circleWeak (fun y => inner ℝ (G y (unitVector i)) (unitVector l))
    (fun y => gv (H y) i l) (locf i l) (locg i l) (hweak i l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l => (hKer i l).1
  have hid := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l =>
    (hKer i l).2 (wgt (azimuth m n) a b i l) (wgt_smooth _ a b i l) (hk ▸ wgt_periodic _ a b i l)
  have h0 : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
    have hnull : volume ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = 0 := by
      rw [show ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) by
        ext p; simp, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with p hp
    simpa using hp
  have hrect : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  rw [ae_restrict_iff' hrect]
  filter_upwards [hint, hid, h0] with p h1 h2 h3 hp
  have hr : 0 < p.1 := lt_of_le_of_ne (hK.r_order.1.trans hp.1.1) (Ne.symm h3)
  obtain ⟨r, z⟩ := p
  exact point m n G H a b r z (fun i l => (h1 i l hr).1) (fun i l => (h1 i l hr).2)
    (fun i l => h2 i l hr)

end LocalField

end CertCell

end Breakdown
