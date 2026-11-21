import Breakdown.FracCell.AngularFrame
import Breakdown.FracCell.PlaneDeleted
import Breakdown.FracCell.CentreIdentityParts
import Breakdown.FracCell.StAngularHeightMode

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis CellEnergy

namespace Internal.AngularHeightMode

open CellEnergy.Internal.AngularFrame

theorem turn_second (hC : CircleWeakStatement) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hF : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      angularGradMode m n H a b p =
        ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' p := by
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
    exact locallyIntegrable_iff.2 fun K hK => ((locs j i l).integrableOn_isCompact hK).smul_const _
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
    set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    calc ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l)
        = ∫ y, L (fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp [L, innerSL_apply_apply, real_inner_comm]
      _ = L (∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := L.integral_comp_comm hi1
      _ = -L (∫ y, φ y • H y (unitVector j) (unitVector i)) := by rw [hw, map_neg]
      _ = -∫ y, L (φ y • H y (unitVector j) (unitVector i)) := by rw [L.integral_comp_comm hi2]
      _ = -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [gv_inner]
          simp [L, innerSL_apply_apply, real_inner_comm]
  have hKer := fun i l => hC (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) (fun y => gv (H y) i l)
    (locf i l) (locg i l) (hweak i l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l => (hKer i l).1
  have hid := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l =>
    (hKer i l).2 (wgt (azimuth m n) a b i l) (wgt_smooth _ a b i l) (hk ▸ wgt_periodic _ a b i l)
  filter_upwards [hint, hid] with p h1 h2 hr
  obtain ⟨r, z⟩ := p
  exact point m n G H a b r z (fun i l => (h1 i l hr).1) (fun i l => (h1 i l hr).2)
    (fun i l => h2 i l hr)

theorem bil_expand (Hy : Space →L[ℝ] Space →L[ℝ] Space) (u w : Space) :
    Hy u w = ∑ i : Fin 3, ∑ j : Fin 3, (u i * w j) • Hy (unitVector i) (unitVector j) := by
  conv_lhs => rw [vec_expand u, vec_expand w]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

theorem bilin_symm (Hy : Space →L[ℝ] Space →L[ℝ] Space)
    (hs : ∀ i j : Fin 3, Hy (unitVector i) (unitVector j) = Hy (unitVector j) (unitVector i)) (u w : Space) :
    Hy u w = Hy w u := by
  rw [bil_expand Hy u w, bil_expand Hy w u]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hs i j, mul_comm]

theorem third_swap (θ : ℝ) (Hy : Space →L[ℝ] Space →L[ℝ] Space)
    (hs : ∀ i j : Fin 3, Hy (unitVector i) (unitVector j) = Hy (unitVector j) (unitVector i)) (a b c : Fin 3) :
    frameThird θ Hy a b c = frameThird θ Hy a c b := by
  unfold frameThird
  rw [bilin_symm Hy hs]

theorem mode_swap {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hF : IsSecondOrderField m v G H) (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → ∀ a b c : Fin 3, modeThird m n H a b c p = modeThird m n H a c b p := by
  filter_upwards [Internal.PlaneDeleted.cyl_ae (CentreIdentityParts.second_symm_field hF)] with p hp hpos a b c
  have hθ := hp hpos
  have e := Internal.PlaneDeleted.mode_congr m n 1
    (Φ := fun θ => (frameThird θ (H (cylPoint p.1 θ p.2)) a b c : ℂ))
    (Ψ := fun θ => (frameThird θ (H (cylPoint p.1 θ p.2)) a c b : ℂ)) ?_ ?_ ?_
  · rw [one_mul] at e
    exact e
  · intro θ
    simp only [Internal.PlaneDeleted.cyl_per, frameThird, frameUnit, Internal.PlaneDeleted.radial_per,
      Internal.PlaneDeleted.angular_per]
  · intro θ
    simp only [Internal.PlaneDeleted.cyl_per, frameThird, frameUnit, Internal.PlaneDeleted.radial_per,
      Internal.PlaneDeleted.angular_per]
  · filter_upwards [hθ] with θ h
    rw [one_mul, third_swap θ _ h]

end Internal.AngularHeightMode

open Internal.AngularHeightMode in
theorem angularHeightMode_of_circle (hC : CircleWeakStatement) : AngularHeightModeStatement := by
  intro m v G H hF n
  filter_upwards [turn_second hC hF n 0 2, turn_second hC hF n 1 2, turn_second hC hF n 2 2, mode_swap hF n]
    with p h0 h1 h2 hsw hr
  have e0 := h0 hr
  have e1 := h1 hr
  have e2 := h2 hr
  simp [angularGradMode, Fin.sum_univ_three, angularComb, frameTurn] at e0 e1 e2
  rw [hsw hr 0 1 2, hsw hr 1 1 2, hsw hr 2 1 2]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e0
  · linear_combination e1
  · linear_combination e2

end Breakdown.CellCert.CellFormula
