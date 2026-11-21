import Breakdown.CertCell.AssemblyStatements
import Breakdown.FracCell.AngularMode
import Breakdown.FracCell.CircleWeak

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open SteadyCert CellCert.CellAnalysis CellCert.CellFormula CellCalculus CellCert.CellEnergy

namespace TurnedProfile

open CellCert.CellFormula.Internal.AngularMode in
theorem angular_local (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hs : LocalField.IsLocalSecondOrderField v G H) (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * gradMode m n G 0 1 p =
          ((azimuth m n : ℂ) * Complex.I) * modeVec m n v p.1 p.2 0 - modeVec m n v p.1 p.2 1 ∧
      (p.1 : ℂ) * gradMode m n G 1 1 p =
          ((azimuth m n : ℂ) * Complex.I) * modeVec m n v p.1 p.2 1 + modeVec m n v p.1 p.2 0 ∧
      (p.1 : ℂ) * gradMode m n G 2 1 p = ((azimuth m n : ℂ) * Complex.I) * modeVec m n v p.1 p.2 2 := by
  have locv : LocallyIntegrable v volume := hs.velocity_six.locallyIntegrable (by norm_num)
  have locG := loc_col hs.measurable_gradient hs.gradient_two
  have locf : ∀ l, LocallyIntegrable (fc v l) volume := fun l => loc_inner locv (unitVector l)
  have locg : ∀ l, LocallyIntegrable (gc G l) volume := by
    intro l
    unfold gc
    refine locallyIntegrable_finsetSum Finset.univ fun i _ => ?_
    exact locallyIntegrable_iff.2 fun K hK =>
      ((loc_inner (locG i) (unitVector l)).integrableOn_isCompact hK).smul_const _
  have hweak : ∀ l, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * fc v l y = -∫ y, φ y * inner ℝ (gc G l y) (unitVector j) := by
    intro l φ hφ j
    have hw := hs.weak_gradient φ hφ j
    have hcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
    have hi1 := locv.integrable_smul_left_of_hasCompactSupport hcont hsupp
    have hi2 := (locG j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    calc ∫ y, fderiv ℝ φ y (unitVector j) * fc v l y
        = ∫ y, L (fderiv ℝ φ y (unitVector j) • v y) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp [L, fc, innerSL_apply_apply, real_inner_comm]
      _ = L (∫ y, fderiv ℝ φ y (unitVector j) • v y) := L.integral_comp_comm hi1
      _ = -L (∫ y, φ y • G y (unitVector j)) := by rw [hw, map_neg]
      _ = -∫ y, L (φ y • G y (unitVector j)) := by rw [L.integral_comp_comm hi2]
      _ = -∫ y, φ y * inner ℝ (gc G l y) (unitVector j) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [gc_inner]
          simp [L, innerSL_apply_apply, real_inner_comm, unitVector]
  have hK := fun l => circleWeak (fc v l) (gc G l) (locf l) (locg l) (hweak l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun l => (hK l).1
  have hid := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun l =>
    (hK l).2 (wt (azimuth m n) a l) (wt_smooth _ a l) (hk ▸ wt_periodic _ a l)
  filter_upwards [hint, hid] with p h1 h2 hr
  obtain ⟨r, z⟩ := p
  exact point m n v G r z (fun l => (h1 l hr).1) (fun l => (h1 l hr).2) (fun a l => h2 a l hr)

theorem fst_ne_zero_ae : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have e : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ Set.univ := by
    ext p
    simp
  have h0 : volume {p : ℝ × ℝ | p.1 = 0} = 0 := by
    rw [e, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  refine ae_iff.2 ?_
  simp only [ne_eq, not_not]
  exact h0

end TurnedProfile

theorem bandProfileTurned_holds
    (hP : ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
      IsPerturbation Γ P v G H g → IsPeriodicSecondOrder v G H)
    (hL : HarmonicLiftStatement) : BandProfileTurnedHolds := by
  intro k C nE nM D hM K q v G H g κ F Pg ht ι _
  have hv := hP _ _ v G H g ht.perturbation
  have hmode : harmonicMode (labelTime ι) ι.1 = ι := by
    ext
    · rfl
    · simp only [harmonicMode, labelTime]
      omega
  have heven : Even (ι.1 + labelTime ι) := ⟨ι.2, by simp only [labelTime]; ring⟩
  obtain ⟨hc, hs, hlift⟩ := hL D.azimuthOrder v G H hv (labelTime ι)
  have hA := hlift ι.1 heven
  rw [hmode] at hA
  have hC := TurnedProfile.angular_local D.azimuthOrder _ _ _ hc ι.1
  have hS := TurnedProfile.angular_local D.azimuthOrder _ _ _ hs ι.1
  have hpos : ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), 0 < p.1 := by
    filter_upwards [ae_restrict_of_ae TurnedProfile.fst_ne_zero_ae,
      ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hne hp
    exact lt_of_le_of_ne ((hM.box_valid K).r_order.1.trans hp.1.1) (Ne.symm hne)
  filter_upwards [ae_restrict_of_ae hA, ae_restrict_of_ae hC, ae_restrict_of_ae hS, hpos] with p h1 h2 h3 h4
  obtain ⟨hv1, hg1, -⟩ := h1 h4
  obtain ⟨c0, c1, c2⟩ := h2 h4
  obtain ⟨s0, s1, s2⟩ := h3 h4
  have hk : ((labelAzimuth D.azimuthOrder ι : ℤ) : ℂ) = (azimuth D.azimuthOrder ι.1 : ℂ) := by
    simp [labelAzimuth, azimuth]
  intro a
  fin_cases a
  · simp [bandProfile, pairVec, gradArray, velArray, Fin.sum_univ_three, turnMatrix, hk]
    rw [hg1, hv1, hv1]
    linear_combination c0 + Complex.I * s0
  · simp [bandProfile, pairVec, gradArray, velArray, Fin.sum_univ_three, turnMatrix, hk]
    rw [hg1, hv1, hv1]
    linear_combination c1 + Complex.I * s1
  · simp [bandProfile, pairVec, gradArray, velArray, Fin.sum_univ_three, turnMatrix, hk]
    rw [hg1, hv1]
    linear_combination c2 + Complex.I * s2

end Assembly

end CertCell

end Breakdown
