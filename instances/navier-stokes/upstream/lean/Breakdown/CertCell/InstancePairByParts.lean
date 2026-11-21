import Breakdown.CertCell.InstancePairByPartsMollify
import Breakdown.CertCell.InstancePairByPartsModes

open scoped ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

open Instance

namespace Internal.ByParts

theorem slice_lintegral_finite {F : ℝ → Space → ℝ}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (h : periodLIntegral F < ⊤) :
    ∀ᵐ σ, σ ∈ Set.Icc (0 : ℝ) 1 → ∫⁻ y, ENNReal.ofReal (F σ y) < ⊤ := by
  have hm' : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (F z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    have e : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space) =
        (volume : Measure (ℝ × Space)).restrict (Set.Icc 0 1 ×ˢ Set.univ) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    exact hm.aemeasurable.ennreal_ofReal.restrict
  have h2 := ae_lt_top' hm'.lintegral_prod_right' h.ne
  exact (ae_restrict_iff' measurableSet_Icc).1 h2

theorem sgn_eq_zero_of_not_inPiece {T : Set (ℤ × ℤ)} {ι : ℤ × ℤ} (h : ¬ PieceWeights.inPiece T ι) :
    PieceWeights.sgn T ι = 0 := by
  unfold PieceWeights.inPiece at h
  push Not at h
  simp [PieceWeights.sgn, h.1, h.2]

theorem not_inPiece_of_label {T : Set (ℤ × ℤ)} {m : ℕ} {ι ι' : ℤ × ℤ}
    (hn : ¬ PieceWeights.inPiece T (labelHarmonic m ι')) (he : labelHarmonic m ι' = ι ∨ labelHarmonic m ι' = -ι) :
    ¬ PieceWeights.inPiece T ι := by
  unfold PieceWeights.inPiece at hn ⊢
  rcases he with h | h
  · rwa [h] at hn
  · rw [h, neg_neg] at hn
    exact fun h' => hn h'.symm

end Internal.ByParts

open Internal.ByParts in
theorem actuatorPairingByParts (hgm : ActuatorGradientModes) : ActuatorPairingByParts := by
  intro k C nE nM D S jmax hinst hfmt q hq v G H g hp i
  unfold multiplierRight
  rw [← add_zero (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, matInner (G σ y) (gradField (D.cert.actuator i) σ y))]
  congr 1
  · refine setIntegral_congr_ae measurableSet_Icc ?_
    have hG := slice_lintegral_finite (F := fun σ y => matSq (G σ y))
      (Cert.Internal.ReadingEnergy.continuous_matSq.comp_aestronglyMeasurable hp.measurable_gradient)
      hp.gradient_finite
    have hH := slice_lintegral_finite (F := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)
      ((Cert.Internal.ReadingEnergy.continuous_secondDerivTrace.comp_aestronglyMeasurable
        hp.measurable_secondDeriv).norm.pow 2) hp.sumSecondPartials_finite
    have hD := slice_lintegral_finite (F := fun σ y => matSq (gradField (D.cert.actuator i) σ y))
      (Cert.Internal.ReadingEnergy.continuous_matSq.comp_aestronglyMeasurable (hfmt i).gradient_measurable)
      (hfmt i).gradient_finite
    obtain ⟨Bb, Rb, hbd⟩ := (hfmt i).bounded_support
    filter_upwards [hG, hH, hD, hp.weak_secondDeriv] with σ h1 h2 h3 h4 hσ
    exact Internal.ByPartsMollify.trace_pairing_by_parts ((hfmt i).weak_gradient σ) (fun y => (hbd σ y).1)
      (fun y => (hbd σ y).2) (h3 hσ) h4 (h1 hσ) (h2 hσ)
  · refine (tsum_congr fun ι => ?_).trans tsum_zero
    refine integral_eq_zero_of_ae (Eventually.of_forall fun σ => ?_)
    refine integral_eq_zero_of_ae ?_
    by_cases hι : ∃ ι' ∈ S i, labelHarmonic D.azimuthOrder ι' = ι ∨ labelHarmonic D.azimuthOrder ι' = -ι
    · obtain ⟨ι', hι', he⟩ := hι
      have hb := hinst.modes_bound i ι' hι'
      have hsE : ∀ β, PieceWeights.sgn ((D.pieces q).epsP β).modes ι = 0 := fun β =>
        sgn_eq_zero_of_not_inPiece (not_inPiece_of_label (hinst.eps_avoid q hq β ι' hb.1 hb.2) he)
      have hsM : ∀ β, PieceWeights.sgn ((D.pieces q).muP β).modes ι = 0 := fun β =>
        sgn_eq_zero_of_not_inPiece (not_inPiece_of_label (hinst.mu_avoid q hq β ι' hb.1 hb.2) he)
      filter_upwards with y
      simp [hsE, hsM]
    · push Not at hι
      have hg0 := Internal.ByPartsModes.modeGrad_gradField_ae_zero hgm hinst.azimuth_pos (hfmt i) hι σ
      filter_upwards [hg0, FracInternal.RowTurnPair.axis_null] with y hy hax
      have hv : modeVel ι (D.cert.actuator i) σ y = 0 := by
        by_contra h
        obtain ⟨ι', hι', he⟩ := (hfmt i).modes_in ι σ y hax h
        rcases he with h' | h'
        · exact (hι ι' hι').1 h'
        · exact (hι ι' hι').2 h'
      rw [hy, hv]
      simp [curlOfGrad, cdot]

end InstancePair

end CertCell

end Breakdown
