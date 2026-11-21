import Breakdown.CertCell.CreditEvalStatements
import Breakdown.CertCell.StripDataFlipLinks

open MeasureTheory Set Matrix

noncomputable section

namespace Breakdown.CertCell.CreditEval

namespace Internal.OwnerEvalLinks

open CellCert.CellFormula CellCalculus Bridge Bridge.Internal.StripFlipLinks

theorem mode_of_labelTime (ι : ℤ × ℤ) : harmonicMode (labelTime ι) ι.1 = ι := by
  unfold harmonicMode labelTime
  ext
  · rfl
  · simp only
    have h : ι.1 + (2 * ι.2 - ι.1) = 2 * ι.2 := by ring
    rw [h]
    omega

theorem even_label_sum (ι : ℤ × ℤ) : Even (ι.1 + labelTime ι) := by
  unfold labelTime
  exact ⟨ι.2, by ring⟩

theorem zero_isGradientField : SteadyCert.IsGradientField (0 : Space → Space) := by
  refine ⟨fun _ => 0, fun K _ => ?_, fun K _ => ?_, aestronglyMeasurable_const, fun φ _ j => ?_⟩ <;> simp

theorem zero_isPeriodicPressure : IsPeriodicPressure (0 : ℝ → Space → Space) := by
  refine ⟨?_, fun _ _ => rfl, fun R => by simp, fun ν => ?_⟩
  · simp only [Pi.zero_apply]
    exact aestronglyMeasurable_const
  · have hc : harmonicCos ν (0 : ℝ → Space → Space) = 0 := by
      funext y
      simp [harmonicCos]
    have hs : harmonicSin ν (0 : ℝ → Space → Space) = 0 := by
      funext y
      simp [harmonicSin]
    rw [hc, hs]
    exact ⟨zero_isGradientField, zero_isGradientField⟩

theorem sideVelocity_pressure_free (A : CellModeLayouts) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg Pg' : ℝ → Space → Space) (m : (A.layout ι).modes) (s : Fin (A.layout ι).segCount) (a : Fin 3)
    (e : Fin ((A.layout ι).degSide + 2)) :
    modeData A ι v G H Pg (CellDatum.sideVelocity m s a e) = modeData A ι v G H Pg' (CellDatum.sideVelocity m s a e) := by
  unfold modeData harmonicData CellLayout.trueData CellDatum.sideVelocity
  simp only [Sum.elim_inl, Sum.elim_inr, CellLayout.gradModeOf, cosTuple, sinTuple]
  rfl

theorem strip_height_eq (hM : StripMomentTraceHolds) (hT : TraceHeightHolds) (hD : ModeHeightDerivHolds)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g) (ξ : ℤ × ℤ) {h h' lo hi : ℝ}
    {t : ℝ → ℝ} (hh : 0 < h) (hh' : 0 < h') (hlo : 0 < lo) (hlohi : lo < hi) (ht : Continuous t) :
    heightStripMoment 0 h lo hi (fun _ => 1) (fun p => planeVel ξ v 2 p.1 p.2)
        (fun p => planeVelHeight ξ G 2 p.1 p.2) t
      = heightStripMoment 0 h' lo hi (fun _ => 1) (fun p => planeVel ξ v 2 p.1 p.2)
        (fun p => planeVelHeight ξ G 2 p.1 p.2) t := by
  obtain ⟨iF, iFz, -⟩ := plane_rect_integrable hp ξ 2 (a₁ := lo) (b₁ := hi) (c₁ := 0) (d₁ := h) hlo
  obtain ⟨iF', iFz', -⟩ := plane_rect_integrable hp ξ 2 (a₁ := lo) (b₁ := hi) (c₁ := 0) (d₁ := h') hlo
  rw [hM h lo hi (fun _ => 1) t _ _ hh hlohi iF iFz continuous_const ht,
    hM h' lo hi (fun _ => 1) t _ _ hh' hlohi iF' iFz' continuous_const ht]
  have hDa := hD Γ P v G H g hp ξ 2
  rw [ae_restrict_iff' measurableSet_Ioi] at hDa
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hDa] with r hr hmem
  rw [uIoc_of_le hlohi.le] at hmem
  have h2 := hr (hlo.trans hmem.1)
  exact congrArg _ (trace_eq_at_heights hT (fun k hk => (h2 k hk).1) hh hh')

end Internal.OwnerEvalLinks

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus Internal.OwnerEvalLinks in
theorem creditEvalMatches
    (hP : ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
      IsPerturbation Γ P v G H g → IsPeriodicSecondOrder v G H)
    (hS : HarmonicSideDataStatement) (hT : Bridge.TraceHeightHolds) (hD : Bridge.ModeHeightDerivHolds)
    (hM : Bridge.StripMomentTraceHolds) : CreditEvalMatchesHolds := by
  intro k C nE nM D R hC q hq v G H g hpert Pg κ ζ η j
  funext d
  obtain ⟨n, s, e, hn, hx, hrad, hlev, hoth, hlo, hhi, htest⟩ := hC.side_datum j d
  have hpso := hP _ _ v G H g hpert
  obtain ⟨c, S, hco, -, hcl⟩ :=
    (hC.layouts_valid (R.creditOwner j d)).layout_valid _ (R.creditCoord j d).1.2
  have hL : IsHarmonicLayout D.azimuthOrder (D.mesh.box (R.creditOwner j d))
      (R.layouts (R.creditOwner j d)).bases
      ((R.layouts (R.creditOwner j d)).layout (R.creditCoord j d).1.1).modes
      ((R.layouts (R.creditOwner j d)).layout (R.creditCoord j d).1.1) :=
    ⟨c, S, hco, hcl.modes_eq.symm, hcl⟩
  have hev : Even ((n : ℤ) + labelTime (R.creditCoord j d).1.1) := by
    rw [hn]
    exact even_label_sum _
  have key := (hS D.azimuthOrder _ _ _ hL v G H 0 hpso zero_isPeriodicPressure
    (labelTime (R.creditCoord j d).1.1) n hev).1 s 2 e
  rw [hn, mode_of_labelTime] at key
  have hseg := (hC.patches_valid j).segments ((R.creditPatch j).dataOf d).1
  have htf : (((R.layouts (R.creditOwner j d)).layout (R.creditCoord j d).1.1).segment s).test (e : ℕ)
      = ((R.creditPatch j).segment ((R.creditPatch j).dataOf d).1).test ((R.creditPatch j).dataOf d).2 :=
    funext htest
  show modeData (R.layouts (R.creditOwner j d)) (R.creditCoord j d).1.1 v G H Pg (R.creditCoord j d).2 = _
  rw [hx, sideVelocity_pressure_free _ _ v G H Pg 0]
  unfold modeData
  rw [key]
  unfold FaceSegment.moment
  simp only [hrad, if_false, hlev, hlo, hhi, htf, Bool.false_eq_true]
  unfold Bridge.CreditPatch.data Bridge.PlaneSegment.velocityData
  rw [← hC.mode_label j d]
  exact strip_height_eq hM hT hD hpert _ hoth hseg.height_pos hseg.lower_pos hseg.lower_lt_upper
    (hseg.test_continuous _)

end Breakdown.CertCell.CreditEval
