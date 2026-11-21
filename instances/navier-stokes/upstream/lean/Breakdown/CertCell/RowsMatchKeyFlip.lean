import Breakdown.CertCell.RowsMatchKeyFlipMain
import Breakdown.CertCell.HarmonicProfiles

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField
  CellCalculus

namespace Internal.OddKeyStream

open CellCalculus.Internal.HarmonicProfiles in
theorem timeMode_lift (m : ℕ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hv : IsPeriodicSecondOrder v G H) (ν n : ℤ) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 →
      (∀ a, modeVel (ν, n * m) v 0 (planePoint p) a
          = modeVec m n (harmonicCos ν v) p.1 p.2 a + Complex.I * modeVec m n (harmonicSin ν v) p.1 p.2 a) ∧
      (∀ a b, modeGrad (ν, n * m) G 0 (planePoint p) (a, b)
          = gradMode m n (harmonicCos ν G) a b p + Complex.I * gradMode m n (harmonicSin ν G) a b p) := by
  filter_upwards [ae_integrable_orbit (fun z : ℝ × Space => v z.1 z.2) hv.measurable_velocity
      (box_velocity v G H hv),
    ae_integrable_orbit (fun z : ℝ × Space => G z.1 z.2) hv.measurable_gradient (box_gradient v G H hv)]
    with p hpv hpG hp0
  refine ⟨fun a => ?_, fun a b => ?_⟩
  · have h := mode_split _ (hpv hp0) (fun τ θ => by simp only [rot_add_two_pi]) (velFun a)
      (continuous_velFun a) (velFun_bound a) (velFun_periodic a) ν (n * m)
    simp only [modeVel, modeAverage, modeVec, zero_add, rot_neg_apply, frameVec_eq, cylPoint_eq_rot,
      harmonicCos, harmonicSin, azimuth]
    simp only [velFun, innerSL_apply_apply, Coercive.Internal.ModeRotation.expFactor] at h
    push_cast at h ⊢
    exact h
  · have h := mode_split _ (hpG hp0) (fun τ θ => by simp only [rot_add_two_pi]) (gradFun a b)
      (continuous_gradFun a b) (gradFun_bound a b) (gradFun_periodic a b) ν (n * m)
    simp only [modeGrad, modeAverage, zero_add, rot_unitVector, rot_neg_apply, gradMode, modeMat, frameMat_eq,
      cylPoint_eq_rot, harmonicCos, harmonicSin, azimuth]
    simp only [gradFun, velFun, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply, Coercive.Internal.ModeRotation.expFactor] at h
    push_cast at h ⊢
    exact h

end Internal.OddKeyStream

open PlaneFlipFacts PlaneOdd.Internal CellCert.CellCoordinates

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem oddStreamKeyZero_holds (hF : PlanePairInternal.PlaneTraceFacts) {D : CellLayerData k C nE nM}
    (L : CellLayout) (hL : L.order = D.azimuthOrder) : OddStreamKeyZero D L := by
  intro q v G H g Pg hyp ν hν r hr
  obtain ⟨-, hmc, hpert, -, -⟩ := hyp
  have hv := hF.second _ _ _ _ _ _ hpert
  obtain ⟨hc, hs, -⟩ := hF.lift L.order v G H hv ν
  have hlift := Internal.OddKeyStream.timeMode_lift L.order v G H hv ν 0
  simp only [zero_mul] at hlift
  show heightStripMoment 0 (0 + 1) 0 r (fun r => r) (fun p => modeVec L.order 0 (harmonicCos ν v) p.1 p.2 2)
        (gradMode L.order 0 (harmonicCos ν G) 2 2) (fun _ => 1)
      + Complex.I * heightStripMoment 0 (0 + 1) 0 r (fun r => r)
        (fun p => modeVec L.order 0 (harmonicSin ν v) p.1 p.2 2) (gradMode L.order 0 (harmonicSin ν G) 2 2)
        (fun _ => 1) = 0
  by_cases hlh : (0 : ℝ) < r
  swap
  · rw [strip_null _ _ _ _ _ _ _ _ hlh, strip_null _ _ _ _ _ _ _ _ hlh, mul_zero, add_zero]
  have hh : (0 : ℝ) < 0 + 1 := by norm_num
  have hK : IsCompact (Icc 0 r ×ˢ Icc (min (0 : ℝ) (0 + 1)) (max (0 : ℝ) (0 + 1))) := isCompact_Icc.prod isCompact_Icc
  have hM : MeasurableSet (Icc 0 r ×ˢ Icc (min (0 : ℝ) (0 + 1)) (max (0 : ℝ) (0 + 1))) :=
    measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨cV, cG⟩ := mode_int hc L.order (hi := r) (z₁ := min (0 : ℝ) (0 + 1)) (z₂ := max (0 : ℝ) (0 + 1)) le_rfl
  obtain ⟨sV, sG⟩ := mode_int hs L.order (hi := r) (z₁ := min (0 : ℝ) (0 + 1)) (z₂ := max (0 : ℝ) (0 + 1)) le_rfl
  rw [strip_combine (wt := fun r => r) (t := fun _ => (1 : ℝ)) (F := planeVelocity (ν, 0) v 2) (dF := planeGrad (ν, 0) G 2 2)
    (strip_integrable hK (cV 2) (cG 2 2) 0 (0 + 1) continuous_id' continuous_const)
    (strip_integrable hK (sV 2) (sG 2 2) 0 (0 + 1) continuous_id' continuous_const)
    (by
      filter_upwards [ae_restrict_pos hM (fun p hp => hp.1.1) hlift] with p hp
      exact ⟨hp.1 2, hp.2 2 2⟩)]
  have e := (hF.strip _ _ v G H g hpert hmc.flip (ν, 0) 2 0 r (0 + 1) (0 + 1) (fun r => r) (fun _ => 1) le_rfl hlh
    hh hh continuous_id' continuous_const).1
  rw [flipLabel_axis, show frameSign (2 : Fin 3) = -1 by simp [frameSign]] at e
  push_cast at e
  linear_combination e / 2

theorem keyPlaneFlip_holds (hF : PlanePairInternal.PlaneTraceFacts) {D : CellLayerData k C nE nM}
    (L : CellLayout) (hL : L.order = D.azimuthOrder) : KeyPlaneFlip D L :=
  keyPlaneFlip_of hF L hL (oddStreamKeyZero_holds hF L hL)

end Assembly

end CertCell

end Breakdown
