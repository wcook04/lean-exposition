import Breakdown.CertCell.AssemblyTiedParts
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.CertCell.HarmonicSideData
import Breakdown.CertCell.AssemblyPotentialExpandLattice
import Breakdown.CertCell.ClassSupportLinks
import Breakdown.CertCell.ModeOffLattice
import Breakdown.CertCell.ModeShiftRotate
import Breakdown.CertCell.ModeShiftRotateTensor
import Breakdown.CertCell.LabelArithmetic
import Breakdown.CertCell.PeriodicSecondOrder
import Breakdown.CertCell.VelocitySixthIntegral
import Breakdown.CertCell.SixthPower
import Breakdown.CertCell.SecondDerivEnergyIdentity

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField
  CellCalculus

namespace Internal.OddStream

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

theorem not_lattice_of_odd {m : ℕ} (hm : 1 ≤ m) {ν : ℤ} (hν : Odd ν) : ¬ IsLatticeHarmonic m (ν, 0) := by
  rintro ⟨ι, hι⟩
  simp only [labelHarmonic, labelTime, labelAzimuth, Prod.mk.injEq] at hι
  obtain ⟨h1, h2⟩ := hι
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have h0 : ι.1 = 0 := (mul_eq_zero.1 h2).resolve_right hm'
  obtain ⟨k, hk⟩ := hν
  omega

theorem ae_snd_ne_zero : ∀ᵐ p : ℝ × ℝ ∂volume, p.2 ≠ 0 := by
  have h : (volume : Measure (ℝ × ℝ)) (univ ×ˢ {0}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with p hp h0
  exact hp ⟨trivial, h0⟩

theorem strip_combine {μ : Measure (ℝ × ℝ)} {A B : ℝ × ℝ → ℂ} (h : ∀ᵐ p ∂μ, A p = -Complex.I * B p) (e : ℂ) :
    e * ∫ p, A p ∂μ + Complex.I * (e * ∫ p, B p ∂μ) = 0 := by
  rw [integral_congr_ae h, integral_const_mul]
  ring

end Internal.OddStream

open CellCalculus.Internal.HarmonicSide Internal.OddStream in
theorem oddStreamZero_holds : OddStreamZeroStatement := by
  intro m K B L hL Γ P v G H g Pg hv hclass ν hν c
  obtain ⟨cd, S, hco, -, hLay⟩ := hL
  have hord : L.order = m := hLay.order_eq.trans hco
  have hK : IsCellBox K := hLay.box_valid
  have hsec := periodicSecondOrder_of_perturbation
    (Bridge.velocitySixthIntegral ⟨4 / 3, sixthPowerGradientBound_four_thirds⟩) Bridge.secondDerivEnergyIdentity
    Γ P v G H g hv
  have hoff := Internal.StretchPairs.ae_offLattice_zero
    (Bridge.classSupport (Bridge.modeOffLattice Bridge.modeShiftRotate Bridge.modeShiftRotateTensor)
      Bridge.labelArithmetic) hclass hv (ν, 0) (not_lattice_of_odd hclass.order_pos hν)
  rw [ae_restrict_iff' (s := halfPlane) (measurableSet_Ioi.prod measurableSet_Ioi)] at hoff
  have hlift := timeMode_lift m v G H hsec ν 0
  simp only [zero_mul] at hlift
  have hzc : 0 ≤ min (L.corner c).2 (L.cornerOther c).2 := by
    obtain ⟨-, hz, -⟩ := hLay.corner_is_corner c
    rw [(hLay.corner_other c).2]
    have h1 := hK.z_order.1
    have h2 := hK.z_order.2
    rcases hz with h | h <;> rw [h] <;> exact le_min (by linarith) (by linarith)
  have hae : ∀ᵐ p ∂(volume.restrict (Icc 0 (L.corner c).1 ×ˢ
      Icc (min (L.corner c).2 (L.cornerOther c).2) (max (L.corner c).2 (L.cornerOther c).2))),
      modeVec m 0 (harmonicCos ν v) p.1 p.2 2 = -(Complex.I * modeVec m 0 (harmonicSin ν v) p.1 p.2 2) ∧
      gradMode m 0 (harmonicCos ν G) 2 2 p = -(Complex.I * gradMode m 0 (harmonicSin ν G) 2 2 p) := by
    rw [ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)]
    filter_upwards [hoff, hlift, ae_fst_ne_zero, ae_snd_ne_zero] with p h1 h2 h3 h4 hp
    have hp1 : 0 < p.1 := lt_of_le_of_ne hp.1.1 (Ne.symm h3)
    have hp2 : 0 < p.2 := lt_of_le_of_ne (hzc.trans hp.2.1) (Ne.symm h4)
    have hq : p ∈ halfPlane := by
      simp only [halfPlane, mem_prod, mem_Ioi]
      exact ⟨hp1, hp2⟩
    obtain ⟨e1, e2⟩ := h1 hq
    obtain ⟨f1, f2⟩ := h2 hp1
    have a1 := congrFun e1 2
    have a2 := congrFun e2 (2, 2)
    rw [f1 2, Pi.zero_apply] at a1
    rw [f2 2 2, Pi.zero_apply] at a2
    exact ⟨eq_neg_of_add_eq_zero_left a1, eq_neg_of_add_eq_zero_left a2⟩
  have eVc : L.velMode 0 (cosTuple ν v G H Pg) 2 = fun p : ℝ × ℝ => modeVec m 0 (harmonicCos ν v) p.1 p.2 2 := by
    rw [← hord]
    rfl
  have eVs : L.velMode 0 (sinTuple ν v G H Pg) 2 = fun p : ℝ × ℝ => modeVec m 0 (harmonicSin ν v) p.1 p.2 2 := by
    rw [← hord]
    rfl
  have eGc : L.gradModeOf 0 (cosTuple ν v G H Pg) 2 2 = gradMode m 0 (harmonicCos ν G) 2 2 := by
    rw [← hord]
    rfl
  have eGs : L.gradModeOf 0 (sinTuple ν v G H Pg) 2 2 = gradMode m 0 (harmonicSin ν G) 2 2 := by
    rw [← hord]
    rfl
  simp only [harmonicData, CellLayout.trueData, CellDatum.cornerStream, Sum.elim_inr, Sum.elim_inl]
  rw [eVc, eVs, eGc, eGs]
  unfold heightStripMoment
  refine strip_combine ?_ _
  filter_upwards [hae] with p hp
  simp only [hp.1, hp.2]
  ring

end Assembly

end CertCell

end Breakdown
