import Breakdown.CertCell.BridgeTraceStatements
import Breakdown.CertCell.PeriodicSecondOrder
import Breakdown.CertCell.VelocitySixthIntegral
import Breakdown.CertCell.SixthPower
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.CertCell.LocalModeIntegrable

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

namespace Internal.AxisPlain

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy
  LocalField CellCalculus CellCalculus.Internal.HarmonicProfiles

theorem plane_lift (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hv : IsPeriodicSecondOrder v G H) (ν k : ℤ) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 →
      (∀ a, modeVel (ν, k) v 0 (planePoint p) a
          = modeVec 1 k (harmonicCos ν v) p.1 p.2 a + Complex.I * modeVec 1 k (harmonicSin ν v) p.1 p.2 a) ∧
      (∀ a b, modeGrad (ν, k) G 0 (planePoint p) (a, b)
          = gradMode 1 k (harmonicCos ν G) a b p + Complex.I * gradMode 1 k (harmonicSin ν G) a b p) := by
  have hlab : ((ν, k) : ℤ × ℤ) = (ν, k * ((1 : ℕ) : ℤ)) := by simp
  filter_upwards [ae_integrable_orbit (fun z : ℝ × Space => v z.1 z.2) hv.measurable_velocity
      (box_velocity v G H hv),
    ae_integrable_orbit (fun z : ℝ × Space => G z.1 z.2) hv.measurable_gradient (box_gradient v G H hv)]
    with p hpv hpG hp0
  refine ⟨fun a => ?_, fun a b => ?_⟩
  · have h := mode_split _ (hpv hp0) (fun τ θ => by simp only [rot_add_two_pi]) (velFun a)
      (continuous_velFun a) (velFun_bound a) (velFun_periodic a) ν (k * ((1 : ℕ) : ℤ))
    rw [hlab]
    simp only [modeVel, modeAverage, modeVec, zero_add, rot_neg_apply, frameVec_eq, cylPoint_eq_rot,
      harmonicCos, harmonicSin, azimuth]
    simp only [velFun, innerSL_apply_apply, Coercive.Internal.ModeRotation.expFactor] at h
    push_cast at h ⊢
    exact h
  · have h := mode_split _ (hpG hp0) (fun τ θ => by simp only [rot_add_two_pi]) (gradFun a b)
      (continuous_gradFun a b) (gradFun_bound a b) (gradFun_periodic a b) ν (k * ((1 : ℕ) : ℤ))
    rw [hlab]
    simp only [modeGrad, modeAverage, zero_add, rot_unitVector, rot_neg_apply, gradMode, modeMat, frameMat_eq,
      cylPoint_eq_rot, harmonicCos, harmonicSin, azimuth]
    simp only [gradFun, velFun, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply, Coercive.Internal.ModeRotation.expFactor] at h
    push_cast at h ⊢
    exact h

theorem ae_radius_pos (hi zlo zhi : ℝ) :
    ∀ᵐ p ∂(volume.restrict (Set.Icc (0 : ℝ) hi ×ˢ Set.Icc zlo zhi)), 0 < p.1 := by
  have hnull : (volume : Measure (ℝ × ℝ)) (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have h0 := measure_eq_zero_iff_ae_notMem.1 hnull
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc), ae_restrict_of_ae h0]
    with p hp hn
  have hne : p.1 ≠ 0 := fun h => hn ⟨h, trivial⟩
  exact lt_of_le_of_ne hp.1.1 (Ne.symm hne)

end Internal.AxisPlain

open Internal.AxisPlain CellCalculus in
theorem modeAxisPlainIntegrable (hE : Bridge.HessianEnergyIdentityHolds) : ModeAxisPlainIntegrableHolds := by
  intro Γ P v G H g hp ξ a b hi zlo zhi _ _
  have hV : Bridge.VelocitySixthIntegralHolds :=
    Bridge.velocitySixthIntegral ⟨_, sixthPowerGradientBound_four_thirds⟩
  have hP : IsPeriodicSecondOrder v G H := periodicSecondOrder_of_perturbation hV hE Γ P v G H g hp
  have hL := harmonic_local v G H hP ξ.1
  have hC := LocalField.localModeStripIntegrable 1 _ _ _ hL.1 ξ.2 hi zlo zhi
  have hS := LocalField.localModeStripIntegrable 1 _ _ _ hL.2 ξ.2 hi zlo zhi
  have hlift := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) hi ×ˢ Set.Icc zlo zhi) (plane_lift v G H hP ξ.1 ξ.2)
  have hpos := ae_radius_pos hi zlo zhi
  refine ⟨((hC.1 a).add ((hS.1 a).const_mul Complex.I)).congr ?_,
    ((hC.2 a b).add ((hS.2 a b).const_mul Complex.I)).congr ?_⟩
  · filter_upwards [hlift, hpos] with p h1 h2
    simp only [Pi.add_apply, planeVelocity]
    rw [(h1 h2).1 a]
  · filter_upwards [hlift, hpos] with p h1 h2
    simp only [Pi.add_apply, planeGrad]
    rw [(h1 h2).2 a b]

end SideTrace

end CertCell

end Breakdown
