import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.LabelRowProfile
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.CertCell.HarmonicPressureLift
import Breakdown.CertCell.PeriodicSecondOrder
import Breakdown.CertCell.SecondDerivEnergyIdentity
import Breakdown.CertCell.VelocitySixthIntegral
import Breakdown.CertCell.SixthPower

open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.Assembly

open CellCert CellCert.CellAnalysis CellCalculus

namespace Internal.BandIntegrable

theorem pairVec_sq (s : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    ∑ j, ‖pairVec s w j‖ ^ 2 = ∑ a, cnormSq (s a) + cnormSq w := by
  simp [Fin.sum_univ_succ, pairVec, cnormSq]
  ring

theorem pairVec_meas {μ : Measure (ℝ × ℝ)} {s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {w : ℝ × ℝ → Fin 3 → ℂ}
    (hs : ∀ a b, AEStronglyMeasurable (fun p => s p a b) μ) (hw : ∀ a, AEStronglyMeasurable (fun p => w p a) μ)
    (j : Fin 12) : AEStronglyMeasurable (fun p => pairVec (s p) (w p) j) μ := by
  unfold pairVec
  split_ifs
  · exact hs _ _
  · exact hw _

end Internal.BandIntegrable

open Internal.BandIntegrable in
theorem bandProfileIntegrable_holds : BandProfileIntegrableHolds := by
  intro k C nE nM D hM K q v G H g κ F Pg ht ι _
  have hV : Bridge.VelocitySixthIntegralHolds :=
    Bridge.velocitySixthIntegral ⟨_, sixthPowerGradientBound_four_thirds⟩
  have hP : IsPeriodicSecondOrder v G H :=
    periodicSecondOrder_of_perturbation hV Bridge.secondDerivEnergyIdentity _ _ v G H g ht.perturbation
  have hK : IsCellBox (D.mesh.box K) := hM.box_valid K
  obtain ⟨mV, mG, -, -⟩ :=
    CellCalculus.Internal.LabelRowProfile.profile_measurable _ hK D.azimuthOrder v G H Pg hP ht.pressure ι
  have hI := CellCalculus.Internal.LabelRowProfile.profile_integrable harmonicLift_holds
    harmonicPressureLift_holds _ hK D.azimuthOrder v G H Pg hP ht.pressure ι
  have hm : ∀ j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) (volume.restrict (D.mesh.box K).rect) :=
    fun j => pairVec_meas (s := fun p => gradArray D.azimuthOrder ι G p)
      (w := fun p => velArray D.azimuthOrder ι v p) mG mV j
  refine ⟨hm, hI.mono' (continuous_fst.aestronglyMeasurable.mul
    (Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hm j).norm.pow 2)) ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  have hc : ∀ {β : Type} [Fintype β] (x : β → ℂ), 0 ≤ cnormSq x := fun x =>
    Finset.sum_nonneg fun _ _ => by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (Finset.sum_nonneg fun _ _ => by positivity))]
  refine mul_le_mul_of_nonneg_left ?_ h0
  rw [bandProfile, pairVec_sq]
  have h1 := hc (fun a => ∑ c : Fin 3, slopeAt D.azimuthOrder ι H a c c p)
  have h2 := hc (velArray D.azimuthOrder ι Pg p)
  linarith

end Breakdown.CertCell.Assembly
