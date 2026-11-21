import Breakdown.CertCell.BridgeTraceStatements
import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.CertCell.SideTrace

open Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.CellAnalysis Breakdown.CellCert.CellFormula
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.FracInternal.ModeHeightAxis Breakdown.FracInternal.ModeRectIntegrable
open Breakdown.FracInternal.MeshDataAffineModes Breakdown.FracInternal.ModeStripIntegrable

namespace Internal.PressureModeIntegrable

theorem squareNear_compact {Q : Space → Space} (hQ : IsSquareIntegrableNear Q) :
    IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2) := by
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  have hm : AEStronglyMeasurable (fun y => ‖Q y‖ ^ 2) volume := hQ.1.norm.pow 2
  have hI : IntegrableOn (fun y => ‖Q y‖ ^ 2) (Metric.closedBall (0 : Space) R) :=
    ⟨hm.restrict, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)).2 (hQ.2 R)⟩
  exact hI.mono_set hR

theorem weightedMode_integrable {Q : Space → Space} (hQ : IsSquareIntegrableNear Q) (m : ℕ) (n : ℤ)
    (b : Fin 3) (hi zlo zhi : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeVec m n Q p.1 p.2 b) (Icc 0 hi ×ˢ Icc zlo zhi) := by
  have hQloc : LocallyIntegrable Q volume := locInt_of_sq hQ.1 (squareNear_compact hQ)
  have hSm : MeasurableSet (Icc (0 : ℝ) hi ×ˢ Icc zlo zhi) := measurableSet_Icc.prod measurableSet_Icc
  refine IntegrableOn.congr_fun (IntegrableOn.mono_set ((weighted_int hi (|zlo| + |zhi|) hQloc (velKernel m n b)
    (velKernel_cont m n b) (velKernel_bound m n b)).const_mul (1 / (2 * π) : ℂ))
      (strip_sub hi zlo zhi)) (fun p _ => ?_) hSm
  rw [modeVec_k, mode_ioo _ (velKernel_per m n b)]
  ring

theorem pressureMode_integrable {Q : Space → Space} {q : Space → ℝ} (hq : IsPotentialOf Q q)
    (hQ : IsSquareIntegrableNear Q) (m : ℕ) (n : ℤ) (hi zlo zhi : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => presMode m n q p.1 p.2) (Icc 0 hi ×ˢ Icc zlo zhi) := by
  set Z : ℝ := |zlo| + |zhi| with hZ
  have hsub := strip_sub hi zlo zhi
  have hSm : MeasurableSet (Icc (0 : ℝ) hi ×ˢ Icc zlo zhi) := measurableSet_Icc.prod measurableSet_Icc
  set ρ : ℝ := 2 * |hi| + |Z| + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hχ : IsTestScalar (radialCutoff ρ) :=
    ⟨contDiff_radialCutoff hρ0, hasCompactSupport_radialCutoff hρ0⟩
  have hχ1 : ∀ y, |radialCutoff ρ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (radialCutoff_nonneg ρ y)]
    exact radialCutoff_le_one ρ y
  have h6 := pot_six hq hQ.1 (squareNear_compact hQ) hχ hχ1
  refine IntegrableOn.congr_fun (IntegrableOn.mono_set ((six_int hi Z h6 (presKernel m n) (presKernel_cont m n)
    (presKernel_bound m n)).const_mul (1 / (2 * π) : ℂ)) hsub) (fun p hp => ?_) hSm
  rw [presMode_k, mode_ioo _ (presKernel_per m n)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  have hp' := hsub hp
  have hn : ‖cylPoint p.1 θ p.2‖ ≤ ρ := by
    refine (cylPoint_norm _ _ _).trans ?_
    have h1 : |p.1| ≤ |hi| := by
      rw [abs_of_nonneg hp'.1.1]
      exact hp'.1.2.trans (le_abs_self _)
    have h2 : |p.2| ≤ |Z| :=
      abs_le.2 ⟨by linarith [hp'.2.1, le_abs_self Z, neg_abs_le Z], hp'.2.2.trans (le_abs_self _)⟩
    rw [hρ]
    linarith
  simp only [radialCutoff_eq_one hρ0 hn, one_mul]

theorem offAxisMode_integrable {Q : Space → Space} (hQ : IsSquareIntegrableNear Q) (m : ℕ) (n : ℤ)
    (b : Fin 3) {lo hi : ℝ} (zlo zhi : ℝ) (hlo : 0 < lo) :
    IntegrableOn (fun p : ℝ × ℝ => modeVec m n Q p.1 p.2 b) (Icc lo hi ×ˢ Icc zlo zhi) := by
  have hS : MeasurableSet (Icc lo hi ×ˢ Icc zlo zhi) := measurableSet_Icc.prod measurableSet_Icc
  have hK : IsCompact (Icc lo hi ×ˢ Icc zlo zhi) := isCompact_Icc.prod isCompact_Icc
  have hW := (weightedMode_integrable hQ m n b hi zlo zhi).mono_set
    (prod_mono (Icc_subset_Icc_left hlo.le) (Subset.refl (Icc zlo zhi)))
  have hne : ∀ p ∈ Icc lo hi ×ˢ Icc zlo zhi, (p.1 : ℂ) ≠ 0 := fun p hp =>
    Complex.ofReal_ne_zero.2 (ne_of_gt (lt_of_lt_of_le hlo hp.1.1))
  have hc : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ)⁻¹) (Icc lo hi ×ˢ Icc zlo zhi) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn.inv₀ hne
  refine (IntegrableOn.continuousOn_mul_of_subset hc hW hK hS (Subset.refl _)).congr_fun
    (fun p hp => ?_) hS
  exact inv_mul_cancel_left₀ (hne p hp) _

end Internal.PressureModeIntegrable

end Breakdown.CertCell.SideTrace

namespace Breakdown.CertCell.SideTrace

open Internal.PressureModeIntegrable

theorem pressureModeIntegrable : PressureModeIntegrableHolds := by
  intro m Q q _ hq hQ n b hi zlo zhi _ _
  exact ⟨pressureMode_integrable hq hQ m n hi zlo zhi, weightedMode_integrable hQ m n b hi zlo zhi,
    fun lo hlo _ => offAxisMode_integrable hQ m n b zlo zhi hlo⟩

end Breakdown.CertCell.SideTrace
