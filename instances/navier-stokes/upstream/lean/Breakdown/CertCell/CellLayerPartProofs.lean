import Breakdown.CertCell.CellLayerJunctions
import Breakdown.CertCell.ShapeJetScaledAgree
import Breakdown.CertCell.ShapeJetScaledValid
import Breakdown.CertCell.CellLayerConclusion
import Breakdown.CertCell.FormNegativeFinite
import Breakdown.CertCell.RowSharesInstance
import Breakdown.CertCell.ShapeSupportRadius
import Breakdown.CertCell.EnergyLeafBound
import Breakdown.CertCell.HarmonicEnergyValueClosed
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.CertCell.LabelModeFacts
import Breakdown.CertCell.LabelResolvedEnergy
import Breakdown.CertCell.LowSlotFormValue
import Breakdown.CertCell.PeriodicSecondOrder
import Breakdown.CertCell.HarmonicSideData
import Breakdown.CertCell.CreditPatchBound
import Breakdown.CertCell.CreditEvalLinks
import Breakdown.CertCell.AssemblyTrueRegular
import Breakdown.CertCell.AssemblyExteriorNonneg
import Breakdown.CertCell.AssemblyExteriorStretch
import Breakdown.CertCell.AssemblyExteriorValueSetsProof
import Breakdown.CertCell.AssemblyLinkPressure
import Breakdown.CertCell.AssemblyAnnihilatorGradient
import Breakdown.CertCell.AssemblyHarmonicAnnihilator
import Breakdown.CertCell.AssemblyFlipAverage
import Breakdown.CertCell.AssemblyRemainderAnnihilates
import Breakdown.CertCell.AssemblyRemainderRegular
import Breakdown.CertCell.PatchCreditLinks
import Breakdown.CertCell.CouplingInverseCredit
import Breakdown.CertCell.PatchTraceBound
import Breakdown.CertCell.TailExteriorLinks
import Breakdown.CertCell.TailSquareModes
import Breakdown.CertCell.TailSquareSmooth
import Breakdown.CertCell.TailFlipDecay
import Breakdown.CertCell.AssemblyPressureFlip
import Breakdown.CertCell.HarmonicRelations

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

theorem scaledJetParts_closed : GivenShape.ScaledJetParts :=
  ⟨GivenShape.jetParts_closed, GivenShape.scaledSplineAgreementHolds, GivenShape.scaledJetDataHolds⟩

theorem periodicSecondOrder_closed (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) : CellCalculus.IsPeriodicSecondOrder v G H :=
  CellCalculus.periodicSecondOrder_of_perturbation velocitySixthIntegral_closed Bridge.secondDerivEnergyIdentity
    Γ P v G H g hv

theorem cellFormAssembly_closed : CellCalculus.CellFormAssemblyStatement :=
  CellCalculus.cellFormAssembly_of
    (CellCalculus.energyLeafBound_of_periodic
      (CellCalculus.harmonicEnergyFormValue_of_lift CellCalculus.harmonicLift_holds)
      (CellCalculus.labelResolvedEnergy_holds (CellCalculus.labelModeFacts_holds CellCalculus.harmonicLift_holds))
      CellCalculus.lowSlotFormValue_holds periodicSecondOrder_closed)

theorem creditPatchBound_closed : Bridge.CreditPatchBoundHolds :=
  Bridge.creditPatchBound
    (Bridge.patchCredit Coupling.inverseFormCredit
      (Bridge.patchTraceBound planeDataFlip_closed modeHeightDeriv_closed Bridge.traceMatch))
    Bridge.stripMomentTrace Bridge.traceHeight modeHeightDeriv_closed

theorem creditEvalMatches_closed : CreditEval.CreditEvalMatchesHolds :=
  CreditEval.creditEvalMatches periodicSecondOrder_closed
    (CellCalculus.harmonicSideData_holds CellCalculus.harmonicLift_holds) Bridge.traceHeight modeHeightDeriv_closed
    Bridge.stripMomentTrace

theorem exteriorConditionSound_closed : TailBand.ExteriorConditionSound :=
  TailBand.exteriorConditionSound_of_square
    (TailBand.modeSquareInverseSquare_of_smooth TailBand.squareExteriorSmoothStatement)

theorem exteriorNonneg_of_offModeSound (hS : TailBand.OffModeConditionSound) : Assembly.ExteriorNonnegHolds :=
  fun D X hFR htf hadm hmc hmesh hN hc hX hst =>
    Assembly.exteriorNonneg_of_sound_of_measurable exteriorConditionSound_closed hS TailBand.labelFlipEvenHolds D X
      (fun q hq v G H g hv ι => (htf.2.2.2.2 q hq v G H g hv).1 ι) hFR htf hadm hmc hmesh hN hc hX hst

theorem pressureRecovery_closed : Assembly.PressureRecoveryHolds :=
  Assembly.pressureRecoveryHolds_of_pressureParts Assembly.annihilatorGradient_holds
    Assembly.harmonicAnnihilator_holds Assembly.flipAverageRightSide_holds Assembly.remainderAnnihilates_holds
    Assembly.remainderRegular_holds

theorem cellLayerParts_of_cell (hInit : InitialStateHolds) (hPair : InstancePair.PairSharesFromSurrogateProfiles)
    (hCredit : CreditEval.CreditLeavesBoundHolds)
    (hSound : TailBand.OffModeConditionSound) (hOff : Assembly.OffModesVanishHolds) (hRes : CellResidualFromConditions)
    (hTree : Assembly.TreeStateHolds) (hRF : Assembly.RowsMatchFieldsHolds)
    (hRS : Assembly.RowsMatchStateOfFieldsHolds) (hSI : Assembly.CellStateInRowRangeHolds)
    (hFG : FieldGaugeParts) : CellLayerParts where
  initial_state := hInit
  cell_form := cellFormAssembly_closed
  pair_shares := hPair
  credit_leaves := hCredit
  scaled_jets := scaledJetParts_closed
  actuator_pairing := actuatorPairing_holds
  form_negative := formNegFinite
  state_certificate := stateEnclosureCertificateNonneg_holds
  support_radius := GivenShape.compactFieldSupportRadius_holds
  row_shares := rowSharesOfInstance
  instance_parts := instanceParts_holds
  true_field := Assembly.trueFieldRegularHolds
  off_modes := hOff
  exterior := exteriorNonneg_of_offModeSound hSound
  exterior_stretch := Assembly.exteriorStretchCharged
  exterior_values := Assembly.exteriorValuesChargeHolds
  pressure := pressureRecovery_closed
  residual := hRes
  tree_state := hTree
  rows_fields := hRF
  rows_state := hRS
  states_in := hSI
  field_gauge := hFG
  pressure_flip := fun D hPF => Assembly.chosenPressureFlip_holds D hPF
  relations := CellCalculus.harmonicRelations_holds CellCalculus.harmonicLift_holds

end CertCell

end Breakdown
