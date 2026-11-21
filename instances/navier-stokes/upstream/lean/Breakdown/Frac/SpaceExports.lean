import Breakdown.Frac.SpaceScaling
import Breakdown.Frac.SpaceUnitBreakdown
import Breakdown.Frac.PBlowup
import Breakdown.Frac.POrbit
import Breakdown.Frac.PWeak
import Breakdown.Frac.PMomentum
import Breakdown.Frac.PTimeBound
import Breakdown.Frac.PSlice
import Breakdown.Frac.PAxial
import Breakdown.Frac.PUnitViscosity
import Breakdown.Frac.PProfileIff
import Breakdown.Frac.NNiceField
import Breakdown.Frac.RegPowerGlue
import Breakdown.Frac.RegPowerFlow
import Breakdown.Frac.RegPowerLocal
import Breakdown.Frac.RegPowerConcat
import Breakdown.Frac.RegPowerPersist
import Breakdown.Frac.RegPowerApriori
import Breakdown.Frac.RegPowerIdentify
import Breakdown.Frac.RegPowerSolution
import Breakdown.Frac.RegPowerMildMapBasic
import Breakdown.Frac.RegPowerMildMapEst
import Breakdown.Frac.RegPowerMildMapCurve
import Breakdown.Frac.RegPowerMildIntegralCurve
import Breakdown.Frac.RegPowerMildGain
import Breakdown.Frac.RegPowerHeatPart
import Breakdown.Frac.RegPowerHeatGain
import Breakdown.Frac.RegPowerHeatWeight
import Breakdown.Frac.RegPowerHeatBasic
import Breakdown.Frac.RegPowerDissipation
import Breakdown.Frac.RegPowerEnergy
import Breakdown.Frac.RegPowerPointwise
import Breakdown.Frac.RegPowerMild
import Breakdown.Frac.RegPowerBilinIntegral
import Breakdown.Frac.RegPowerBilinPhys
import Breakdown.Frac.RegPowerHeatSolenoidal
import Breakdown.Frac.RegPowerPhysCurve
import Breakdown.Frac.RegPowerWeightCurve
import Breakdown.Frac.RegPowerPressure
import Breakdown.Frac.RegPowerPhysPower
import Breakdown.Frac.TorusPlaneWave
import Breakdown.Frac.OpSymbolScalar
import Breakdown.Frac.OpNormalizer
import Breakdown.Frac.SpaceRestrict
import Breakdown.Frac.SpaceUniqueness
import Breakdown.Frac.SpaceEnergy
import Breakdown.Frac.SpacePressureDiff
import Breakdown.Frac.SpacePressureIdentity
import Breakdown.Frac.SpacePressureCont
import Breakdown.Frac.SpacePressureMollify
import Breakdown.Frac.SpacePressureTraceSecondDeriv
import Breakdown.Frac.SpacePressureAverage
import Breakdown.Frac.SpacePressureTime
import Breakdown.Frac.SpaceForced
import Breakdown.Frac.SpaceSolenoidal
import Breakdown.Frac.SpaceWeakCont
import Breakdown.Frac.SpaceMollify
import Breakdown.Frac.SpaceDecay
import Breakdown.Frac.SpaceDifference
import Breakdown.Frac.SpaceLowerBound
import Breakdown.Frac.SpaceLocalization
import Breakdown.Frac.SpaceSixth
import Breakdown.Frac.SpaceGradient
import Breakdown.Frac.OpExports
import Breakdown.Frac.OpCovariance
import Breakdown.Frac.RExports
import Breakdown.Frac.ScaledExports
import Breakdown.Frac.SpaceOrbitRate
import Breakdown.Frac.RMildOfWeak
import Breakdown.Frac.RWeakInX
import Breakdown.Frac.NNiceDense
import Breakdown.Frac.NNiceEmbed
import Breakdown.Frac.NNicePairing
import Breakdown.Frac.RHeat
import Breakdown.Frac.RBilinShiftCont

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

namespace FracInternal.SpaceAssembly

theorem pressureDifference : ForcedPressureDifferenceStatement :=
  forcedPressureDifference_of
    (forcedPressureIdentity_of forcedPressureContinuity
      (forcedPressureMollify_of forcedScalarTraceSecondDeriv)
      (forcedPressureAverage_of forcedTimeIdentity forcedPressureContinuity))

theorem forced : FracForcedStatement :=
  fracForced_of symmetryCompact
    (fracWeakSolenoidal_of symmetryCompact fracCompactDecay covariance)
    (fracWeakContinuity_of fracCompactDecay) fracMollifyPairing remainderIntegrable

theorem gradientBound : FracGradientBoundStatement :=
  fracGradientBound_of symbol

theorem difference : FracDifferenceStatement :=
  fracDifference_of
    (fracCutoffLowerBound_of fracLocalization gradientBound fracCompactDecay covariance)
    (fracSixthNorm_of gradientBound) gradientBound

theorem uniqueness : FracUniquenessStatement :=
  fracUniqueness_of forcedLocalEnergy pressureDifference forced difference symmetryCompact
    additivity remainderIntegrable

theorem heatIntegral (α : ℝ) (hα : 1 < α) : SmoothFlow.PowerHeatIntegralStatement α :=
  SmoothFlow.powerHeatIntegral_of α hα (SmoothFlow.powerHeatWeight α hα)

theorem fixedPoint (α : ℝ) (hα : 1 < α) : SmoothFlow.PowerFixedPointStatement α :=
  SmoothFlow.powerFixedPoint_of α hα (SmoothFlow.powerMildMapBasic α)
    (SmoothFlow.powerMildMapEst_of α hα (heatIntegral α hα) (SmoothFlow.powerHeatBasic α hα))
    (SmoothFlow.powerMildMapCurve_of α hα
      (SmoothFlow.powerMildIntegralCurve α hα (SmoothFlow.powerHeatBasic α hα)
        (SmoothFlow.powerHeatWeight α hα))
      (SmoothFlow.powerHeatPart_holds α hα))

theorem localExistence (α : ℝ) (hα : 1 < α) : SmoothFlow.PowerLocalStatement α :=
  SmoothFlow.powerLocal_of α hα (fixedPoint α hα) (SmoothFlow.powerMildMapBasic α)

theorem persist (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) : SmoothFlow.PowerPersistStatement α :=
  SmoothFlow.powerPersist_of α hα
    (SmoothFlow.powerMildGain_of α hα hα2 (SmoothFlow.powerHeatGain α hα)
      (SmoothFlow.powerHeatPart_holds α hα))
    (SmoothFlow.powerHeatPart_holds α hα)

theorem apriori (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) : SmoothFlow.PowerAprioriStatement α :=
  SmoothFlow.powerApriori_of α hα
    (SmoothFlow.powerDissipation_of α hα hα2
      (SmoothFlow.powerEnergyInequality_of α hα (SmoothFlow.powerPointwiseDeriv α hα))
      (SmoothFlow.powerAEMeas_of α hα (SmoothFlow.powerPointwiseDeriv α hα)))
    (SmoothFlow.powerHsMild_of α hα (SmoothFlow.powerEnormMild α hα))

theorem flow (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) : SmoothFlow.PowerFlowStatement α :=
  SmoothFlow.powerFlow_of α hα (localExistence α hα) (SmoothFlow.powerConcat α hα) (persist α hα hα2)
    (apriori α hα hα2)

theorem bilinPhys (α : ℝ) (hα : 1 < α) : SmoothFlow.PowerBilinPhysStatement α :=
  SmoothFlow.powerBilinPhys_of α hα (Freq.fracBilinH1_holds α hα) (SmoothFlow.powerSolenoidal α hα)

theorem identify (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) : SmoothFlow.PowerIdentifyStatement α :=
  SmoothFlow.powerIdentify_of α hα hα2
    (SmoothFlow.powerBilinIntegral_of α hα (bilinPhys α hα)
      (SmoothFlow.powerBilinContinuous_of α hα (bilinPhys α hα) (SmoothFlow.powerSolenoidal α hα))
      (SmoothFlow.powerHeatX α))
    (SmoothFlow.powerHeatX α)

theorem weightCurve (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) :
    SmoothFlow.PowerWeightCurveStatement α :=
  SmoothFlow.powerWeightCurve_of α hα hα2 (SmoothFlow.powerPointwiseDeriv α hα)

theorem solutionOn (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) :
    SmoothFlow.PowerSolutionOnStatement α :=
  SmoothFlow.powerSolutionOn_of α hα
    (SmoothFlow.powerPhysCurve_of α hα hα2 (weightCurve α hα hα2)
      (SmoothFlow.powerPressureCurve_of α hα (weightCurve α hα hα2))
      (SmoothFlow.powerPhysPower_of α hα hα2
        (Periodic.planeWaveEigen_of α hα hα2 (symbolScalar normalizer) normalizer)))

theorem mildRegular (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) : FracMildRegularStatement α :=
  fracMildRegular_of α hα hα2 (flow α hα hα2) (identify α hα hα2) (solutionOn α hα hα2)
    (Freq.fracBilin_holds α hα).2

theorem selfSimilarWeak : SelfSimilarWeak :=
  selfSimilarWeak_of (selfSimilarMomentum axialRotationSpec)
    (selfSimilarTimeBound axialRotationSpec (selfSimilarMomentum axialRotationSpec))
    rotatingSliceDecay Freq.niceFieldProps

theorem profileOrbit_of_mild (hM : ∀ α : ℝ, 1 < α → α < 5 / 4 → Freq.FracMildOfWeak α) :
    FracProfileOrbit :=
  fracProfileOrbit_of_weak selfSimilarWeak hM

theorem mildBlowup_of_mild (hM : ∀ α : ℝ, 1 < α → α < 5 / 4 → Freq.FracMildOfWeak α) :
    FracMildBlowup :=
  fracMildBlowup_of scaledTransferHolds (profileOrbit_of_mild hM) unitViscosity profileExistsIff
    rotatingSliceDecay

theorem unitBreakdown_of_mild (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (hM : ∀ α : ℝ, 1 < α → α < 5 / 4 → Freq.FracMildOfWeak α) :
    FracSpaceUnitBreakdownStatement α :=
  fracSpaceUnitBreakdown_of α hα₁ hα₂ (mildBlowup_of_mild hM) (profileOrbit_of_mild hM)
    (mildRegular α hα₁ (by linarith)) fracRestrict uniqueness
    (fracOrbitRateFalse α hα₁ hα₂ (Freq.fracVelocityDilate_holds α hα₁))

theorem breakdownOnSpace_of_mild (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (hM : ∀ α : ℝ, 1 < α → α < 5 / 4 → Freq.FracMildOfWeak α)
    (h : RotatingFractionalProfileExists α) : FractionalBreakdownOnSpace α :=
  fracScaling α (unitBreakdown_of_mild α hα₁ hα₂ hM h)

theorem mildOfWeak (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) : Freq.FracMildOfWeak α :=
  have hH := Freq.fracHeatSemigroup α
  have hB := Freq.fracBilin_holds α hα
  have hP := Freq.fracPhi_holds α hα
  have hF := Freq.fracPower_niceField α hα hα2
  Freq.fracMildOfWeak_of α hα hα2
    (Freq.fracWeakInX_of α hα hα2 (Freq.niceFieldProps α hα hα2) Freq.nicePairingByParts
      Freq.niceAdvectionTrilinear)
    (Freq.fracNiceGraphDense α hα hα2 Freq.niceEmbedSymbol hF)
    (Freq.fracNiceEmbedPower α hα hα2 Freq.niceEmbedSymbol hF)
    hH hB.1 hB.2
    (Freq.fracBilinContinuous α hα hB.1 hB.2 hP.1 hP.2 hH)
    (Freq.fracBilinShift α hB.1 hH) hP.2 hP.1 (Freq.niceFieldProps α hα hα2)

end FracInternal.SpaceAssembly

open FracInternal.SpaceAssembly in
theorem fracBreakdownOnSpace (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (h : RotatingFractionalProfileExists α) : FractionalBreakdownOnSpace α :=
  breakdownOnSpace_of_mild α hα₁ hα₂ (fun β hβ₁ hβ₂ => mildOfWeak β hβ₁ (by linarith)) h

end Breakdown
