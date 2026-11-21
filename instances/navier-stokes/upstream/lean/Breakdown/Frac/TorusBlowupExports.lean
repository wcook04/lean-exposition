import Breakdown.Frac.RExports
import Breakdown.Frac.RHeat
import Breakdown.Frac.RDilation
import Breakdown.Frac.RDecayEmbed
import Breakdown.Frac.RBilinTestCompact
import Breakdown.Frac.NNiceField
import Breakdown.Frac.POrbit
import Breakdown.Frac.PWeak
import Breakdown.Frac.PMomentum
import Breakdown.Frac.PTimeBound
import Breakdown.Frac.PSlice
import Breakdown.Frac.PFlow
import Breakdown.Frac.PAxial
import Breakdown.Frac.PUnitViscosity
import Breakdown.Frac.PProfileIff
import Breakdown.Frac.ScaledExports
import Breakdown.Frac.ScaledOrbitNorm
import Breakdown.Frac.OpExports
import Breakdown.Frac.OpCovariance
import Breakdown.Frac.OpRemainder
import Breakdown.Frac.OpNormalizer
import Breakdown.Frac.OpSymbolScalar
import Breakdown.Frac.TorusExports
import Breakdown.Frac.TorusHeat
import Breakdown.Frac.TorusKernel
import Breakdown.Frac.TorusKernelBound
import Breakdown.Frac.TorusForce
import Breakdown.Frac.TorusSource
import Breakdown.Frac.TorusCoef
import Breakdown.Frac.TorusPlaneWave
import Breakdown.Frac.TorusSymmetry
import Breakdown.Frac.TorusForceSmoothing
import Breakdown.Frac.TorusForced
import Breakdown.Frac.TorusSelfSimilar
import Breakdown.Frac.TorusSelfSimilarDecay
import Breakdown.Frac.TorusApproxField
import Breakdown.Frac.TorusApproxLinks
import Breakdown.Frac.TorusPointwiseBound
import Breakdown.Frac.TorusResidualCore
import Breakdown.Frac.TorusResidualShell
import Breakdown.Frac.TorusResidualOuter
import Breakdown.Frac.TorusResidualOuterBound
import Breakdown.Frac.TorusResidual
import Breakdown.Frac.TorusPeriodizationTail
import Breakdown.Frac.TorusApproxForced
import Breakdown.Frac.TorusApproxResidual
import Breakdown.Frac.TorusApproximants
import Breakdown.Frac.TorusShellR3
import Breakdown.Frac.TorusShellTorus
import Breakdown.Frac.TorusShellLambda
import Breakdown.Frac.TorusHeatSolenoidalCont
import Breakdown.Frac.TorusChainR3
import Breakdown.Frac.TorusChainTorus
import Breakdown.Frac.TorusOpNorm
import Breakdown.Frac.TorusBaseInverse
import Breakdown.Frac.TorusCompareChain
import Breakdown.Frac.TorusCompareLambda
import Breakdown.Frac.TorusCompareHeatSolenoidal
import Breakdown.Frac.TorusCompareEntryR3
import Breakdown.Frac.TorusCompareEntryTorus
import Breakdown.Frac.TorusCompareFrame
import Breakdown.Frac.TorusHeatCompareAssembly
import Breakdown.Frac.TorusHeatCompareTorus
import Breakdown.Frac.TorusHeatCompareInverse
import Breakdown.Frac.TorusHeatCompareProj
import Breakdown.Frac.TorusHeatCompareDensity
import Breakdown.Frac.TorusCompareSeedEntry
import Breakdown.Frac.TorusCompareTail
import Breakdown.Frac.TorusCompareLambdaAssembly
import Breakdown.Frac.TorusCompareFinal
import Breakdown.Frac.TorusGlue
import Breakdown.Frac.TorusGlueUnbounded
import Breakdown.Torus.SeqOps
import Breakdown.Torus.SeqPerturbation
import Breakdown.Torus.InverseAlgebra
import Breakdown.Torus.TestLift
import Breakdown.Torus.ToVLinear
import Breakdown.Torus.Transplant
import Breakdown.Torus.ShellR3
import Breakdown.Torus.CompareInvSeries
import Breakdown.Torus.CompareSplit
import Breakdown.Torus.CompareDilate
import Breakdown.Torus.Cutoff
import Breakdown.Torus.FreqTrSeries
import Breakdown.Torus.CoefCalculus
import Breakdown.Torus.HeatComparisonPartition
import Breakdown.Torus.HeatComparisonStep
import Breakdown.Torus.HeatComparisonSeries
import Breakdown.Torus.HeatComparisonCoef
import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.GradSixDecay
import Breakdown.Transfer.Exports
import Breakdown.Transfer.VarConstIntegral
import Breakdown.Transfer.Restrict
import Breakdown.Frac.RWeakInX
import Breakdown.Frac.NNiceDense
import Breakdown.Frac.NNiceEmbed
import Breakdown.Frac.NNicePairing
import Breakdown.Frac.RBilinShiftCont
import Breakdown.Frac.TorusCompareSeedAssembly
import Breakdown.Frac.TorusOpDiff
import Breakdown.Frac.TorusCompareWindow
import Breakdown.Frac.RMildOfWeak
import Breakdown.Frac.TorusApproxClose
import Breakdown.Frac.TorusCutoffGrad
import Breakdown.Frac.TorusCutoffMass
import Breakdown.Frac.TorusApproxSizes
import Breakdown.Frac.TorusApproxDatum
import Breakdown.Frac.TorusAssembly

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic.TorusBlowupAssembly.Internal

theorem fracSelfSimilarSolves_holds (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) :
    FracSelfSimilarSolves α :=
  fracSelfSimilarSolves_of α h1 h2 axialRotationSpec covariance

theorem fracSelfSimilarDecay_holds (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) :
    FracSelfSimilarDecay α :=
  fracSelfSimilarDecay_of α h1 h2 (fracSelfSimilarSolves_holds α h1 h2) axialRotationSpec covariance

theorem fracApproxFieldProperties_holds (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) :
    FracApproxFieldProperties α :=
  fracApproxFieldProperties_of α (fracSelfSimilarSolves_holds α h1 h2) homotopyCurl

theorem fracApproxLinks_holds (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) : FracApproxLinks α :=
  fracApproxLinks α h1 (fracApproxFieldProperties_holds α h1 h2) (freqTrSeriesSpec coefDeriv)

theorem fracPointwiseBound_holds (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) : FracPointwiseBound α :=
  fracPointwiseBound_of α h1 (by linarith) remainderBound normalizer

theorem fracApproxFieldThirdBound_holds (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) :
    FracApproxFieldThirdBound α := by
  intro a U P hU
  obtain ⟨C, -, hC⟩ := fracApproxField_bounds α h1 h2 (fracSelfSimilarDecay_holds α h1 h2)
    (fracApproxFieldProperties_holds α h1 h2) a U P hU
  exact ⟨C, fun T t hT hT1 ht htT x hx => (hC T t hT hT1 ht htT x).2 hx⟩

theorem fracSpaceResidualBound_holds (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) :
    FracSpaceResidualBound α :=
  fracSpaceResidualBound_of α
    (fracResidualCore_of α h1 h2 (fracSelfSimilarSolves_holds α h1 h2)
      (fracSelfSimilarDecay_holds α h1 h2) (fracApproxFieldProperties_holds α h1 h2)
      (fracPointwiseBound_holds α h1 h2) additivity remainderIntegrable covariance
      (fracApproxFieldThirdBound_holds α h1 h2))
    (fracResidualShell_of α h1 h2 (fracSelfSimilarSolves_holds α h1 h2)
      (fracSelfSimilarDecay_holds α h1 h2) (fracApproxFieldProperties_holds α h1 h2)
      (fracPointwiseBound_holds α h1 h2) remainderIntegrable homotopyCurl)
    (fracResidualOuter_of α h1 h2 (fracSelfSimilarDecay_holds α h1 h2)
      (fracApproxFieldProperties_holds α h1 h2) (fracPointwiseBound_holds α h1 h2) remainderIntegrable)

theorem fracApproxResidualBound_holds (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) :
    FracApproxResidualBound α :=
  fracApproxResidualBound_of α h1 h2 (fracSpaceResidualBound_holds α h1 h2)
    (fracPeriodizationTail_of α h1 (by linarith) additivity remainderIntegrable normalizer)
    (fracApproxFieldProperties_holds α h1 h2) (fracSelfSimilarDecay_holds α h1 h2) covariance

theorem fracTorusForceAlgebra_holds (α : ℝ) (h1 : 1 < α) : FracTorusForceAlgebra α :=
  fracTorusForceAlgebra α h1.le (fracTorusHeatAlgebra α)

theorem fracTorusKernelAlgebra_holds (α : ℝ) (h1 : 1 < α) : FracTorusKernelAlgebra α :=
  fracTorusKernelAlgebra α h1.le (fracTorusHeatAlgebra α)

theorem fracSourceOpExists_holds (α : ℝ) (h1 : 1 < α) : FracSourceOpExists α :=
  fracSourceOpExists α h1 (fracTorusForceAlgebra_holds α h1)

theorem fracSourceOpContinuous_holds (α : ℝ) (h1 : 1 < α) : FracSourceOpContinuous α :=
  fracSourceOpContinuous α h1 (fracSourceOpExists_holds α h1) (fracTorusForceAlgebra_holds α h1)

theorem fracTorusLambdaBound_holds (α : ℝ) (h1 : 1 < α) : FracTorusLambdaBound α :=
  fracTorusLambdaBound α h1 (fracTorusForceAlgebra_holds α h1) (fracSourceOpExists_holds α h1)

theorem fracR3LambdaBound_holds (α : ℝ) (h1 : 1 < α) : FracR3LambdaBound α :=
  fracR3LambdaBound α h1 (Freq.fracPhi_holds α h1).1

theorem fracForceSmoothing_holds (α : ℝ) (h1 : 1 < α) : FracForceSmoothing α :=
  fracForceSmoothing_of α h1 (fracTorusHeatAlgebra α) (fracTorusForceAlgebra_holds α h1)

theorem fracForcedPeriodicIsMild_holds (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) :
    FracForcedPeriodicIsMild α := by
  have h3 : α < 3 / 2 := by linarith
  exact fracForcedPeriodicIsMild_of α h1 h2 (fracTorusHeatAlgebra α) (fracTorusKernelAlgebra_holds α h1)
    (fracTorusKernelSharpBound_of α h1 (fracTorusKernelAlgebra_holds α h1))
    (coefFractional_of α (planeWaveEigen_of α h1 h3 (symbolScalar normalizer) normalizer)
      (periodicSymmetry_of α h1 h3 remainderBound))
    (fracTorusForceAlgebra_holds α h1) (fracForceSmoothing_holds α h1)

theorem fracApproxResidualSmall_holds (α : ℝ) (hα : 1 < α) (h2 : α < 5 / 4) :
    FracApproxResidualSmall α hα :=
  fracApproxResidualSmall α hα h2 (fracApproxFieldProperties_holds α hα h2)
    (fracApproxResidualBound_holds α hα h2) (fracApproxLinks_holds α hα h2)
    (fracApproxForcedSolution_of α hα h2 (fracApproxFieldProperties_holds α hα h2) covariance
      remainderIntegrable)
    (fracForcedPeriodicIsMild_holds α hα h2) (fracForceSmoothing_holds α hα)

theorem restrictR3Bound_holds : RestrictR3Bound :=
  restrictR3Bound Freq.velocity_holds Freq.partial_holds.2

theorem fracOperatorNormBounds_holds (α : ℝ) (hα : 1 < α) : FracOperatorNormBounds α hα :=
  fracOperatorNormBounds α hα seqOpSpec pieceCompSpec pieceConvSpec (fracR3LambdaBound_holds α hα)
    (fracTorusLambdaBound_holds α hα) restrictR3Bound_holds Freq.embedNormLinear_holds.2
    (fracHeatSolenoidalContinuous α hα) (fracSourceOpContinuous_holds α hα)

theorem fracR3ChainEq_holds (α : ℝ) (hα : 1 < α) : FracR3ChainEq α :=
  fracR3ChainEq α hα (fracR3Factor α hα (Freq.fracBilinTestFormula α hα (Freq.fracBilin_holds α hα).1))
    (fracR3LambdaBound_holds α hα) seqOpSpec pieceCompSpec pieceConvSpec pieceOperator
    (fracHeatSolenoidalContinuous α hα)

theorem fracTorusChainEq_holds (α : ℝ) (hα : 1 < α) : FracTorusChainEq α hα :=
  fracTorusChainEq α hα
    (fracTorusFactor α hα (fracTorusKernelAlgebra_holds α hα) (fracTorusForceAlgebra_holds α hα)
      (fracSourceOpExists_holds α hα))
    (fracTorusLambdaBound_holds α hα) seqOpSpec pieceCompSpec pieceConvSpec pieceOperator
    (fracSourceOpContinuous_holds α hα)

theorem fracBaseInverse_holds (α : ℝ) (hα : 1 < α) : FracBaseInverse α :=
  fracBaseInverse α hα scaledStepData seqOpSpec

theorem fracTailBound_holds (α : ℝ) (hα : 1 < α) : FracTailBound α hα :=
  fracTailBound α hα shiftChainNorm (fracOperatorNormBounds_holds α hα) restrictR3Bound_holds

theorem fracR3EntryFormula_holds (α : ℝ) (hα : 1 < α) : FracR3EntryFormula α :=
  fracR3EntryFormula α hα (fracR3ChainFormula α hα pieceOperator)
    (fracR3LambdaFormula α hα seqOpSpec pieceConvSpec (fracR3LambdaBound_holds α hα)
      (fracHeatSolenoidalContinuous α hα))
    (fracHeatSolenoidalShift α hα (Freq.fracHeatSemigroup α)) (fracHeatSolenoidalContinuous α hα)
    (fracR3LambdaBound_holds α hα)

theorem fracTorusEntryFormula_holds (α : ℝ) (hα : 1 < α) : FracTorusEntryFormula α hα :=
  fracTorusEntryFormula α hα (fracTorusChainFormula α hα pieceOperator)
    (fracTorusLambdaFormula α hα seqOpSpec pieceConvSpec (fracTorusLambdaBound_holds α hα)
      (fracSourceOpContinuous_holds α hα))
    (fracTorusLambdaBound_holds α hα) (fracTorusForceAlgebra_holds α hα) (fracSourceOpExists_holds α hα)

theorem fracFrameChange_holds (α : ℝ) (hα : 1 < α) : FracFrameChange α :=
  fracFrameChange α hα (Freq.fracVelocityDilate_holds α hα) (Freq.fracDilationAlgebra_holds α hα)

theorem fracProjectedHeatComparison_holds (α : ℝ) (hα : 1 < α) : FracHeatSolenoidalComparison α :=
  fracHeatSolenoidalComparison_of α hα (partitionSumBound_of_step stepIntegral)
    (fracTorusSourceSeries_of α hα torusSeriesPointwise sourceCoefFormula
      (fracTorusForceAlgebra_holds α hα) (fracSourceOpExists_holds α hα))
    (fracR3ValueFormula_of α hα (fracHeatSolenoidalFactor α hα)) (fracSourceDensityBounds α hα)
    (fracSourceDensityIncrement α hα)

theorem fracFreeHeatComparison_holds (α : ℝ) (hα : 1 < α) : FracFreeHeatComparison α :=
  fracFreeHeatComparison_of α hα (partitionSumBound_of_step stepIntegral)
    (fracTorusFreeSeries_of α hα torusSeriesPointwise transplantCoefFormula coefDeriv transplantSmooth
      stepIntegral (fracTorusHeatAlgebra α) (fracFreeDensityBounds α hα))
    (fracR3FreeFormula α hα (Freq.fracHeatSemigroup α)) (fracFreeDensityBounds α hα)
    (fracFreeDensityIncrement α hα)

theorem fracEmbedDilate_holds (α : ℝ) (hα : 1 < α) : Freq.FracEmbedDilate α :=
  Freq.fracEmbedDilate α (by linarith) (Freq.fracDilationAlgebra_holds α hα)
    (Freq.decayFieldScale α (by linarith))

theorem fracR3SeedEntry_holds (α : ℝ) (hα : 1 < α) : FracR3SeedEntry α :=
  fracR3SeedEntry α hα invSeriesEntry seqOpSpec (fracR3ChainFormula α hα pieceOperator)
    (fracOperatorNormBounds_holds α hα) pieceOperator

theorem fracTorusSeedEntry_holds (α : ℝ) (hα : 1 < α) : FracTorusSeedEntry α hα :=
  fracTorusSeedEntry α hα invSeriesEntry seqOpSpec (fracTorusChainFormula α hα pieceOperator)
    (fracOperatorNormBounds_holds α hα) pieceOperator

theorem selfSimilarWeak_holds : SelfSimilarWeak :=
  selfSimilarWeak_of (selfSimilarMomentum axialRotationSpec)
    (selfSimilarTimeBound axialRotationSpec (selfSimilarMomentum axialRotationSpec)) rotatingSliceDecay
    (fun α h1 h2 => Freq.niceFieldProps α h1 h2)

theorem fracWindowBound_holds (α : ℝ) (hα : 1 < α) : FracWindowBound α hα :=
  fracWindowBound α hα (fracR3EntryFormula_holds α hα) (fracTorusEntryFormula_holds α hα)
    (fracFrameChange_holds α hα) splitIntegralBound (fracProjectedHeatComparison_holds α hα)
    (fracR3LambdaBound_holds α hα) (fracTorusLambdaBound_holds α hα) restrictR3Bound_holds
    (advectShellBounds Freq.gradSixDecay Freq.embedNormLinear_holds.1) (Freq.fracDilationAlgebra_holds α hα)
    (fracHeatSolenoidalContinuous α hα)

theorem fracSeedComparison_holds (α : ℝ) (hα : 1 < α) : FracSeedComparison α hα :=
  fracSeedComparison α hα (fracR3SeedEntry_holds α hα) (fracTorusSeedEntry_holds α hα) transplantDilate
    dilateTest (fracFreeHeatComparison_holds α hα) (fracEmbedDilate_holds α hα)
    (transplantNorm transplantSmooth) restrictR3Bound_holds seqOpSpec pieceCompSpec
    (fracOperatorNormBounds_holds α hα) (Freq.fracHeatSemigroup α) (Freq.fracDilationAlgebra_holds α hα)

theorem fracOpDiffBounds_holds (α : ℝ) (hα : 1 < α) : FracOpDiffBounds α hα :=
  fracOpDiffBounds α hα seqOpSpec pieceOperator

theorem fracCutoffClose_holds (α : ℝ) (hα : 1 < α) (h2 : α < 5 / 4) : FracCutoffClose α :=
  fun a U P hU =>
    ⟨fracCutoffGrad α hα h2 (fracApproxFieldProperties_holds α hα h2) (fracSelfSimilarDecay_holds α hα h2)
      a U P hU,
    fracCutoffMass α hα h2 (fracApproxFieldProperties_holds α hα h2) (fracSelfSimilarDecay_holds α hα h2)
      a U P hU⟩

theorem fracApproxClose_holds (α : ℝ) (hα : 1 < α) (h2 : α < 5 / 4) : FracApproxClose α :=
  fracApproxClose α hα h2 (transplantNorm transplantSmooth) transplantSmooth
    (fracApproxFieldProperties_holds α hα h2) (fracApproxLinks_holds α hα h2) (fracEmbedDilate_holds α hα)
    (Freq.fracDilationAlgebra_holds α hα)
    (Freq.fracDilationContinuous α (by linarith) (Freq.fracDilationAlgebra_holds α hα))
    rotatingSliceContinuous_holds (fracSelfSimilarDecay_holds α hα h2) (fracCutoffClose_holds α hα h2)

theorem fracApproxSizes_holds (α : ℝ) (hα : 1 < α) (h2 : α < 5 / 4) : FracApproxSizes α :=
  fracApproxSizes α hα h2 (transplantNorm transplantSmooth) (fracApproxFieldProperties_holds α hα h2)
    (fracApproxLinks_holds α hα h2) (fracSelfSimilarDecay_holds α hα h2)

theorem fracDatumClose_holds (α : ℝ) (hα : 1 < α) (h2 : α < 5 / 4) : FracDatumClose α :=
  fracDatumClose α hα h2 (transplantNorm transplantSmooth) transplantSmooth
    (fracApproxFieldProperties_holds α hα h2) (fracApproxLinks_holds α hα h2) toVAdd
    (fracSelfSimilarDecay_holds α hα h2)

theorem fracMildOfWeak_holds (α : ℝ) (hα : 1 < α) (h2 : α < 5 / 4) : Freq.FracMildOfWeak α := by
  have h3 : α < 3 / 2 := by linarith
  have hH := Freq.fracHeatSemigroup α
  have hB := Freq.fracBilin_holds α hα
  have hP := Freq.fracPhi_holds α hα
  have hF := Freq.fracPower_niceField α hα h3
  exact Freq.fracMildOfWeak_of α hα h3
    (Freq.fracWeakInX_of α hα h3 (Freq.niceFieldProps α hα h3) Freq.nicePairingByParts
      Freq.niceAdvectionTrilinear)
    (Freq.fracNiceGraphDense α hα h3 Freq.niceEmbedSymbol hF)
    (Freq.fracNiceEmbedPower α hα h3 Freq.niceEmbedSymbol hF)
    hH hB.1 hB.2 (Freq.fracBilinContinuous α hα hB.1 hB.2 hP.1 hP.2 hH) (Freq.fracBilinShift α hB.1 hH)
    hP.2 hP.1 (Freq.niceFieldProps α hα h3)

theorem fracComparisonSmall_holds (α : ℝ) (hα : 1 < α) : FracComparisonSmall α hα :=
  fracComparisonSmall_of_parts α hα
    (fracLambdaComparison α hα invSeriesEntry seqOpSpec pieceCompSpec (fracOperatorNormBounds_holds α hα)
      (fracWindowBound_holds α hα) (fracTailBound_holds α hα))
    (fracSeedComparison_holds α hα)

theorem fracProfileOrbit_holds : FracProfileOrbit :=
  fracProfileOrbit_of_weak selfSimilarWeak_holds fracMildOfWeak_holds

theorem fracGlueMild_holds (α : ℝ) (hα : 1 < α) : FracGlueMild α hα :=
  fracGlueMild_of α hα restrict concat shift


end Breakdown.Periodic.TorusBlowupAssembly.Internal

namespace Breakdown.Periodic

open TorusBlowupAssembly.Internal

theorem fracTorusBlowup_holds (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (h : RotatingFractionalProfileExists α) : FracTorusBlowup α :=
  fracTorusBlowup_of_parts α hα₁ hα₂ (Freq.fracFramework_holds α hα₁) fracProfileOrbit_holds unitViscosity
    profileExistsIff scaledOrbitNorm scaledOrbitBound scaledProfilePiece Freq.testDense_holds.2
    Freq.testSpan_holds (fracBaseInverse_holds α hα₁) (fracR3ChainEq_holds α hα₁)
    (fracTorusChainEq_holds α hα₁) (fracOpDiffBounds_holds α hα₁) (fracOperatorNormBounds_holds α hα₁)
    (testLiftExists Freq.testSpan_holds Freq.embedNormLinear_holds.2) (torusLiftExists toVAdd transplantSmooth)
    (fracComparisonSmall_holds α hα₁) (fracApproxLinks_holds α hα₁ hα₂)
    (fracApproxResidualSmall_holds α hα₁ hα₂) (fracApproxClose_holds α hα₁ hα₂)
    (fracApproxSizes_holds α hα₁ hα₂) (fracDatumClose_holds α hα₁ hα₂) toVAdd
    (fracApproximantExists α hα₁ scaledProfilePiece) transplantSmooth
    (seqPerturbation pieceOperator varConstIntegral) (fracGlueMild_holds α hα₁) (fracGlueUnbounded α hα₁)
    rightInversePerturb (shellInverseTransfer rightInversePerturb) seqOpSpec h

end Breakdown.Periodic

namespace Breakdown

theorem fracBreakdownOnTorus (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (h : RotatingFractionalProfileExists α) : FractionalBreakdownOnTorus α :=
  Periodic.fractionalBreakdownOnTorus_of_torusBlowup α hα₁ hα₂ (Periodic.fracTorusBlowup_holds α hα₁ hα₂ h)

end Breakdown
