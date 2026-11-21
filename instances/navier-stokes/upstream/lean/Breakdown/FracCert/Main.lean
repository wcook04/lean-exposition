import Breakdown.FracCert.StHeld
import Breakdown.FracCert.StWeak
import Breakdown.FracCert.ActiveEnclosure
import Breakdown.FracCert.AprioriBound
import Breakdown.FracCert.BallShift
import Breakdown.FracCert.CertTestBox
import Breakdown.FracCert.CertificateWeakProfile
import Breakdown.FracCert.DecayBase
import Breakdown.FracCert.DecayFarField
import Breakdown.FracCert.DecayFixedPoint
import Breakdown.FracCert.DecayFixedPointGradient
import Breakdown.FracCert.DecayFixedPointWeight
import Breakdown.FracCert.DecayHeatDiv
import Breakdown.FracCert.DecayNonzero
import Breakdown.FracCert.DecayPower
import Breakdown.FracCert.DecayPressure
import Breakdown.FracCert.DecayPressureDiv
import Breakdown.FracCert.DecayPressureModel
import Breakdown.FracCert.DecayPressureRep
import Breakdown.FracCert.DecayPressureTrace
import Breakdown.FracCert.DecayPressureVanish
import Breakdown.FracCert.DecayStep
import Breakdown.FracCert.DefectRightSide
import Breakdown.FracCert.DriftEnergy
import Breakdown.FracCert.DriftPower
import Breakdown.FracCert.DriftPowerSolenoidal
import Breakdown.FracCert.DriftSymbolWeak
import Breakdown.FracCert.EmbedWeak
import Breakdown.FracCert.FarFieldGradientFree
import Breakdown.FracCert.FarFieldPairing
import Breakdown.FracCert.FarFieldWeighted
import Breakdown.FracCert.FlowDeriv
import Breakdown.FracCert.FlowPairing
import Breakdown.FracCert.FreeExists
import Breakdown.FracCert.FreeNice
import Breakdown.FracCert.FreeSymbolExists
import Breakdown.FracCert.FreeUnique
import Breakdown.FracCert.GradientAdd
import Breakdown.FracCert.GradientClosed
import Breakdown.FracCert.GradientOrthogonal
import Breakdown.FracCert.HeatDivRegular
import Breakdown.FracCert.HeldExists
import Breakdown.FracCert.HeldLimit
import Breakdown.FracCert.HeldMultiplierContinuous
import Breakdown.FracCert.HeldNonzero
import Breakdown.FracCert.HeldStateLimitBBound
import Breakdown.FracCert.HeldStateLimitBExports
import Breakdown.FracCert.HeldUnique
import Breakdown.FracCert.HeldWeakProfile
import Breakdown.FracCert.HeldWeakProfileParts
import Breakdown.FracCert.HeldZero
import Breakdown.FracCert.InverseSquare
import Breakdown.FracCert.KernelDyadicSplit
import Breakdown.FracCert.KernelDyadicSum
import Breakdown.FracCert.KernelExports
import Breakdown.FracCert.KernelMultiplier
import Breakdown.FracCert.KernelRingCutoff
import Breakdown.FracCert.LinearSolve
import Breakdown.FracCert.LinearSolveCore
import Breakdown.FracCert.LinearStateClosed
import Breakdown.FracCert.MildAnnihilator
import Breakdown.FracCert.MildBilinPairing
import Breakdown.FracCert.MildNiceHeat
import Breakdown.FracCert.MildPowerSim
import Breakdown.FracCert.MildProfileMoments
import Breakdown.FracCert.MildProfileOrbit
import Breakdown.FracCert.MildSimCompose
import Breakdown.FracCert.MildSimMoments
import Breakdown.FracCert.NiceClassDense
import Breakdown.FracCert.PowerSymbol
import Breakdown.FracCert.PowerSymbolRapid
import Breakdown.FracCert.PressureGradientSquare
import Breakdown.FracCert.ProductClass
import Breakdown.FracCert.ProductCompact
import Breakdown.FracCert.ProductSquare
import Breakdown.FracCert.ProfileMildForm
import Breakdown.FracCert.ProfileSymbolEquation
import Breakdown.FracCert.ProfileSymbolSix
import Breakdown.FracCert.QuadraticSquare
import Breakdown.FracCert.ResidualGradient
import Breakdown.FracCert.ResidualNice
import Breakdown.FracCert.SecondOrderComplete
import Breakdown.FracCert.SecondPairRapid
import Breakdown.FracCert.SecondSymbol
import Breakdown.FracCert.SecondTraceSolenoidal
import Breakdown.FracCert.SixthGradientBound
import Breakdown.FracCert.SmoothAssembly
import Breakdown.FracCert.SmoothFirstGain
import Breakdown.FracCert.SmoothMomentStep
import Breakdown.FracCert.SmoothSupGain
import Breakdown.FracCert.SolenoidalSplit
import Breakdown.FracCert.SplitFormBounds
import Breakdown.FracCert.StiffEnclosure
import Breakdown.FracCert.WeakFieldSmooth
import Breakdown.FracCert.WeakLowFrequency
import Breakdown.FracCert.WeakNiceDrift
import Breakdown.FracCert.WeakNiceSim
import Breakdown.FracCert.WeakPowerSub
import Breakdown.FracCert.WeakRegular
import Breakdown.FracCert.WeakSimDeriv
import Breakdown.FracCert.WeakSimPair
import Breakdown.FracCert.WeakToProfile
import Breakdown.FracCert.WeakSymbolL1

namespace Breakdown.SteadyCert

namespace ChainInternal

theorem freeSymbolExists_holds : Breakdown.SteadyCert.FreeSymbolExistsStatement :=
  Breakdown.SteadyCert.freeSymbolExists

theorem profileSymbolSix_holds : Breakdown.SteadyCert.ProfileSymbolSixStatement :=
  Breakdown.SteadyCert.profileSymbolSix

theorem profileSymbolEquation_holds : Breakdown.SteadyCert.ProfileSymbolEquationStatement :=
  Breakdown.SteadyCert.profileSymbolEquation

theorem freeExistsNice_holds : Breakdown.SteadyCert.FreeExistsNiceStatement :=
  Breakdown.SteadyCert.freeExistsNice_of ChainInternal.freeSymbolExists_holds ChainInternal.profileSymbolSix_holds ChainInternal.profileSymbolEquation_holds

theorem niceClassDense_holds : Breakdown.SteadyCert.NiceClassDenseStatement :=
  Breakdown.SteadyCert.niceClassDense

theorem freeBounds_holds : Breakdown.SteadyCert.FreeBoundsStatement :=
  Breakdown.SteadyCert.HeldBoundInternal.freeBoundsProved

theorem secondSymbolEnergy_holds : Breakdown.SteadyCert.SecondSymbolEnergyStatement :=
  Breakdown.SteadyCert.secondSymbolEnergy

theorem sixthGradientBound_holds : Breakdown.SteadyCert.SixthGradientBoundStatement :=
  Breakdown.SteadyCert.sixthGradientBound

theorem secondOrderComplete_holds : Breakdown.SteadyCert.SecondOrderCompleteStatement :=
  Breakdown.SteadyCert.secondOrderComplete_of ChainInternal.secondSymbolEnergy_holds ChainInternal.sixthGradientBound_holds

theorem secondOrderLinear_holds : Breakdown.SteadyCert.SecondOrderLinearStatement :=
  Breakdown.SteadyCert.secondOrderLinear

theorem freeExists_holds : Breakdown.SteadyCert.FreeExistsStatement :=
  Breakdown.SteadyCert.freeExists_of ChainInternal.freeExistsNice_holds ChainInternal.niceClassDense_holds ChainInternal.freeBounds_holds ChainInternal.secondOrderComplete_holds ChainInternal.secondOrderLinear_holds

theorem rapidWeakPower_holds : Breakdown.SteadyCert.RapidWeakPowerStatement :=
  Breakdown.SteadyCert.rapidWeakPower

theorem bandWeakPower_holds : Breakdown.SteadyCert.BandWeakPowerStatement :=
  Breakdown.SteadyCert.PowerSymbolInternal.bandWeakPower_of ChainInternal.rapidWeakPower_holds

theorem rapidSecondPair_holds : Breakdown.SteadyCert.RapidSecondPairStatement :=
  Breakdown.SteadyCert.rapidSecondPair

theorem bandSecondPair_holds : Breakdown.SteadyCert.BandSecondPairStatement :=
  Breakdown.SteadyCert.PowerSymbolInternal.bandSecondPair_of ChainInternal.rapidSecondPair_holds

theorem weakPowerSymbol_holds : Breakdown.SteadyCert.WeakPowerSymbolStatement :=
  Breakdown.SteadyCert.weakPowerSymbol_of_band ChainInternal.secondSymbolEnergy_holds ChainInternal.bandWeakPower_holds ChainInternal.bandSecondPair_holds

theorem driftSymbolWeak_holds : Breakdown.SteadyCert.DriftSymbolWeakStatement :=
  Breakdown.SteadyCert.driftSymbolWeak

theorem flowDeriv_holds : Breakdown.SteadyCert.FlowDerivStatement :=
  Breakdown.SteadyCert.flowDeriv

theorem flowTest_holds : Breakdown.SteadyCert.FlowTestStatement :=
  Breakdown.SteadyCert.flowTest_of_deriv ChainInternal.flowDeriv_holds

theorem flowIntegral_holds : Breakdown.SteadyCert.FlowIntegralStatement :=
  Breakdown.SteadyCert.flowIntegral_of_test ChainInternal.flowTest_holds

theorem flowPairing_holds : Breakdown.SteadyCert.FlowPairingStatement :=
  Breakdown.SteadyCert.flowPairing_of_integral ChainInternal.flowIntegral_holds

theorem driftPairSymbol_holds : Breakdown.SteadyCert.DriftPairSymbolStatement :=
  Breakdown.SteadyCert.driftPairSymbol_of ChainInternal.secondSymbolEnergy_holds ChainInternal.driftSymbolWeak_holds ChainInternal.flowPairing_holds

theorem driftPower_holds : Breakdown.SteadyCert.DriftPowerStatement :=
  Breakdown.SteadyCert.driftPower_of ChainInternal.secondSymbolEnergy_holds ChainInternal.weakPowerSymbol_holds ChainInternal.driftPairSymbol_holds

theorem freeUnique_holds : Breakdown.SteadyCert.FreeUniqueStatement :=
  Breakdown.SteadyCert.freeUnique_of ChainInternal.secondSymbolEnergy_holds ChainInternal.weakPowerSymbol_holds ChainInternal.driftPower_holds

theorem inverseSquareBound_holds : Breakdown.SteadyCert.InverseSquareBoundStatement :=
  Breakdown.SteadyCert.inverseSquareBound

theorem ballShift_holds : Breakdown.SteadyCert.BallShiftStatement :=
  Breakdown.SteadyCert.ballShift

theorem profileProductCompact_holds : Breakdown.SteadyCert.ProfileProductCompactStatement :=
  Breakdown.SteadyCert.profileProductCompact_of ChainInternal.inverseSquareBound_holds ChainInternal.secondSymbolEnergy_holds ChainInternal.ballShift_holds

theorem solenoidalSplit_holds : Breakdown.SteadyCert.SolenoidalSplitStatement :=
  Breakdown.SteadyCert.Internal.SolenoidalSplit.main

theorem gradientOrthogonal_holds : Breakdown.SteadyCert.GradientOrthogonalStatement :=
  Breakdown.SteadyCert.gradientOrthogonal

theorem productClass_holds : Breakdown.SteadyCert.ProductClassStatement :=
  Breakdown.SteadyCert.productClass

theorem weakPowerDifference_holds : Breakdown.SteadyCert.WeakPowerDifferenceStatement :=
  Breakdown.SteadyCert.weakPowerDifference

theorem driftEnergy_holds : Breakdown.SteadyCert.DriftEnergyStatement :=
  Breakdown.SteadyCert.driftEnergy

theorem splitFormBounds_holds : Breakdown.SteadyCert.SplitFormBoundsStatement :=
  Breakdown.SteadyCert.splitFormBounds ChainInternal.secondSymbolEnergy_holds ChainInternal.weakPowerSymbol_holds

theorem secondTraceSolenoidal_holds : Breakdown.SteadyCert.SecondTraceSolenoidalStatement :=
  Breakdown.SteadyCert.secondTraceSolenoidal

theorem gradientAdd_holds : Breakdown.SteadyCert.GradientAddStatement :=
  Breakdown.SteadyCert.gradientAdd

theorem aprioriBound_holds : Breakdown.SteadyCert.AprioriBoundStatement :=
  Breakdown.SteadyCert.aprioriBound ChainInternal.driftEnergy_holds ChainInternal.splitFormBounds_holds ChainInternal.gradientOrthogonal_holds ChainInternal.secondTraceSolenoidal_holds ChainInternal.gradientAdd_holds

theorem linearKernel_holds : Breakdown.SteadyCert.LinearKernelStatement :=
  Breakdown.SteadyCert.linearKernel ChainInternal.aprioriBound_holds ChainInternal.inverseSquareBound_holds

theorem linearSolve_holds : Breakdown.SteadyCert.LinearSolveStatement :=
  Breakdown.SteadyCert.LinearSolveCore.linearSolve_of_kernel' ChainInternal.freeExists_holds ChainInternal.freeUnique_holds ChainInternal.freeBounds_holds ChainInternal.profileProductCompact_holds ChainInternal.solenoidalSplit_holds ChainInternal.secondOrderLinear_holds ChainInternal.gradientOrthogonal_holds ChainInternal.productClass_holds ChainInternal.inverseSquareBound_holds ChainInternal.weakPowerDifference_holds ChainInternal.linearKernel_holds

theorem driftPowerSolenoidal_holds : Breakdown.SteadyCert.DriftPowerSolenoidalStatement :=
  Breakdown.SteadyCert.driftPowerSolenoidal

theorem gradientClosed_holds : Breakdown.SteadyCert.GradientClosedStatement :=
  Breakdown.SteadyCert.gradientClosed

theorem linearStateClosed_holds : Breakdown.SteadyCert.LinearStateClosedStatement :=
  Breakdown.SteadyCert.linearStateClosed ChainInternal.freeBounds_holds ChainInternal.secondOrderComplete_holds ChainInternal.secondOrderLinear_holds ChainInternal.solenoidalSplit_holds ChainInternal.gradientOrthogonal_holds ChainInternal.inverseSquareBound_holds ChainInternal.driftPowerSolenoidal_holds ChainInternal.gradientClosed_holds

theorem quadraticSquareIntegrable_holds : Breakdown.SteadyCert.QuadraticSquareIntegrableStatement :=
  Breakdown.SteadyCert.quadraticSquareIntegrable

theorem weakPowerSub_holds : Breakdown.SteadyCert.WeakPowerSubStatement :=
  Breakdown.SteadyCert.weakPowerSub

theorem defectRightSide_holds : Breakdown.SteadyCert.DefectRightSideStatement :=
  Breakdown.SteadyCert.defectRightSide

theorem heldExists_holds : Breakdown.SteadyCert.HeldExistsStatement :=
  Breakdown.SteadyCert.heldExists ChainInternal.linearSolve_holds ChainInternal.aprioriBound_holds ChainInternal.linearStateClosed_holds ChainInternal.secondOrderLinear_holds ChainInternal.quadraticSquareIntegrable_holds ChainInternal.gradientAdd_holds ChainInternal.weakPowerSub_holds ChainInternal.defectRightSide_holds

theorem productSquare_holds : Breakdown.SteadyCert.ProductSquareStatement :=
  Breakdown.SteadyCert.productSquare

theorem heldUnique_holds : Breakdown.SteadyCert.HeldUniqueStatement :=
  Breakdown.SteadyCert.heldUnique ChainInternal.aprioriBound_holds ChainInternal.secondOrderLinear_holds ChainInternal.productSquare_holds

theorem heldQuadraticL2_holds : Breakdown.SteadyCert.HeldQuadraticL2Statement :=
  Breakdown.SteadyCert.heldQuadraticL2_of ChainInternal.quadraticSquareIntegrable_holds

theorem profileEmbedData_holds : Breakdown.SteadyCert.ProfileEmbedDataStatement :=
  Breakdown.SteadyCert.profileEmbedData

theorem weakPowerClass_holds : Breakdown.SteadyCert.WeakPowerClassStatement :=
  Breakdown.SteadyCert.weakPowerClass_holds

theorem gradientClass_holds : Breakdown.SteadyCert.GradientClassStatement :=
  Breakdown.SteadyCert.gradientClass_holds

theorem heldResidualClass_holds : Breakdown.SteadyCert.HeldResidualClassStatement :=
  Breakdown.SteadyCert.heldResidualClass_of ChainInternal.profileEmbedData_holds ChainInternal.weakPowerClass_holds ChainInternal.gradientClass_holds

theorem heldResidualSquare_holds : Breakdown.SteadyCert.HeldResidualSquareStatement :=
  Breakdown.SteadyCert.heldResidualSquare_of ChainInternal.heldQuadraticL2_holds ChainInternal.heldResidualClass_holds

theorem heldStateLimit_holds : Breakdown.SteadyCert.HeldStateLimitStatement :=
  Breakdown.SteadyCert.heldStateLimitProved

theorem heldWeakLimit_holds : Breakdown.SteadyCert.HeldWeakLimitStatement :=
  Breakdown.SteadyCert.heldWeakLimit_of ChainInternal.heldResidualSquare_holds ChainInternal.heldStateLimit_holds

theorem heldLimit_holds : Breakdown.SteadyCert.HeldLimitStatement :=
  Breakdown.SteadyCert.heldLimit_of ChainInternal.solenoidalSplit_holds ChainInternal.gradientOrthogonal_holds ChainInternal.heldResidualSquare_holds ChainInternal.heldWeakLimit_holds

theorem heldMultiplierContinuous_holds : Breakdown.SteadyCert.HeldMultiplierContinuousStatement :=
  Breakdown.SteadyCert.heldMultiplierContinuous ChainInternal.heldExists_holds ChainInternal.heldUnique_holds ChainInternal.heldLimit_holds

theorem testBoxSubset_holds : Breakdown.SteadyCert.TestBoxSubsetStatement :=
  Breakdown.SteadyCert.testBoxSubset

theorem activeEnclosure_holds : Breakdown.SteadyCert.ActiveEnclosureStatement :=
  Breakdown.SteadyCert.activeEnclosure ChainInternal.gradientOrthogonal_holds ChainInternal.testBoxSubset_holds ChainInternal.quadraticSquareIntegrable_holds

theorem stiffEnclosure_holds : Breakdown.SteadyCert.StiffEnclosureStatement :=
  Breakdown.SteadyCert.stiffEnclosure

theorem heldZero_holds : Breakdown.SteadyCert.HeldZeroStatement :=
  Breakdown.SteadyCert.heldZero ChainInternal.heldMultiplierContinuous_holds ChainInternal.activeEnclosure_holds ChainInternal.stiffEnclosure_holds ChainInternal.testBoxSubset_holds

theorem embedWeak_holds : Breakdown.SteadyCert.EmbedWeakStatement :=
  Breakdown.SteadyCert.embedWeak

theorem heldNonzero_holds : Breakdown.SteadyCert.HeldNonzeroStatement :=
  Breakdown.SteadyCert.heldNonzero

theorem heldWeakProfile_holds : Breakdown.SteadyCert.HeldWeakProfileStatement :=
  Breakdown.SteadyCert.heldWeakProfile ChainInternal.embedWeak_holds ChainInternal.heldNonzero_holds ChainInternal.gradientOrthogonal_holds ChainInternal.quadraticSquareIntegrable_holds

theorem certificateWeakProfile_holds : Breakdown.SteadyCert.CertificateWeakProfileStatement :=
  Breakdown.SteadyCert.certificateWeakProfile ChainInternal.heldZero_holds ChainInternal.heldWeakProfile_holds

theorem niceHeat_holds : Breakdown.FracCert.NiceHeatStatement :=
  Breakdown.FracCert.niceHeat

theorem niceAnnihilator_holds : Breakdown.FracCert.NiceAnnihilatorStatement :=
  Breakdown.FracCert.niceAnnihilator

theorem bilinPairing_holds : Breakdown.FracCert.BilinPairingStatement :=
  Breakdown.FracCert.bilinPairing

theorem powerSimAdj_holds : Breakdown.FracCert.PowerSimAdjStatement :=
  Breakdown.FracCert.powerSimAdj

theorem simAdjPairing_holds : Breakdown.FracCert.SimAdjPairingStatement :=
  Breakdown.FracCert.simAdjPairing

theorem simAdjDeriv_holds : Breakdown.FracCert.SimAdjDerivStatement :=
  Breakdown.FracCert.simAdjDeriv

theorem niceSimAdjClosed_holds : Breakdown.FracCert.NiceSimAdjClosedStatement :=
  Breakdown.FracCert.niceSimAdjClosed

theorem niceDriftClosed_holds : Breakdown.FracCert.NiceDriftClosedStatement :=
  Breakdown.FracCert.niceDriftClosed

theorem simOpCompose_holds : Breakdown.FracCert.SimOpComposeStatement :=
  Breakdown.FracCert.simOpCompose

theorem mildOfWeakProfile_holds : Breakdown.FracCert.MildOfWeakProfileStatement :=
  Breakdown.FracCert.mildOfWeakProfile_of ChainInternal.niceHeat_holds ChainInternal.niceAnnihilator_holds ChainInternal.bilinPairing_holds ChainInternal.powerSimAdj_holds ChainInternal.simAdjPairing_holds ChainInternal.simAdjDeriv_holds ChainInternal.niceSimAdjClosed_holds ChainInternal.niceDriftClosed_holds ChainInternal.simOpCompose_holds

theorem mildFirstGain_holds : Breakdown.FracCert.MildFirstGainStatement :=
  Breakdown.FracCert.mildFirstGain

theorem supFromGain_holds : Breakdown.FracCert.SupFromGainStatement :=
  Breakdown.FracCert.supFromGain

theorem mildMomentStep_holds : Breakdown.FracCert.MildMomentStepStatement :=
  Breakdown.FracCert.mildMomentStep

theorem mildSmoothing_holds : Breakdown.FracCert.MildSmoothingStatement :=
  Breakdown.FracCert.mildSmoothing_of ChainInternal.mildFirstGain_holds ChainInternal.supFromGain_holds ChainInternal.mildMomentStep_holds

theorem simOpMoments_holds : Breakdown.FracCert.SimOpMomentsStatement :=
  Breakdown.FracCert.simOpMoments

theorem profileMoments_holds : Breakdown.FracCert.ProfileMomentsStatement :=
  Breakdown.FracCert.profileMoments_of ChainInternal.mildOfWeakProfile_holds ChainInternal.mildSmoothing_holds ChainInternal.simOpCompose_holds ChainInternal.simOpMoments_holds

theorem symbolL1OfMoments_holds : Breakdown.FracCert.SymbolL1OfMomentsStatement :=
  Breakdown.FracCert.symbolL1OfMoments

theorem fieldSmoothOfMoments_holds : Breakdown.FracCert.FieldSmoothOfMomentsStatement :=
  Breakdown.FracCert.fieldSmoothOfMoments

theorem lowFrequencyRemoval_holds : Breakdown.FracCert.LowFrequencyRemovalStatement :=
  Breakdown.FracCert.lowFrequencyRemoval

theorem pressureGradientSquare_holds : Breakdown.FracCert.PressureGradientSquareStatement :=
  Breakdown.FracCert.pressureGradientSquare ChainInternal.symbolL1OfMoments_holds

theorem residualNice_holds : Breakdown.FracCert.ResidualNiceStatement :=
  Breakdown.FracCert.residualNice_of ChainInternal.symbolL1OfMoments_holds ChainInternal.fieldSmoothOfMoments_holds ChainInternal.pressureGradientSquare_holds

theorem residualGradient_holds : Breakdown.FracCert.ResidualGradientStatement :=
  Breakdown.FracCert.residualGradient ChainInternal.symbolL1OfMoments_holds ChainInternal.fieldSmoothOfMoments_holds

theorem weakProfileRegular_holds : Breakdown.FracCert.WeakProfileRegularStatement :=
  Breakdown.FracCert.weakProfileRegular_of ChainInternal.symbolL1OfMoments_holds ChainInternal.fieldSmoothOfMoments_holds ChainInternal.lowFrequencyRemoval_holds ChainInternal.pressureGradientSquare_holds ChainInternal.residualNice_holds ChainInternal.residualGradient_holds

theorem kernelDecay_holds : Breakdown.FracCert.KernelDecayStatement :=
  Breakdown.FracCert.FarFieldWeightedInternal.kernelDecayHolds

theorem kernelScaling_holds : Breakdown.FracCert.KernelScalingStatement :=
  Breakdown.FracCert.FarFieldWeightedInternal.kernelScalingHolds

theorem heatDivBound_holds : Breakdown.FracCert.HeatDivBoundStatement :=
  Breakdown.FracCert.heatDivBound_of ChainInternal.kernelDecay_holds ChainInternal.kernelScaling_holds

theorem heatDivRegular_holds : Breakdown.FracCert.HeatDivRegularStatement :=
  Breakdown.FracCert.heatDivRegular

theorem farFieldBound_holds : Breakdown.FracCert.FarFieldBoundStatement :=
  Breakdown.FracCert.farFieldBound_of ChainInternal.heatDivBound_holds ChainInternal.heatDivRegular_holds

theorem velocityInverseWeight_holds : Breakdown.FracCert.VelocityInverseWeightStatement :=
  Breakdown.FracCert.profileInverseWeight

theorem farFieldWeighted_holds : Breakdown.FracCert.FarFieldWeightedStatement :=
  Breakdown.FracCert.farFieldWeighted

theorem profileMildForm_holds : Breakdown.FracCert.ProfileMildFormStatement :=
  Breakdown.FracCert.profileMildForm

theorem farFieldPairing_holds : Breakdown.FracCert.FarFieldPairingStatement :=
  Breakdown.FracCert.farFieldPairing_of_regular ChainInternal.heatDivRegular_holds

theorem profileGradientFree_holds : Breakdown.FracCert.ProfileGradientFreeStatement :=
  Breakdown.FracCert.profileGradientFree

theorem farFieldGradientFree_holds : Breakdown.FracCert.FarFieldGradientFreeStatement :=
  Breakdown.FracCert.farFieldGradientFree ChainInternal.kernelDecay_holds

theorem fixedPointAnnulus_holds : Breakdown.FracCert.FixedPointAnnulusStatement :=
  Breakdown.FracCert.fixedPointAnnulus_of ChainInternal.farFieldBound_holds ChainInternal.velocityInverseWeight_holds ChainInternal.farFieldWeighted_holds ChainInternal.profileMildForm_holds ChainInternal.farFieldPairing_holds ChainInternal.profileGradientFree_holds ChainInternal.farFieldGradientFree_holds

theorem profileFixedPoint_holds : Breakdown.FracCert.ProfileFixedPointStatement :=
  Breakdown.FracCert.profileFixedPoint_of_annulus ChainInternal.farFieldBound_holds ChainInternal.velocityInverseWeight_holds ChainInternal.farFieldWeighted_holds ChainInternal.fixedPointAnnulus_holds

theorem profileDecayBase_holds : Breakdown.FracCert.ProfileDecayBaseStatement :=
  Breakdown.FracCert.profileDecayBase_of ChainInternal.profileFixedPoint_holds ChainInternal.farFieldBound_holds ChainInternal.symbolL1OfMoments_holds ChainInternal.fieldSmoothOfMoments_holds ChainInternal.kernelDecay_holds

theorem profileDecayStep_holds : Breakdown.FracCert.ProfileDecayStepStatement :=
  Breakdown.FracCert.profileDecayStep_of ChainInternal.profileFixedPoint_holds ChainInternal.farFieldBound_holds ChainInternal.symbolL1OfMoments_holds ChainInternal.fieldSmoothOfMoments_holds ChainInternal.profileDecayBase_holds

theorem ringCutoff_holds : Breakdown.FracCert.RingCutoffStatement :=
  Breakdown.FracCert.ringCutoff

theorem dyadicSplit_holds : Breakdown.FracCert.DyadicSplitStatement :=
  Breakdown.FracCert.dyadicSplit

theorem dyadicPieceBound_holds : Breakdown.FracCert.DyadicPieceBoundStatement :=
  Breakdown.FracCert.dyadicPieceBound

theorem dyadicSum_holds : Breakdown.FracCert.DyadicSumStatement :=
  Breakdown.FracCert.dyadicSum

theorem homogeneousMultiplier_holds : Breakdown.FracCert.HomogeneousMultiplierStatement :=
  Breakdown.FracCert.homogeneousMultiplier_of ChainInternal.ringCutoff_holds ChainInternal.dyadicSplit_holds ChainInternal.dyadicPieceBound_holds ChainInternal.dyadicSum_holds

theorem powerDecay_holds : Breakdown.FracCert.PowerDecayStatement :=
  Breakdown.FracCert.powerDecay_of ChainInternal.homogeneousMultiplier_holds ChainInternal.symbolL1OfMoments_holds ChainInternal.fieldSmoothOfMoments_holds

theorem pressureTrace_holds : Breakdown.FracCert.PressureTraceStatement :=
  Breakdown.FracCert.DecayPressureTrace.pressureTrace_of ChainInternal.symbolL1OfMoments_holds ChainInternal.fieldSmoothOfMoments_holds

theorem productWeightedSmooth_holds : Breakdown.FracCert.ProductWeightedSmoothStatement :=
  Breakdown.FracCert.DecayPressureTrace.productWeightedSmooth_of ChainInternal.symbolL1OfMoments_holds ChainInternal.fieldSmoothOfMoments_holds

theorem pressureRepresentation_holds : Breakdown.FracCert.PressureRepresentationStatement :=
  Breakdown.FracCert.DecayPressureRep.pressureRepresentation_of ChainInternal.symbolL1OfMoments_holds

theorem modelPressureDecay_holds : Breakdown.FracCert.ModelPressureDecayStatement :=
  Breakdown.FracCert.DecayPressureModel.modelPressureDecay_of ChainInternal.homogeneousMultiplier_holds ChainInternal.productWeightedSmooth_holds ChainInternal.pressureRepresentation_holds

theorem pressureModel_holds : Breakdown.FracCert.PressureModelStatement :=
  Breakdown.FracCert.pressureModel_of ChainInternal.pressureTrace_holds ChainInternal.modelPressureDecay_holds ChainInternal.symbolL1OfMoments_holds

theorem powerDivergenceFree_holds : Breakdown.FracCert.PowerDivergenceFreeStatement :=
  Breakdown.FracCert.powerDivergenceFree_of ChainInternal.symbolL1OfMoments_holds

theorem residualDivergence_holds : Breakdown.FracCert.ResidualDivergenceStatement :=
  Breakdown.FracCert.residualDivergence_of ChainInternal.powerDivergenceFree_holds ChainInternal.powerDecay_holds ChainInternal.symbolL1OfMoments_holds ChainInternal.fieldSmoothOfMoments_holds

theorem decayingGradientVanishes_holds : Breakdown.FracCert.DecayingGradientVanishesStatement :=
  Breakdown.FracCert.DecayPressureVanish.decayingGradientVanishes

theorem pressureDecay_holds : Breakdown.FracCert.PressureDecayStatement :=
  Breakdown.FracCert.pressureDecay_of_parts ChainInternal.pressureModel_holds ChainInternal.residualDivergence_holds ChainInternal.decayingGradientVanishes_holds ChainInternal.powerDecay_holds

theorem profileNonzero_holds : Breakdown.FracCert.ProfileNonzeroStatement :=
  Breakdown.FracCert.profileNonzero_of ChainInternal.symbolL1OfMoments_holds ChainInternal.fieldSmoothOfMoments_holds

theorem weakToProfile_holds : Breakdown.FracCert.WeakToProfileStatement :=
  Breakdown.FracCert.weakToProfile_of ChainInternal.profileMoments_holds ChainInternal.weakProfileRegular_holds ChainInternal.profileDecayBase_holds ChainInternal.profileDecayStep_holds ChainInternal.powerDecay_holds ChainInternal.pressureDecay_holds ChainInternal.profileNonzero_holds

end ChainInternal

theorem fracCertificate_profile_chain (hC : CertificateWeakProfileStatement)
    (hW : FracCert.WeakToProfileStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) (h : FracCertificateHypothesis α) :
    RotatingFractionalProfileExists α :=
  hW α hα₁ hα₂ (hC α hα₁ hα₂ h)

theorem fracCertificate_profile_proved (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) (h : FracCertificateHypothesis α) :
    RotatingFractionalProfileExists α :=
  fracCertificate_profile_chain ChainInternal.certificateWeakProfile_holds ChainInternal.weakToProfile_holds α hα₁ hα₂ h

end Breakdown.SteadyCert
