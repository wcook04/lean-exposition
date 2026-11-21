import Breakdown.Torus.Assembly
import Breakdown.Torus.Reduction
import Breakdown.Torus.BaseInverse
import Breakdown.Torus.ChainR3
import Breakdown.Torus.ChainTorus
import Breakdown.Torus.OpBounds
import Breakdown.Torus.TestLift
import Breakdown.Torus.ToVLinear
import Breakdown.Torus.Approximants
import Breakdown.Torus.ApproxLinks
import Breakdown.Torus.ApproxResidual
import Breakdown.Torus.ApproxSizes
import Breakdown.Torus.ApproxClose
import Breakdown.Torus.InverseAlgebra
import Breakdown.Torus.SeqPerturbation
import Breakdown.Torus.SeqOps
import Breakdown.Torus.Glue
import Breakdown.Torus.GlueUnbounded
import Breakdown.Torus.Transplant
import Breakdown.Torus.TorusSeriesSmooth
import Breakdown.Torus.HeatDivFreeCont
import Breakdown.Torus.SourceCont
import Breakdown.Torus.ShellTorus
import Breakdown.Torus.ShellR3
import Breakdown.Torus.HeatComparison
import Breakdown.Torus.Residual
import Breakdown.Torus.ApproxField
import Breakdown.Torus.SelfSimilar
import Breakdown.Torus.Cutoff
import Breakdown.Torus.CompareFinal
import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.FreqTrL1
import Breakdown.FreqTr.FreqTrConjSym
import Breakdown.FreqTr.GradSixDecay
import Breakdown.FreqTr.EmbedDilate
import Breakdown.FreqTr.EmbedRot
import Breakdown.Profile.Orbit
import Breakdown.Profile.SliceContinuity
import Breakdown.Transfer.Exports
import Breakdown.Spectral.RealDichotomy

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

theorem isFreqTrRealization : IsFreqTrRealization Freq.realization :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem approxFieldProperties_holds : ApproxFieldProperties :=
  approxFieldProperties selfSimilarSolves homotopyCurl (cutoffDivergenceFree homotopyCurl)

theorem approxLinks_holds : ApproxLinks :=
  approxLinks approxFieldProperties_holds transplantSmooth (freqTrSeriesSpec coefDeriv)

theorem r3LambdaBound_holds : R3LambdaBound :=
  r3LambdaBound Freq.fieldOpRealized_holds Freq.phi_holds.1 Freq.velocityDecay_holds Freq.partial_holds.1
    Freq.partial_holds.2

theorem torusLambdaBound_holds : TorusLambdaBound :=
  torusLambdaBound trigHs Freq.gradSixDecay Freq.embedNormLinear_holds.1

theorem operatorNormBounds_holds : OperatorNormBounds :=
  operatorNormBounds seqOpSpec pieceCompSpec pieceConvSpec r3LambdaBound_holds torusLambdaBound_holds
    (restrictR3Bound Freq.velocity_holds Freq.partial_holds.2) Freq.embedNormLinear_holds.2
    (heatDivFree_continuousOn Freq.fieldOpRealized_holds) sourceOp_continuousOn

theorem breakdownOnTorus_of_profile :
    PeriodicSimilarityProfileExists → BreakdownOnTorus := fun hP =>
  breakdownOnTorus_of_torusBlowup
    (torusBlowup_of_parts Freq.realization isFreqTrRealization embeddedProfileOrbit_holds
      orbitNorm orbitBound profilePiece Freq.testDense_holds.2 Freq.testSpan_holds
      (baseInverse (stepData dichotomyHolds) seqOpSpec)
      (r3ChainEq (r3Factor Freq.bilinTestFormula_holds Freq.velocityDecay_holds Freq.partial_holds.1)
        r3LambdaBound_holds seqOpSpec pieceCompSpec pieceConvSpec pieceOperator
        (heatDivFree_continuousOn Freq.fieldOpRealized_holds))
      (torusChainEq (torusFactor torusSeriesSmooth transplantSmooth (freqTrSeriesSpec coefDeriv))
        torusLambdaBound_holds seqOpSpec pieceCompSpec pieceConvSpec pieceOperator)
      (opDiffBounds seqOpSpec pieceOperator)
      operatorNormBounds_holds
      (testLiftExists Freq.testSpan_holds Freq.embedNormLinear_holds.2)
      (torusLiftExists toVAdd transplantSmooth)
      (comparisonSmall (heatDivFreeComparison Freq.fieldOpRealized_holds (Freq.freqTrL1L2).1
        (Freq.freqTrConjSym Freq.fieldOpRealized_holds) Freq.velocityInverts_holds (Freq.freqTrL1L2).2)
        (freeHeatComparison coefDeriv transplantSmooth Freq.fieldOpRealized_holds Freq.heat_holds
          Freq.velocityInverts_holds (Freq.freqTrL1L2).2 (Freq.freqTrL1L2).1
          (Freq.freqTrConjSym Freq.fieldOpRealized_holds))
        r3LambdaBound_holds torusLambdaBound_holds (restrictR3Bound Freq.velocity_holds Freq.partial_holds.2)
        (transplantNorm transplantSmooth) seqOpSpec pieceConvSpec pieceCompSpec operatorNormBounds_holds
        pieceOperator Freq.fieldOpRealized_holds Freq.heat_holds Freq.dilation_holds Freq.velocityCov_holds.2
        Freq.gradSixDecay Freq.embedNormLinear_holds.1
        (Freq.embedDilate Freq.fieldOpRealized_holds Freq.dilation_holds Freq.embedMem_holds))
      approxLinks_holds
      (approxResidualSmall approxFieldProperties_holds
        (approxResidualBound selfSimilarSolves homotopyCurl approxFieldProperties_holds)
        approxLinks_holds transplantSmooth)
      (approxClose (transplantNorm transplantSmooth) transplantSmooth approxFieldProperties_holds
        approxLinks_holds Freq.embedNormLinear_holds.1 Freq.embedNormLinear_holds.2
        (Freq.embedDilate Freq.fieldOpRealized_holds Freq.dilation_holds Freq.embedMem_holds)
        profilePiece Freq.dilation_holds Freq.dilationCont_holds sliceGradientContinuous_holds Freq.gradSixDecay)
      (approxSizes (transplantNorm transplantSmooth) approxFieldProperties_holds approxLinks_holds
        Freq.embedNormLinear_holds.1 Freq.embedNormLinear_holds.2)
      (datumClose (transplantNorm transplantSmooth) transplantSmooth approxFieldProperties_holds
        approxLinks_holds Freq.embedNormLinear_holds.1 Freq.embedNormLinear_holds.2 toVAdd)
      toVAdd
      (approximantExists Freq.testDense_holds.2 Freq.testSpan_holds
        (Freq.embedRot Freq.fieldOpRealized_holds Freq.rotation_holds Freq.embedMem_holds Freq.gradCompatible)
        Freq.embedNormLinear_holds.2 Freq.rotation_holds profilePiece)
      transplantSmooth (seqPerturbation pieceOperator varConstIntegral)
      (glueMild restrict concat shift varConstIntegral) glueUnbounded rightInversePerturb
      (shellInverseTransfer rightInversePerturb) seqOpSpec hP)

end Breakdown.Periodic
