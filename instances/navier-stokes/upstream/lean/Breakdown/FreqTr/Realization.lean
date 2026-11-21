import Breakdown.FreqTr.Assembly
import Breakdown.FreqTr.FieldOp
import Breakdown.FreqTr.Heat
import Breakdown.FreqTr.Dilation
import Breakdown.FreqTr.DilationCont
import Breakdown.FreqTr.Rotation
import Breakdown.FreqTr.GradCompat
import Breakdown.FreqTr.FreqTrConjSym
import Breakdown.FreqTr.EmbedMem
import Breakdown.FreqTr.EmbedNorm
import Breakdown.FreqTr.EmbedNeZero
import Breakdown.FreqTr.EmbedRot
import Breakdown.FreqTr.EmbedDilate
import Breakdown.FreqTr.EmbedNegSsp
import Breakdown.FreqTr.GradSixDecay
import Breakdown.FreqTr.NiceDense
import Breakdown.FreqTr.NiceApprox
import Breakdown.FreqTr.TestDense
import Breakdown.FreqTr.TestSpan
import Breakdown.FreqTr.VelocityExists
import Breakdown.FreqTr.VelocityDecay
import Breakdown.FreqTr.PartialDecay
import Breakdown.FreqTr.VelocityInvert
import Breakdown.FreqTr.Trilinear
import Breakdown.FreqTr.Phi
import Breakdown.FreqTr.BilinExists
import Breakdown.FreqTr.BilinShift
import Breakdown.FreqTr.BilinCont
import Breakdown.FreqTr.VelocityRotate
import Breakdown.FreqTr.BilinDilate
import Breakdown.FreqTr.BilinRotate
import Breakdown.FreqTr.BilinTestFormula
import Breakdown.FreqTr.FreqTrL1
import Breakdown.FreqTr.BilinCompact
import Breakdown.FreqTr.PairingEmbed
import Breakdown.FreqTr.PairingByParts
import Breakdown.FreqTr.Advection
import Breakdown.FreqTr.WeakInX
import Breakdown.FreqTr.MildOfWeak
import Breakdown.FreqTr.VelocityInjective
import Breakdown.FreqTr.H1Consistency
import Breakdown.FreqTr.BilinH1

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Freq

theorem fieldOpRealized_holds : FieldOpRealized := fieldOpRealized

theorem heat_holds : HeatSemigroup := heatSemigroup fieldOpRealized

theorem dilation_holds : DilationAlgebra := dilationAlgebra fieldOpRealized heat_holds

theorem dilationCont_holds : DilationContinuous := dilationContinuous fieldOpRealized dilation_holds

theorem rotation_holds : RotationAlgebra := rotationAlgebra fieldOpRealized dilation_holds heat_holds

theorem embedMem_holds : EmbedMem :=
  embedMem fieldOpRealized gradCompatible (freqTrConjSym fieldOpRealized)

theorem embedNormLinear_holds : EmbedNorm ∧ EmbedLinear :=
  embedNormLinear fieldOpRealized gradCompatible embedMem_holds

theorem embedNegSsp_holds : EmbedNegSsp := embedNegSsp fieldOpRealized embedMem_holds

theorem testDense_holds : TestDenseGraph ∧ TestDense :=
  testDenseGraphDense fieldOpRealized (niceDense fieldOpRealized)
    (niceApprox fieldOpRealized embedMem_holds embedNormLinear_holds.1 embedNormLinear_holds.2
      embedNegSsp_holds)

theorem testSpan_holds : TestSpanSpec := testSpanSpec embedNormLinear_holds.2

theorem velocity_holds : VelocityExists :=
  velocityExists testDense_holds.2 testSpan_holds embedNormLinear_holds.2 embedNormLinear_holds.1
    gradSixDecay

theorem velocityDecay_holds : VelocityDecay :=
  velocityDecay velocity_holds testDense_holds.1 testDense_holds.2 testSpan_holds
    embedNormLinear_holds.2 embedNormLinear_holds.1 gradSixDecay embedMem_holds

theorem partial_holds : PartialDecay ∧ PartialNormLe :=
  partialDecayNorm fieldOpRealized gradCompatible embedMem_holds

theorem velocityInverts_holds : VelocityInvertsHalfSsp :=
  velocityInvertsHalfSsp velocity_holds testDense_holds.2 testSpan_holds embedMem_holds
    embedNormLinear_holds.2 fieldOpRealized gradCompatible

theorem trilinear_holds : TrilinearBound := trilinearBound partial_holds.2

theorem phi_holds : PhiBounds ∧ PhiVelocity :=
  phiBoundsVelocity fieldOpRealized heat_holds velocityInverts_holds

theorem bilin_holds : BilinExists ∧ BilinBound := bilinExistsBound trilinear_holds phi_holds.1

theorem bilinShift_holds : BilinShift := bilinShift bilin_holds.1 heat_holds fieldOpRealized

theorem bilinCont_holds : BilinContinuous :=
  bilinContinuous bilin_holds.1 bilin_holds.2 trilinear_holds phi_holds.1 phi_holds.2
    fieldOpRealized heat_holds

theorem velocityCov_holds : VelocityRotate ∧ VelocityDilate :=
  velocityRotateDilate velocity_holds testDense_holds.2 testSpan_holds
    (embedRot fieldOpRealized rotation_holds embedMem_holds gradCompatible)
    (embedDilate fieldOpRealized dilation_holds embedMem_holds) rotation_holds dilation_holds
    embedNormLinear_holds.2

theorem bilinDilate_holds : BilinDilate :=
  bilinDilate bilin_holds.1 dilation_holds fieldOpRealized velocityCov_holds.2 trilinear_holds
    heat_holds

theorem bilinRotate_holds : BilinRotate :=
  bilinRotate bilin_holds.1 rotation_holds fieldOpRealized velocityCov_holds.1 trilinear_holds

theorem bilinCompact_holds : BilinCompact :=
  bilinCompact (bilinTestFormula bilin_holds.1 velocity_holds fieldOpRealized trilinear_holds
    partial_holds.2) freqTrL1L2.1 testSpan_holds fieldOpRealized velocity_holds partial_holds.2
    embedNormLinear_holds.2

theorem weak_holds : WeakInX :=
  weakInX (pairingEmbed embedNormLinear_holds.1 embedNormLinear_holds.2) pairingByParts
    (advectionTrilinear velocityDecay_holds partial_holds.1) trilinear_holds embedNormLinear_holds.2

theorem mild_holds : MildOfWeak :=
  mildOfWeak weak_holds testDense_holds.1 testDense_holds.2 fieldOpRealized heat_holds
    bilin_holds.1 bilin_holds.2 bilinCont_holds bilinShift_holds phi_holds.2 phi_holds.1
    trilinear_holds velocityInverts_holds velocity_holds embedNegSsp_holds embedNormLinear_holds.2

def realization : Realization X :=
  realizationOf heat_holds dilation_holds dilationCont_holds bilin_holds.2 bilinCont_holds
    bilinShift_holds bilinDilate_holds testDense_holds.2 bilinCompact_holds rotation_holds
    bilinRotate_holds embedNormLinear_holds.2 embedNormLinear_holds.1
    (embedNeZero embedNormLinear_holds.1)
    (embedRot fieldOpRealized rotation_holds embedMem_holds gradCompatible)
    (embedDilate fieldOpRealized dilation_holds embedMem_holds) mild_holds testSpan_holds

theorem velocityInjective_holds : VelocityInjective :=
  velocityInjective velocity_holds testDense_holds.2 testSpan_holds embedMem_holds fieldOpRealized
    gradCompatible embedNormLinear_holds.2

theorem bilinTestFormula_holds : BilinTestFormula :=
  bilinTestFormula bilin_holds.1 velocity_holds fieldOpRealized trilinear_holds partial_holds.2

theorem h1Consistency_holds : H1Consistency :=
  h1Consistency fieldOpRealized (freqTrConjSym fieldOpRealized) velocityInverts_holds

theorem bilinH1Formula_holds : BilinH1Formula :=
  bilinH1Formula bilin_holds.1 h1Consistency_holds fieldOpRealized trilinear_holds

end Breakdown.Freq
