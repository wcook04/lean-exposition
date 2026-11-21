import Breakdown.Weak.OrbitBreakdown
import Breakdown.Weak.OrbitOfParts
import Breakdown.Weak.GradientFreqTr
import Breakdown.Weak.ZeroGradient
import Breakdown.Weak.PairingVelocity
import Breakdown.Weak.VelocityWeakGradient
import Breakdown.Weak.AdvectionByParts
import Breakdown.Weak.PairingDilate
import Breakdown.Weak.TrilinearDilate
import Breakdown.Weak.SliceMeasurable
import Breakdown.Weak.ScaledTestField
import Breakdown.Weak.SliceIntegrand
import Breakdown.Weak.SimilarityIdentity
import Breakdown.Weak.PhysicalIdentity
import Breakdown.Weak.ConstOfWeakDeriv
import Breakdown.Weak.GoodTimes
import Breakdown.Weak.BilinIntegrable
import Breakdown.Weak.VarConstInner
import Breakdown.Weak.VarConstGood
import Breakdown.Weak.MildFromGood
import Breakdown.Weak.ContinuousVarConst
import Breakdown.Weak.Representative
import Breakdown.Weak.SliceEmbedding

noncomputable section

namespace Breakdown

open WeakProfile

theorem breakdownOnSpace_of_weak : WeakPeriodicSimilarityProfileExists → BreakdownOnSpace := fun h =>
  breakdownOnSpace_of_orbit
    (weakOrbitOfParts_holds pairingVelocity_holds velocityWeakGradient_holds zeroGradientSix_holds
      gradientFreqTr_holds sliceEmbedding_holds advectionByParts_holds pairingDilate_holds
      trilinearDilate_holds sliceMeasurable_holds scaledTestField_holds sliceIntegrand_holds
      similarityIdentity_holds
      (physicalIdentity_of_parts pairingVelocity_holds velocityWeakGradient_holds) constOfWeakDeriv_holds goodTimes_holds
      bilinIntegrable_holds varConstInner_holds varConstGood_holds continuousVarConst_holds
      mildFromGood_holds globalRepresentative_holds timeChangeNull_holds
      physicalCurveMeasurable_holds h)

end Breakdown
