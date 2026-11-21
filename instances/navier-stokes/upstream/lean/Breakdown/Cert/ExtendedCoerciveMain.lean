import Breakdown.Cert.ExtendedCoerciveAssembly
import Breakdown.Cert.ExtendedCoerciveZeroFlow
import Breakdown.Cert.ExtendedCoerciveSecondDerivSymm
import Breakdown.Cert.ExtendedCoerciveEnergyIdentity
import Breakdown.Cert.ExtendedCoercivePairingSplit
import Breakdown.Cert.ExtendedCoercivePieceDensity
import Breakdown.Cert.ExtendedCoerciveAbsorbStep
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveTorus
import Breakdown.Cert.CoerciveSquareSum
import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveSolenoidal
import Breakdown.Cert.CoerciveTestDensityProof
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveSmoothIsPerturbation
import Breakdown.Cert.CoerciveSmoothCurlWeight
import Breakdown.Cert.CoerciveSmoothBase
import Breakdown.Cert.CoercivePieceField
import Breakdown.Cert.CoerciveSmoothApprox
import Breakdown.Cert.ExtendedCoercivePieceEps
import Breakdown.Cert.ExtendedCoercivePieceMu
import Breakdown.Cert.ExtendedCoercivePieceDensityPassage
import Breakdown.Cert.CoerciveSmoothSumSecondPartialsPairing

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

open PieceWeights

theorem modeSquareSumHolds_closed : Coercive.ModeSquareSumHolds :=
  Coercive.modeSquareSumHolds_of Coercive.torusSquareSumHolds_proof Coercive.axialRotationHolds_proof

theorem modeDerivativeHolds_closed : Coercive.ModeDerivativeHolds :=
  Coercive.modeDerivativeHolds_of Coercive.axialRotationHolds_proof
    Coercive.perturbationLocalIntegrabilityHolds_proof

theorem modeRotationHolds_closed : Coercive.ModeRotationHolds :=
  Coercive.modeRotationHolds_of Coercive.axialRotationHolds_proof
    Coercive.perturbationLocalIntegrabilityHolds_proof

theorem solenoidalModeHolds_closed : Coercive.SolenoidalModeHolds :=
  Coercive.solenoidalModeHolds_of Coercive.axialRotationHolds_proof Coercive.gradSolenoidalDensityHolds_proof

theorem pieceMultiplierDensityWeakHolds_proof : PieceMultiplierDensityWeakHolds :=
  pieceMultiplierDensityWeakHolds_of_nodes modeSquareSumHolds_closed modeDerivativeHolds_closed
    modeRotationHolds_closed solenoidalModeHolds_closed
    Coercive.smoothPerturbationIsPerturbationHolds_proof
    (energyIdentitySmoothWeak_of_symmetric weakSecondDerivSymmetricHolds_proof)
    (Coercive.baseDensitySmoothHolds_of modeSquareSumHolds_closed Coercive.curlWeightIdentityDecayHolds_proof)
    (piecePairingSplitSmoothWeakHolds_of modeSquareSumHolds_closed solenoidalModeHolds_closed)
    (pieceEpsEstimateSmoothWeakHolds_of modeSquareSumHolds_closed modeDerivativeHolds_closed modeRotationHolds_closed
      Coercive.smoothPerturbationIsPerturbationHolds_proof Coercive.weightedSumSecondPartialsPairingHolds_proof)
    (pieceMuEstimateSmoothWeakHolds_of modeSquareSumHolds_closed modeDerivativeHolds_closed modeRotationHolds_closed
      solenoidalModeHolds_closed Coercive.smoothPerturbationIsPerturbationHolds_proof
      Coercive.weightedSumSecondPartialsPairingHolds_proof)
    (pieceDensitySmoothWeakHolds_of modeSquareSumHolds_closed)
    (Coercive.pieceFieldExistsHolds_of modeSquareSumHolds_closed modeDerivativeHolds_closed
      modeRotationHolds_closed)
    zeroFlowAdmissibleHolds_proof
    Coercive.smoothApproximationHolds_proof
    pieceDensityPassageWeakHolds_of
    (pieceAbsorbStepWeakHolds_of modeSquareSumHolds_closed Coercive.perturbationSecondDerivBoundHolds_proof
      Coercive.perturbationLocalSquareIntegrabilityHolds_proof)

section Extended

variable {k : ℕ}

theorem extendedCoerciveClause_of_pieceData_proved {d : ExtendedCertificateData k}
    (hrad : ∀ j ∈ d.adjointSet, 0 ≤ d.radius j)
    (hwup : ∀ y, d.weightFn y ≤ d.weightMax)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.actuator i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (d.actuator i))
    (hnorm : ∑ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
      ENNReal.ofReal (d.actuatorBound ^ 2))
    (HW : (Fin k → ℝ) → ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : (Fin k → ℝ) → ℝ)
    (hmodel : ∀ q ∈ d.params, IsWeakSecondDerivState (d.model q) (HW q) (D q))
    {C : Type} {nE nM : ℕ} (m : (Fin k → ℝ) → PieceWeights C nE nM)
    (hs : (Fin k → ℝ) → HarmonicBounds)
    {c cμ t epsSup epsGradSup ratio : ℝ}
    (hc : ∀ q ∈ d.params, (m q).c = c) (hcμ : ∀ q ∈ d.params, (m q).cμ = cμ) (ht : 0 ≤ t)
    (hm : ∀ q ∈ d.params, IsAdmissibleWeak (m q) (d.period q) (hs q) d.weightFn (d.model q) (HW q)
      d.weight epsSup epsGradSup ratio)
    (hrest : RowRestClause d m hs HW c t)
    (hL2 : Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt d.weight) ^ 2 / c + ratio / cμ)
      / Real.sqrt c ≤ d.coerciveL2)
    (hPin : Real.sqrt (t / c) ≤ d.coercivePin) :
    ExtendedCoerciveClause d :=
  extendedCoerciveClause_of_pieceDataHolds pieceMultiplierDensityWeakHolds_proof hrad hwup hactm hactp hnorm
    HW D hmodel m hs hc hcμ ht hm hrest hL2 hPin

end Extended

end CoerciveWeak

end Breakdown
