import Breakdown.Cert.CoerciveAssembly
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveTorus
import Breakdown.Cert.CoerciveSquareSum
import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveSolenoidal
import Breakdown.Cert.CoerciveTestDensityProof
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveSmoothIsPerturbation
import Breakdown.Cert.CoerciveSmoothEnergyIdentity
import Breakdown.Cert.CoerciveSmoothCurlWeight
import Breakdown.Cert.CoerciveSmoothSumSecondPartialsPairing
import Breakdown.Cert.CoerciveSmoothEps
import Breakdown.Cert.CoerciveSmoothMu
import Breakdown.Cert.CoerciveField
import Breakdown.Cert.CoerciveSmoothApprox
import Breakdown.Cert.CoerciveDensityPassage
import Breakdown.Cert.CoerciveAbsorb
import Breakdown.Cert.CoerciveSmoothPiecePairingSplit
import Breakdown.Cert.CoerciveSmoothPieceEps
import Breakdown.Cert.CoerciveSmoothPieceMu
import Breakdown.Cert.CoercivePieceField
import Breakdown.Cert.CoercivePieceDensityPassage
import Breakdown.Cert.CoercivePieceAbsorb
import Breakdown.Cert.CoerciveGain
import Breakdown.Cert.CoerciveStretch
import Breakdown.Cert.ProjectionSpec
import Breakdown.Cert.TestPairing
import Breakdown.Cert.CoerciveSmoothBase
import Breakdown.Cert.CoerciveSmoothPairingSplit
import Breakdown.Cert.CoerciveSmoothDensity
import Breakdown.Cert.CoerciveSmoothPieceDensity

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

theorem projectionHolds_of_spec : Cert.ProjectionHolds :=
  ⟨Cert.exists_projSpec, Cert.norm_solProj_le, Cert.inner_solProj, Cert.solProj_toPhysH⟩

theorem modeSquareSumHolds_proved : ModeSquareSumHolds :=
  modeSquareSumHolds_of torusSquareSumHolds_proof axialRotationHolds_proof

theorem multiplierDensityHolds_proof : MultiplierDensityHolds :=
  multiplierDensityHolds_of_nodes axialRotationHolds_proof torusSquareSumHolds_proof
    modeSquareSumHolds_of
    (fun r => modeDerivativeHolds_of r perturbationLocalIntegrabilityHolds_proof)
    (fun r => modeRotationHolds_of r perturbationLocalIntegrabilityHolds_proof)
    projectionHolds_of_spec Cert.testPairingHolds_proof
    (fun _ _ r => solenoidalModeHolds_of r gradSolenoidalDensityHolds_proof)
    smoothPerturbationIsPerturbationHolds_proof energyIdentitySmoothHolds_proof
    curlWeightIdentityDecayHolds_proof weightedSumSecondPartialsPairingHolds_proof
    baseDensitySmoothHolds_of
    (fun p _ l _ => modePairingSplitSmoothHolds_of p l)
    (fun p _ _ s l => modeEpsEstimateSmoothHolds_of p s l)
    modeMuEstimateSmoothHolds_of
    (modeDensitySmoothHolds_of modeSquareSumHolds_proved)
    (fun p d r _ => modeFieldExistsHolds_of p d r perturbationLocalSquareIntegrabilityHolds_proof)
    smoothApproximationHolds_proof
    modeDensityPassageHolds_of
    modeAbsorbStepHolds_of

theorem pieceMultiplierDensityHolds_proof : PieceMultiplierDensityHolds :=
  pieceMultiplierDensityHolds_of_nodes axialRotationHolds_proof torusSquareSumHolds_proof
    modeSquareSumHolds_of
    (fun r => modeDerivativeHolds_of r perturbationLocalIntegrabilityHolds_proof)
    (fun r => modeRotationHolds_of r perturbationLocalIntegrabilityHolds_proof)
    projectionHolds_of_spec Cert.testPairingHolds_proof
    (fun _ _ r => solenoidalModeHolds_of r gradSolenoidalDensityHolds_proof)
    smoothPerturbationIsPerturbationHolds_proof energyIdentitySmoothHolds_proof
    curlWeightIdentityDecayHolds_proof weightedSumSecondPartialsPairingHolds_proof
    baseDensitySmoothHolds_of
    (fun p _ l _ => piecePairingSplitSmoothHolds_of p l)
    pieceEpsEstimateSmoothHolds_of
    pieceMuEstimateSmoothHolds_of
    (pieceDensitySmoothHolds_of modeSquareSumHolds_proved)
    (fun p d r _ => pieceFieldExistsHolds_of p d r)
    smoothApproximationHolds_proof
    pieceDensityPassageHolds_of
    (fun p => pieceAbsorbStepHolds_of p perturbationSecondDerivBoundHolds_proof
      perturbationLocalSquareIntegrabilityHolds_proof)

theorem modeAzimuthalGainHolds_proof : ModeAzimuthalGainHolds :=
  modeAzimuthalGainHolds_of_nodes axialRotationHolds_proof
    (fun r => modeDerivativeHolds_of r perturbationLocalIntegrabilityHolds_proof)
    (fun r => modeRotationHolds_of r perturbationLocalIntegrabilityHolds_proof)
    modeAzimuthalGainHolds_proof_of

theorem stretchMeanBoundHolds_proof : StretchMeanBoundHolds :=
  stretchMeanBoundHolds_of_nodes axialRotationHolds_proof torusSquareSumHolds_proof
    (fun t r => stretchMeanBoundHolds_proof_of t r perturbationLocalSquareIntegrabilityHolds_proof)

end Coercive

namespace ModeWeights

variable {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)

theorem multiplier_density_proved {k : ℕ} (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) :
    ∀ v G H g, IsPerturbation Γ P v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide W act κ v G g F →
      ∃ M, m.IsMultiplierField v G H M ∧
        m.frequencySeminormSq P v < ⊤ ∧
        periodNorm M ≤ m.multiplierConstant w₀ epsSup epsGradSup ratio
          * Real.sqrt (m.c * weightedEnergy w G H + m.cμ * (m.frequencySeminormSq P v).toReal) ∧
        (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityPos P b w v G H W σ y)
            + ENNReal.ofReal (-m.multiplierGap P w act v G H κ F M)
          ≤ ENNReal.ofReal (m.multiplierGap P w act v G H κ F M)
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityNeg P b w v G H W σ y := by
  exact Coercive.multiplierDensityHolds_proof m P b w Γ W act hm hb hW hWp hWdiv hWdecay hwb hactm hactp
    hact2

theorem mode_azimuthal_gain_proved (Γ : Set Symmetry) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (ι : ℤ × ℤ) (hk : 2 ≤ |ι.2|) :
    ∀ᵐ z : ℝ × Space,
      ((|ι.2| : ℝ) - 1) ^ 2 / cylRadius z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2)
          ≤ cnormSq (modeGrad ι G z.1 z.2) ∧
        ((|ι.2| : ℝ) - 2) ^ 2 / cylRadius z.2 ^ 2 * cnormSq (modeGrad ι G z.1 z.2)
          ≤ cnormSq (modeSecondDeriv ι H z.1 z.2) := by
  exact Coercive.modeAzimuthalGainHolds_proof P Γ v G H g hv ι hk

theorem stretch_mean_bound_proved (Γ : Set Symmetry) (W : ℝ → Space → Space) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hlen : ∀ y, 0 < m.len y) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ y : Space,
      ENNReal.ofReal (-∫ σ in Set.Icc (0 : ℝ) 1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          stretchForm W v G σ (axialRot φ y))
        ≤ ENNReal.ofReal (2 * Real.pi) * ∑' ι : ℤ × ℤ, ENNReal.ofReal (m.stretchCharge b v G ι 0 y) := by
  exact Coercive.stretchMeanBoundHolds_proof m P b Γ W hb hW hWdiv hlen v G H g hv

theorem multiplierInequality_of_density_proved {k : ℕ} {d : CertificateData k}
    (hrad : ∀ i, 0 ≤ d.radius i)
    (hsmooth : ContDiff ℝ 2 (fun q : (Fin k → ℝ) × ℝ × Space => d.profile q.1 q.2.1 q.2.2))
    (hper : ∀ p, IsTimePeriodic (d.profile p))
    (hdiv : ∀ p ∈ d.box, ∀ σ y, divergenceAt (d.profile p σ) y = 0)
    (hdecay : ∀ p ∈ d.box, ∀ σ y, ∀ j ≤ 2,
      ‖iteratedFDeriv ℝ j (d.profile p σ) y‖ ≤ d.decay / (1 + ‖y‖) ^ (j + 1))
    (hwup : ∀ y, d.weightFn y ≤ d.weightMax)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.actuator i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (d.actuator i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) < ⊤)
    {C : Type} (m : (Fin k → ℝ) → ModeWeights C) (b : (Fin k → ℝ) → FlowBounds C)
    {c cμ t K epsSup epsGradSup ratio : ℝ}
    (hc : ∀ p ∈ d.box, (m p).c = c) (hcμ : ∀ p ∈ d.box, (m p).cμ = cμ) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hm : ∀ p ∈ d.box, (m p).IsAdmissible (d.period p) (b p) d.weightFn d.weight epsSup epsGradSup ratio)
    (hb : ∀ p ∈ d.box, (b p).IsValid (m p) (d.profile p))
    (hrest : ∀ p ∈ d.box, ∀ v G H g, IsPerturbation d.symmetries (d.period p) v G H g →
      ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
        AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
        periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
        IsRightSide (d.profile p) d.actuator κ v G g F →
        ∀ M, (m p).IsMultiplierField v G H M →
          (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityNeg (d.period p) (b p) d.weightFn v G H (d.profile p) σ y) < ⊤ ∧
          ENNReal.ofReal (c * ∑ i, κ i ^ 2 - ∑ i, κ i * periodPairing (d.actuator i) M
              - c * K ^ 2 * periodBallNorm d.ballRadius F ^ 2
              - t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2)
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityNeg (d.period p) (b p) d.weightFn v G H (d.profile p) σ y
          ≤ (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityPos (d.period p) (b p) d.weightFn v G H (d.profile p) σ y)
            + ENNReal.ofReal (-(c * ∑ i, κ i ^ 2 - ∑ i, κ i * periodPairing (d.actuator i) M
              - c * K ^ 2 * periodBallNorm d.ballRadius F ^ 2
              - t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2))) :
    MultiplierInequality d c cμ t
      (Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt d.weight) ^ 2 / c + ratio / cμ)) K := by
  exact Coercive.multiplierInequality_of_densityHolds Coercive.multiplierDensityHolds_proof hrad hsmooth hper hdiv
    hdecay hwup hactm hactp hact2 m b hc hcμ ht hK hm hb hrest

end ModeWeights

namespace PieceWeights

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
  (w : Space → ℝ)

theorem piece_multiplier_density_proved {k : ℕ} (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) :
    ∀ v G H g, IsPerturbation Γ P v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide W act κ v G g F →
      ∃ M, m.IsMultiplierField v G H M ∧
        m.seminormSq P v < ⊤ ∧
        periodNorm M ≤ Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt w₀) ^ 2 / m.c + ratio / m.cμ)
          * Real.sqrt (m.c * weightedEnergy w G H + m.cμ * (m.seminormSq P v).toReal) ∧
        (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityPos P h w v G H W σ y)
            + ENNReal.ofReal (-m.multiplierGap P w act v G H κ F M)
          ≤ ENNReal.ofReal (m.multiplierGap P w act v G H κ F M)
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityNeg P h w v G H W σ y := by
  exact Coercive.pieceMultiplierDensityHolds_proof m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2

theorem multiplierInequality_of_pieceDensity_proved {k : ℕ} {d : CertificateData k}
    (hrad : ∀ i, 0 ≤ d.radius i)
    (hsmooth : ContDiff ℝ 2 (fun q : (Fin k → ℝ) × ℝ × Space => d.profile q.1 q.2.1 q.2.2))
    (hper : ∀ p, IsTimePeriodic (d.profile p))
    (hdiv : ∀ p ∈ d.box, ∀ σ y, divergenceAt (d.profile p σ) y = 0)
    (hdecay : ∀ p ∈ d.box, ∀ σ y, ∀ j ≤ 2,
      ‖iteratedFDeriv ℝ j (d.profile p σ) y‖ ≤ d.decay / (1 + ‖y‖) ^ (j + 1))
    (hwup : ∀ y, d.weightFn y ≤ d.weightMax)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.actuator i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (d.actuator i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) < ⊤)
    {C : Type} {nE nM : ℕ} (m : (Fin k → ℝ) → PieceWeights C nE nM)
    (hs : (Fin k → ℝ) → HarmonicBounds)
    {c cμ t K epsSup epsGradSup ratio : ℝ}
    (hc : ∀ p ∈ d.box, (m p).c = c) (hcμ : ∀ p ∈ d.box, (m p).cμ = cμ) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hm : ∀ p ∈ d.box, (m p).IsAdmissible (d.period p) (hs p) d.weightFn (d.profile p)
      d.weight epsSup epsGradSup ratio)
    (hrest : ∀ p ∈ d.box, ∀ v G H g, IsPerturbation d.symmetries (d.period p) v G H g →
      ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
        AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
        periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
        IsRightSide (d.profile p) d.actuator κ v G g F →
        ∀ M, (m p).IsMultiplierField v G H M →
          (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityNeg (d.period p) (hs p) d.weightFn v G H (d.profile p) σ y) < ⊤ ∧
          ENNReal.ofReal (c * ∑ i, κ i ^ 2 - ∑ i, κ i * periodPairing (d.actuator i) M
              - c * K ^ 2 * periodBallNorm d.ballRadius F ^ 2
              - t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2)
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityNeg (d.period p) (hs p) d.weightFn v G H (d.profile p) σ y
          ≤ (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
              (m p).densityPos (d.period p) (hs p) d.weightFn v G H (d.profile p) σ y)
            + ENNReal.ofReal (-(c * ∑ i, κ i ^ 2 - ∑ i, κ i * periodPairing (d.actuator i) M
              - c * K ^ 2 * periodBallNorm d.ballRadius F ^ 2
              - t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2))) :
    MultiplierInequality d c cμ t
      (Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt d.weight) ^ 2 / c + ratio / cμ)) K := by
  exact Coercive.multiplierInequality_of_pieceDensityHolds Coercive.pieceMultiplierDensityHolds_proof hrad hsmooth
    hper hdiv hdecay hwup hactm hactp hact2 m hs hc hcμ ht hK hm hrest

end PieceWeights

end Breakdown
