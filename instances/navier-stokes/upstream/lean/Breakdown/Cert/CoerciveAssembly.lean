import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.Nodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

theorem multiplierDensity_of_field (hF : ModeFieldExistsHolds) (hD : ModeDensityOfFieldHolds)
    (hY : ModeAbsorbStepHolds) : MultiplierDensityHolds := by
  intro C m P b w k Γ W act w₀ epsSup epsGradSup ratio hm hb hW hWp hWdiv hWdecay hwb hactm hactp
    hact2 v G H g hv κ F hFm hFp hF2 hR
  obtain ⟨hfin, M, hMF, hnorm⟩ := hF m P b w Γ hm hwb v G H g hv
  exact ⟨M, hMF, hfin, hnorm, hY m P b w Γ W hm hb hW hWp hWdiv hWdecay hwb v G H g hv _
    (hD m P b w Γ W act hm hb hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g hv κ F hFm hFp hF2 hR M hMF)⟩

theorem pieceMultiplierDensity_of_field (hF : PieceFieldExistsHolds) (hD : PieceDensityOfFieldHolds)
    (hY : PieceAbsorbStepHolds) : PieceMultiplierDensityHolds := by
  intro C nE nM m P h w k Γ W act w₀ epsSup epsGradSup ratio hm hW hWp hWdiv hWdecay hwb hactm hactp
    hact2 v G H g hv κ F hFm hFp hF2 hR
  obtain ⟨hfin, M, hMF, hnorm⟩ := hF m P h w Γ W hm hwb v G H g hv
  exact ⟨M, hMF, hfin, hnorm, hY m P h w Γ W hm hW hWp hWdiv hWdecay hwb v G H g hv _
    (hD m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g hv κ F hFm hFp hF2 hR M hMF)⟩

theorem modeDensity_eq_split {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)
    (ι : ℤ × ℤ) (y : Space) (x2 xc x1 xo x0 : ℝ) :
    m.modeDensity P b w ι y x2 xc x1 xo x0 =
      baseDensity m.convD m.convZ (m.classOf ι) m.c w y x2 xc x1 xo x0
        + modeEpsDensity m P b ι y xc xo x1 x0 + modeMuDensity m P b ι y x1 x0 := by
  unfold ModeWeights.modeDensity baseDensity modeEpsDensity modeMuDensity ModeWeights.coefAA ModeWeights.coefC
  ring

theorem pieceDensity_eq_split {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (ι : ℤ × ℤ) (y : Space) (x2 xc x1 xo x0 : ℝ) :
    m.modeDensity P h w ι y x2 xc x1 xo x0 =
      baseDensity m.convD m.convZ (m.classOf ι) m.c w y x2 xc x1 xo x0
        + ∑ β : Fin nE, pieceEpsDensity m P h β ι y xc xo x1 x0
        + ∑ β : Fin nM, pieceMuDensity m P h β ι y x1 x0 := by
  unfold PieceWeights.modeDensity baseDensity pieceEpsDensity pieceMuDensity PieceWeights.shareHat
    PieceWeights.coefA PieceWeights.coefAA PieceWeights.coefB
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

theorem modeDensityOfField_of_passage (hP : ModeDensityPassageHolds) (hA : SmoothApproximationHolds) :
    ModeDensityOfFieldHolds := by
  intro C m P b w k Γ W act w₀ epsSup epsGradSup ratio hm hb hW hWp hWdiv hWdecay hwb hactm hactp hact2
    v G H g hv κ F hFm hFp hF2 hR M hMF
  obtain ⟨u, hu⟩ := hA Γ P v G H g hv
  exact hP m P b w Γ W act hm hb hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g hv u hu κ F hFm hFp hF2 hR
    M hMF

theorem pieceDensityOfField_of_passage (hP : PieceDensityPassageHolds) (hA : SmoothApproximationHolds) :
    PieceDensityOfFieldHolds := by
  intro C nE nM m P h w k Γ W act w₀ epsSup epsGradSup ratio hm hW hWp hWdiv hWdecay hwb hactm hactp hact2
    v G H g hv κ F hFm hFp hF2 hR M hMF
  obtain ⟨u, hu⟩ := hA Γ P v G H g hv
  exact hP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g hv u hu κ F hFm hFp hF2 hR
    M hMF

theorem multiplierDensityHolds_of_nodes
    (hRot : AxialRotationHolds) (hTorus : TorusSquareSumHolds)
    (hPars : TorusSquareSumHolds → AxialRotationHolds → ModeSquareSumHolds)
    (hDer : AxialRotationHolds → ModeDerivativeHolds)
    (hRotM : AxialRotationHolds → ModeRotationHolds)
    (hProj : Cert.ProjectionHolds) (hTest : Cert.TestPairingHolds)
    (hSolenoidal : Cert.ProjectionHolds → Cert.TestPairingHolds → AxialRotationHolds → SolenoidalModeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hI1 : EnergyIdentitySmoothHolds) (hI4 : CurlWeightIdentityDecayHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds)
    (hBase : ModeSquareSumHolds → CurlWeightIdentityDecayHolds → BaseDensitySmoothHolds)
    (hSplit : ModeSquareSumHolds → ModeDerivativeHolds → SolenoidalModeHolds → SmoothPerturbationIsPerturbationHolds →
      ModePairingSplitSmoothHolds)
    (hEps : ModeSquareSumHolds → ModeDerivativeHolds → ModeRotationHolds → SmoothPerturbationIsPerturbationHolds →
      WeightedSumSecondPartialsPairingHolds → ModeEpsEstimateSmoothHolds)
    (hMu : ModeSquareSumHolds → ModeDerivativeHolds → ModeRotationHolds → SolenoidalModeHolds →
      SmoothPerturbationIsPerturbationHolds → WeightedSumSecondPartialsPairingHolds → ModeMuEstimateSmoothHolds)
    (hSmooth : ModePairingSplitSmoothHolds → EnergyIdentitySmoothHolds → BaseDensitySmoothHolds →
      ModeEpsEstimateSmoothHolds → ModeMuEstimateSmoothHolds → SolenoidalModeHolds → ModeDensitySmoothHolds)
    (hField : ModeSquareSumHolds → ModeDerivativeHolds → ModeRotationHolds → SolenoidalModeHolds → ModeFieldExistsHolds)
    (hApprox : SmoothApproximationHolds)
    (hPass : ModeDensitySmoothHolds → ModeSquareSumHolds → ModeDerivativeHolds → ModeRotationHolds →
      ModeFieldExistsHolds → SolenoidalModeHolds → SmoothPerturbationIsPerturbationHolds → ModeDensityPassageHolds)
    (hAbsorb : ModeSquareSumHolds → ModeAbsorbStepHolds) :
    MultiplierDensityHolds := by
  have p1 : ModeSquareSumHolds := hPars hTorus hRot
  have d1 : ModeDerivativeHolds := hDer hRot
  have r1 : ModeRotationHolds := hRotM hRot
  have l1 : SolenoidalModeHolds := hSolenoidal hProj hTest hRot
  have f1 : ModeFieldExistsHolds := hField p1 d1 r1 l1
  have s1 : ModeDensitySmoothHolds := hSmooth (hSplit p1 d1 l1 hSP) hI1 (hBase p1 hI4) (hEps p1 d1 r1 hSP hSsp)
    (hMu p1 d1 r1 l1 hSP hSsp) l1
  exact @multiplierDensity_of_field f1
    (modeDensityOfField_of_passage (hPass s1 p1 d1 r1 f1 l1 hSP) hApprox) (hAbsorb p1)

theorem pieceMultiplierDensityHolds_of_nodes
    (hRot : AxialRotationHolds) (hTorus : TorusSquareSumHolds)
    (hPars : TorusSquareSumHolds → AxialRotationHolds → ModeSquareSumHolds)
    (hDer : AxialRotationHolds → ModeDerivativeHolds)
    (hRotM : AxialRotationHolds → ModeRotationHolds)
    (hProj : Cert.ProjectionHolds) (hTest : Cert.TestPairingHolds)
    (hSolenoidal : Cert.ProjectionHolds → Cert.TestPairingHolds → AxialRotationHolds → SolenoidalModeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    (hI1 : EnergyIdentitySmoothHolds) (hI4 : CurlWeightIdentityDecayHolds)
    (hSsp : WeightedSumSecondPartialsPairingHolds)
    (hBase : ModeSquareSumHolds → CurlWeightIdentityDecayHolds → BaseDensitySmoothHolds)
    (hSplit : ModeSquareSumHolds → ModeDerivativeHolds → SolenoidalModeHolds → SmoothPerturbationIsPerturbationHolds →
      PiecePairingSplitSmoothHolds)
    (hEps : ModeSquareSumHolds → ModeDerivativeHolds → ModeRotationHolds → SmoothPerturbationIsPerturbationHolds →
      WeightedSumSecondPartialsPairingHolds → PieceEpsEstimateSmoothHolds)
    (hMu : ModeSquareSumHolds → ModeDerivativeHolds → ModeRotationHolds → SolenoidalModeHolds →
      SmoothPerturbationIsPerturbationHolds → WeightedSumSecondPartialsPairingHolds → PieceMuEstimateSmoothHolds)
    (hSmooth : PiecePairingSplitSmoothHolds → EnergyIdentitySmoothHolds → BaseDensitySmoothHolds →
      PieceEpsEstimateSmoothHolds → PieceMuEstimateSmoothHolds → SolenoidalModeHolds → PieceDensitySmoothHolds)
    (hField : ModeSquareSumHolds → ModeDerivativeHolds → ModeRotationHolds → SolenoidalModeHolds → PieceFieldExistsHolds)
    (hApprox : SmoothApproximationHolds)
    (hPass : PieceDensitySmoothHolds → ModeSquareSumHolds → ModeDerivativeHolds → ModeRotationHolds →
      PieceFieldExistsHolds → SolenoidalModeHolds → SmoothPerturbationIsPerturbationHolds → PieceDensityPassageHolds)
    (hAbsorb : ModeSquareSumHolds → PieceAbsorbStepHolds) :
    PieceMultiplierDensityHolds := by
  have p1 : ModeSquareSumHolds := hPars hTorus hRot
  have d1 : ModeDerivativeHolds := hDer hRot
  have r1 : ModeRotationHolds := hRotM hRot
  have l1 : SolenoidalModeHolds := hSolenoidal hProj hTest hRot
  have f1 : PieceFieldExistsHolds := hField p1 d1 r1 l1
  have s1 : PieceDensitySmoothHolds := hSmooth (hSplit p1 d1 l1 hSP) hI1 (hBase p1 hI4) (hEps p1 d1 r1 hSP hSsp)
    (hMu p1 d1 r1 l1 hSP hSsp) l1
  exact @pieceMultiplierDensity_of_field f1
    (pieceDensityOfField_of_passage (hPass s1 p1 d1 r1 f1 l1 hSP) hApprox) (hAbsorb p1)

theorem modeAzimuthalGainHolds_of_nodes (hRot : AxialRotationHolds)
    (hDer : AxialRotationHolds → ModeDerivativeHolds) (hRotM : AxialRotationHolds → ModeRotationHolds)
    (hGain : AxialRotationHolds → ModeDerivativeHolds → ModeRotationHolds → ModeAzimuthalGainHolds) :
    ModeAzimuthalGainHolds :=
  hGain hRot (hDer hRot) (hRotM hRot)

theorem stretchMeanBoundHolds_of_nodes (hRot : AxialRotationHolds) (hTorus : TorusSquareSumHolds)
    (hStretch : TorusSquareSumHolds → AxialRotationHolds → StretchMeanBoundHolds) :
    StretchMeanBoundHolds :=
  hStretch hTorus hRot

theorem multiplierInequality_of_densityHolds (hD : MultiplierDensityHolds) {k : ℕ} {d : CertificateData k}
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
  have hcen : d.center ∈ d.box := by
    constructor <;> intro i <;> simp [hrad i]
  have hc0 : 0 < c := hc d.center hcen ▸ (hm d.center hcen).c_pos
  have hcμ0 : 0 < cμ := hcμ d.center hcen ▸ (hm d.center hcen).cμ_pos
  refine ⟨hc0, hcμ0.le, ht, Real.sqrt_nonneg _, hK, ?_⟩
  intro p hp v G H g hv κ F hFm hFp hF2 hR
  have hWs : ContDiff ℝ 2 (fun z : ℝ × Space => d.profile p z.1 z.2) :=
    hsmooth.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨M, hMF, hfin, hnorm, hdens⟩ := hD (m p) (d.period p) (b p) d.weightFn
    d.symmetries (d.profile p) d.actuator (hm p hp) (hb p hp) hWs (hper p)
    (hdiv p hp) ⟨d.decay, hdecay p hp⟩ ⟨d.weightMax, hwup⟩ hactm hactp hact2
    v G H g hv κ F hFm hFp hF2 hR
  obtain ⟨hneg, hbm⟩ := hrest p hp v G H g hv κ F hFm hFp hF2 hR M hMF
  set n2 := ((m p).frequencySeminormSq (d.period p) v).toReal with hn2
  have hn20 : 0 ≤ n2 := ENNReal.toReal_nonneg
  refine ⟨M, Real.sqrt n2, hMF.1, hMF.2.2.1, Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [Real.sq_sqrt hn20]
    have e : (m p).multiplierConstant d.weight epsSup epsGradSup ratio
        = Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt d.weight) ^ 2 / c + ratio / cμ) := by
      unfold ModeWeights.multiplierConstant
      rw [hc p hp, hcμ p hp]
    rw [← e, ← hc p hp, ← hcμ p hp]
    exact hnorm
  · rw [Real.sq_sqrt hn20]
    have key := ModeWeights.le_of_ennreal_bounds hneg hdens hbm
    unfold ModeWeights.multiplierGap at key
    rw [hc p hp, hcμ p hp] at key
    linarith


theorem multiplierInequality_of_pieceDensityHolds (hD : PieceMultiplierDensityHolds) {k : ℕ} {d : CertificateData k}
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
  have hcen : d.center ∈ d.box := by
    constructor <;> intro i <;> simp [hrad i]
  have hc0 : 0 < c := hc d.center hcen ▸ (hm d.center hcen).c_pos
  have hcμ0 : 0 < cμ := hcμ d.center hcen ▸ (hm d.center hcen).cμ_pos
  refine ⟨hc0, hcμ0.le, ht, Real.sqrt_nonneg _, hK, ?_⟩
  intro p hp v G H g hv κ F hFm hFp hF2 hR
  have hWs : ContDiff ℝ 2 (fun z : ℝ × Space => d.profile p z.1 z.2) :=
    hsmooth.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨M, hMF, hfin, hnorm, hdens⟩ := hD (m p) (d.period p) (hs p)
    d.weightFn d.symmetries (d.profile p) d.actuator (hm p hp) hWs (hper p)
    (hdiv p hp) ⟨d.decay, hdecay p hp⟩ ⟨d.weightMax, hwup⟩ hactm hactp hact2
    v G H g hv κ F hFm hFp hF2 hR
  obtain ⟨hneg, hbm⟩ := hrest p hp v G H g hv κ F hFm hFp hF2 hR M hMF
  set n2 := ((m p).seminormSq (d.period p) v).toReal with hn2
  have hn20 : 0 ≤ n2 := ENNReal.toReal_nonneg
  refine ⟨M, Real.sqrt n2, hMF.1, hMF.2.2.1, Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [Real.sq_sqrt hn20]
    rw [← hc p hp, ← hcμ p hp]
    exact hnorm
  · rw [Real.sq_sqrt hn20]
    have key := ModeWeights.le_of_ennreal_bounds hneg hdens hbm
    unfold PieceWeights.multiplierGap at key
    rw [hc p hp, hcμ p hp] at key
    linarith


end Coercive

end Breakdown
