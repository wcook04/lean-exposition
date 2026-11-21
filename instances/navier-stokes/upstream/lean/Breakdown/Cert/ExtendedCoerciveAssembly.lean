import Breakdown.Cert.ExtendedCoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

open PieceWeights

theorem pieceFieldExistsWeak_of_zeroFlow (hF : Coercive.PieceFieldExistsHolds)
    (hZ : ZeroFlowAdmissibleHolds) : PieceFieldExistsWeakHolds := by
  intro C nE nM m P h w Γ W HW D w₀ epsSup epsGradSup ratio hm hwb v G H g hv
  exact hF (zeroFlowWeights m) P h w Γ (fun _ _ => 0) (hZ m P h w W HW hm) hwb v G H g hv

theorem isAdmissibleWeak_of_isAdmissibleHolds (hV : VortGradMapSecondDerivFieldHolds) {C : Type} {nE nM : ℕ}
    {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ} {W : ℝ → Space → Space}
    {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    IsAdmissibleWeak m P h w W (secondDerivField W) w₀ epsSup epsGradSup ratio :=
  { hm with
    supGradVort_ge := fun σ φ y => by
      rw [hV W hW σ (axialRot φ y)]
      exact hm.supGradVort_ge σ φ y }

theorem vortGradSupWith_secondDerivFieldHolds (hV : VortGradMapSecondDerivFieldHolds) (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    vortGradSupWith (secondDerivField W) = Coercive.vortGradSup W := by
  funext y
  simp only [vortGradSupWith, Coercive.vortGradSup, hV W hW]

theorem pieceEpsBlockWith_secondDerivFieldHolds (hV : VortGradMapSecondDerivFieldHolds) {C : Type} {nE nM : ℕ}
    (m : PieceWeights C nE nM) (W : ℝ → Space → Space) (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    pieceEpsBlockWith m W (secondDerivField W) = Coercive.pieceEpsBlock m W := by
  funext v G H β σ y
  simp only [pieceEpsBlockWith, Coercive.pieceEpsBlock, vortGradSupWith_secondDerivFieldHolds hV W hW]

theorem pieceBlockWith_secondDerivFieldHolds (hV : VortGradMapSecondDerivFieldHolds) {C : Type} {nE nM : ℕ}
    (m : PieceWeights C nE nM) (W : ℝ → Space → Space) (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    pieceBlockWith m W (secondDerivField W) = Coercive.pieceBlock m W := by
  funext v G H σ y
  simp only [pieceBlockWith, Coercive.pieceBlock, pieceEpsBlockWith_secondDerivFieldHolds hV m W hW]

theorem pieceMultiplierDensity_of_weakHolds (hV : VortGradMapSecondDerivFieldHolds)
    (hS : WeakSecondDerivStateOfContDiffHolds) (hD : PieceMultiplierDensityWeakHolds) :
    Coercive.PieceMultiplierDensityHolds := by
  intro C nE nM m P h w k Γ W act w₀ epsSup epsGradSup ratio hm hW hWp hWdiv hWdecay hwb hactm hactp hact2
    v G H g hv κ F hFm hFp hF2 hR
  obtain ⟨D, hD2⟩ := hWdecay
  exact hD m P h w Γ W (secondDerivField W) D act (isAdmissibleWeak_of_isAdmissibleHolds hV hm hW)
    (hS W hW hWp hWdiv hD2) hwb hactm hactp hact2 v G H g hv κ F hFm hFp hF2 hR

theorem pieceEpsEstimateSmooth_of_weak (hV : VortGradMapSecondDerivFieldHolds) (hS : WeakSecondDerivStateOfContDiffHolds)
    (hE : PieceEpsEstimateSmoothWeakHolds) : Coercive.PieceEpsEstimateSmoothHolds := by
  intro C nE nM m P h w W w₀ epsSup epsGradSup ratio hm hW hWp hWdiv hWdecay hwb v hv β
  obtain ⟨D, hD⟩ := hWdecay
  have key := hE m P h w W (secondDerivField W) D (isAdmissibleWeak_of_isAdmissibleHolds hV hm hW)
    (hS W hW hWp hWdiv hD) hwb v hv β
  rw [pieceEpsBlockWith_secondDerivFieldHolds hV m W hW] at key
  exact key

theorem pieceMuEstimateSmooth_of_weak (hV : VortGradMapSecondDerivFieldHolds) (hS : WeakSecondDerivStateOfContDiffHolds)
    (hM : PieceMuEstimateSmoothWeakHolds) : Coercive.PieceMuEstimateSmoothHolds := by
  intro C nE nM m P h w W w₀ epsSup epsGradSup ratio hm hW hWp hWdiv hWdecay hwb v hv Q hQ β
  obtain ⟨D, hD⟩ := hWdecay
  exact hM m P h w W (secondDerivField W) D (isAdmissibleWeak_of_isAdmissibleHolds hV hm hW)
    (hS W hW hWp hWdiv hD) hwb v hv Q hQ β

theorem pieceDensityPassage_of_weak (hV : VortGradMapSecondDerivFieldHolds) (hS : WeakSecondDerivStateOfContDiffHolds)
    (hP : PieceDensityPassageWeakHolds) : Coercive.PieceDensityPassageHolds := by
  intro C nE nM m P h w k Γ W act w₀ epsSup epsGradSup ratio hm hW hWp hWdiv hWdecay hwb hactm hactp hact2
    v G H g hv u hu κ F hFm hFp hF2 hR M hMF
  obtain ⟨D, hD⟩ := hWdecay
  have key := hP m P h w Γ W (secondDerivField W) D act (isAdmissibleWeak_of_isAdmissibleHolds hV hm hW)
    (hS W hW hWp hWdiv hD) hwb hactm hactp hact2 v G H g hv u hu κ F hFm hFp hF2 hR M hMF
  rw [pieceBlockWith_secondDerivFieldHolds hV m W hW] at key
  exact key

theorem pieceMultiplierDensityWeakHolds_of_nodes
    (p1 : Coercive.ModeSquareSumHolds) (d1 : Coercive.ModeDerivativeHolds)
    (r1 : Coercive.ModeRotationHolds) (l1 : Coercive.SolenoidalModeHolds)
    (hSP : Coercive.SmoothPerturbationIsPerturbationHolds)
    (hI1 : EnergyIdentitySmoothWeakHolds) (hBase : Coercive.BaseDensitySmoothHolds)
    (hSplit : PiecePairingSplitSmoothWeakHolds) (hEps : PieceEpsEstimateSmoothWeakHolds)
    (hMu : PieceMuEstimateSmoothWeakHolds)
    (hSmooth : PiecePairingSplitSmoothWeakHolds → EnergyIdentitySmoothWeakHolds →
      Coercive.BaseDensitySmoothHolds → PieceEpsEstimateSmoothWeakHolds →
      PieceMuEstimateSmoothWeakHolds → Coercive.SolenoidalModeHolds → PieceDensitySmoothWeakHolds)
    (hFieldSmooth : Coercive.PieceFieldExistsHolds) (hZero : ZeroFlowAdmissibleHolds)
    (hApprox : Coercive.SmoothApproximationHolds)
    (hPass : PieceDensitySmoothWeakHolds → Coercive.ModeSquareSumHolds → Coercive.ModeDerivativeHolds →
      Coercive.ModeRotationHolds → PieceFieldExistsWeakHolds → Coercive.SolenoidalModeHolds →
      Coercive.SmoothPerturbationIsPerturbationHolds → PieceDensityPassageWeakHolds)
    (hAbsorb : PieceAbsorbStepWeakHolds) : PieceMultiplierDensityWeakHolds :=
  pieceMultiplierDensityWeak_of_nodes (pieceFieldExistsWeak_of_zeroFlow hFieldSmooth hZero) hApprox
    (hPass (hSmooth hSplit hI1 hBase hEps hMu l1) p1 d1 r1
      (pieceFieldExistsWeak_of_zeroFlow hFieldSmooth hZero) l1 hSP) hAbsorb

section Extended

variable {k : ℕ}

theorem extendedCoerciveClause_of_pieceDataHolds (hD : PieceMultiplierDensityWeakHolds)
    {d : ExtendedCertificateData k}
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
  extendedCoerciveClause_of_rowMultiplierInequality
    (rowMultiplierInequality_of_pieceDensity hD hrad hwup hactm hactp
      (actuator_finite d hnorm) HW D hmodel m hs hc hcμ ht hm hrest) hL2 hPin

end Extended

end CoerciveWeak

end Breakdown
