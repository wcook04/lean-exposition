import Breakdown.Cert.CoercivePieceDensityPassageRight
import Breakdown.Cert.CoerciveDensityPassageEnergy
import Breakdown.Cert.CoerciveDensityPassagePairing
import Breakdown.Cert.CoerciveFrequencySeminormBound
import Breakdown.Cert.CoercivePieceDensityPassageMeasurable
import Breakdown.Cert.CoercivePieceDensityPassageRest
import Breakdown.Cert.CoercivePieceDensityPassageMultiplier
import Breakdown.Cert.CoercivePieceDensityPassageSubsequence

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

open Internal.PassageLimit

namespace PieceDensityPassage

namespace Internal

theorem multiplier_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) :
    Tendsto (fun n => periodLIntegral (fun σ y => ‖Mn n σ y - M σ y‖ ^ 2)) atTop (𝓝 0) := by
  exact Breakdown.Coercive.Internal.PieceDensityPassageMultiplier.multiplier_tendsto_of hPars hDer hRot hField hSolenoidal
    hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF Mn hMn

theorem rightSideLimit_memL2 (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M) :
    AEStronglyMeasurable (fun z : ℝ × Space => (rightSideLimit W act κ v G H g) z.1 z.2) volume ∧
      periodLIntegral (fun σ y => ‖(rightSideLimit W act κ v G H g) σ y‖ ^ 2) < ⊤ := by
  exact Breakdown.Coercive.Internal.PassageLimit.rightSideLimit_memL2 κ hv hW hWdecay hactm hact2 (weightedVelocity_lt_top hv hu)

theorem smoothRight_memL2 (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M) (n : ℕ) :
    AEStronglyMeasurable (fun z : ℝ × Space => (fun σ y => smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) z.1 z.2) volume ∧
      periodLIntegral (fun σ y => ‖(fun σ y => smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) σ y‖ ^ 2) < ⊤ := by
  exact Breakdown.Coercive.Internal.PassageLimit.smoothRight_memL2 κ hSP (hu.1 n) hW hWdecay hactm hact2

theorem smoothRight_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M) :
    Tendsto (fun n => periodLIntegral (fun σ y => ‖(fun σ y => smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) σ y - (rightSideLimit W act κ v G H g) σ y‖ ^ 2)) atTop (𝓝 0) := by
  exact Breakdown.Coercive.Internal.PassageLimit.smoothRight_tendsto κ hSP hv hu hWdecay

theorem rightSide_pairing_eq (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M) :
    periodPairing F M = periodPairing (rightSideLimit W act κ v G H g) M := by
  exact Breakdown.Coercive.Internal.DensityPassage.pairing_rightSideLimit_eq hSolenoidal κ hv hW hWp hWdecay hactm hactp
    hact2 (Breakdown.Coercive.Internal.PassageLimit.weightedVelocity_lt_top hv hu) hFm hFp hF2 hR hMF.1 hMF.2.1 hMF.2.2.1 hMF.2.2.2.1

theorem energy_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M) :
    Tendsto (fun n => weightedEnergy w (gradField (u n)) (secondDerivField (u n))) atTop
      (𝓝 (weightedEnergy w G H)) := by
  obtain ⟨B, hB⟩ := hwb
  exact Breakdown.Coercive.weightedEnergy_tendsto (B := B) hm.weight_measurable
    (fun y => hm.weight_pos.le.trans (hm.weight_lower y)) hB hv.measurable_gradient hv.measurable_secondDeriv
    (fun n => (hSP P (u n) (hu.1 n)).measurable_gradient) (fun n => (hSP P (u n) (hu.1 n)).measurable_secondDeriv)
    hv.gradient_finite hv.sumSecondPartials_finite hu.2.1 hu.2.2.1

theorem seminorm_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M) :
    Tendsto (fun n => (m.seminormSq P (u n)).toReal) atTop (𝓝 (m.seminormSq P v).toReal) := by
  obtain ⟨B, hB⟩ := hm.mu_decay
  exact (Breakdown.Coercive.FrequencyBound.pieceSeminormSq_tendsto_of_approximation m hPars hDer hRot hSP hv
    hm.period_pos hm.mu_wt_nonneg (fun β y => ⟨(hB β y).1, (hB β y).2.1⟩)
    (fun β => let ⟨_, hK⟩ := hm.mu_increment β; hK.continuous.measurable) hu).2

theorem right_pairing_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) :
    Tendsto (fun n => periodPairing (fun σ y => smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) (Mn n)) atTop (𝓝 (periodPairing F M)) := by
  rw [rightSide_pairing_eq hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF]
  exact periodPairing_tendsto (fun n => (smoothRight_memL2 hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF n).1)
    (fun n => (smoothRight_memL2 hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF n).2)
    (rightSideLimit_memL2 hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF).1 (rightSideLimit_memL2 hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF).2
    (fun n => (hMn n).1) (fun n => (hMn n).2.2.1) hMF.1 hMF.2.2.1
    (smoothRight_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF) (multiplier_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF Mn hMn)

theorem action_pairing_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) (i : Fin k) :
    Tendsto (fun n => periodPairing (act i) (Mn n)) atTop (𝓝 (periodPairing (act i) M)) :=
  periodPairing_tendsto_right (hactm i) (hact2 i) (fun n => (hMn n).1) (fun n => (hMn n).2.2.1) hMF.1 hMF.2.2.1
    (multiplier_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF Mn hMn)

theorem gap_tendsto (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) :
    Tendsto (fun n => m.multiplierGap P w act (u n) (gradField (u n)) (secondDerivField (u n)) κ
        (fun σ y => smoothRight P W (u n) σ y + ∑ i, κ i • act i σ y) (Mn n)) atTop
      (𝓝 (m.multiplierGap P w act v G H κ F M)) := by
  unfold PieceWeights.multiplierGap
  exact (((right_pairing_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF Mn hMn).sub
    ((energy_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF).const_mul m.c)).sub ((seminorm_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF).const_mul m.cμ)).sub
    (tendsto_finsetSum _ fun i _ => (action_pairing_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF Mn hMn i).const_mul (κ i))

theorem right_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight (fun σ y ι => pieceRest m h w W v G H ι σ y) (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G) σ y) < ⊤ := by
  exact Breakdown.Coercive.Internal.PieceDensityPassageRest.right_finite_of hPars hDer hRot hField hSolenoidal hSP m P h w Γ W
    act hm hW hWp hWdiv hWdecay hwb v G H g u hv hu

theorem left_measurable (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (u₀ : ℝ → Space → Space) (hu₀ : IsSmoothPerturbation P u₀) :
    (∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      AEMeasurable (fun y => splitLeft (fun σ y ι => piecePos m P (u₀) (gradField (u₀)) ι σ y) (fun σ y ι => pieceRest m h w W (u₀) (gradField (u₀)) (secondDerivField (u₀)) ι σ y) (fun σ y => pieceBlock m W (u₀) (gradField (u₀)) (secondDerivField (u₀)) σ y) (stretchForm W (u₀) (gradField (u₀))) σ y) volume) ∧
    AEMeasurable (fun σ => ∫⁻ y, splitLeft (fun σ y ι => piecePos m P (u₀) (gradField (u₀)) ι σ y) (fun σ y ι => pieceRest m h w W (u₀) (gradField (u₀)) (secondDerivField (u₀)) ι σ y) (fun σ y => pieceBlock m W (u₀) (gradField (u₀)) (secondDerivField (u₀)) σ y) (stretchForm W (u₀) (gradField (u₀))) σ y)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  exact Breakdown.Coercive.Internal.PieceDensityPassageMeasure.pieceSplitLeft_aemeasurable hm hW hWdecay hu₀

theorem subsequence_limits (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          splitRight (fun σ y ι => pieceRest m h w W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y) (fun σ y => pieceBlock m W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) σ y) (stretchForm W (u (φ n)) (gradField (u (φ n)))) σ y) atTop
        (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight (fun σ y ι => pieceRest m h w W v G H ι σ y) (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G) σ y)) ∧
      ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y, splitLeft (fun σ y ι => piecePos m P v G ι σ y) (fun σ y ι => pieceRest m h w W v G H ι σ y) (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G) σ y
        ≤ liminf (fun n => splitLeft (fun σ y ι => piecePos m P (u (φ n)) (gradField (u (φ n))) ι σ y) (fun σ y ι => pieceRest m h w W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) ι σ y) (fun σ y => pieceBlock m W (u (φ n)) (gradField (u (φ n))) (secondDerivField (u (φ n))) σ y) (stretchForm W (u (φ n)) (gradField (u (φ n)))) σ y) atTop := by
  exact Breakdown.Coercive.Internal.PieceDensityPassageSubsequence.subsequence_limits_of hPars hDer hRot hField hSolenoidal hSP
    m P h w Γ W act hm hW hWp hWdiv hWdecay hwb v G H g u hv hu

end Internal

end PieceDensityPassage

open PieceDensityPassage.Internal in
theorem pieceDensityPassageHolds_of (hSmooth : PieceDensitySmoothHolds) (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds) :
    PieceDensityPassageHolds := by
  intro C nE nM m P h w k Γ W act w₀ epsSup epsGradSup ratio hm hW hWp hWdiv hWdecay hwb hactm hactp hact2
    v G H g hv u hu κ F hFm hFp hF2 hR M hMF
  have hex : ∀ n, ∃ Mn, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) Mn := fun n =>
    let ⟨_, Mn, hMn, _⟩ := hField m P h w ∅ W hm hwb (u n) (gradField (u n)) (secondDerivField (u n))
      (transportPart P (u n)) (hSP P (u n) (hu.1 n))
    ⟨Mn, hMn⟩
  choose Mn hMn using hex
  obtain ⟨φ, hφ, hN, hlow⟩ := subsequence_limits hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp
    hWdiv hWdecay hwb v G H g u hv hu
  have hgap := gap_tendsto hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v G H g u hv hu κ F M hFm hFp hF2 hR hMF Mn hMn
  exact isSplitLowerBound_of_liminf
    (fun n => hSmooth m P h w W act hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 (u (φ n)) (hu.1 (φ n)) κ
      (Mn (φ n)) (hMn (φ n)))
    (hgap.comp hφ.tendsto_atTop) hN
    (right_finite hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb v G H g u hv hu)
    (fun n => (left_measurable hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb
      (u (φ n)) (hu.1 (φ n))).1)
    (fun n => (left_measurable hPars hDer hRot hField hSolenoidal hSP m P h w Γ W act hm hW hWp hWdiv hWdecay hwb
      (u (φ n)) (hu.1 (φ n))).2)
    hlow

end Coercive

end Breakdown
