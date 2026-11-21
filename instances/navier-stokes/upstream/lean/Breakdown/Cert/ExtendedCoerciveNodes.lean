import Breakdown.Cert.ExtendedCoerciveStatement

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

open PieceWeights

def WeakSecondDerivSymmetricHolds : Prop :=
  ∀ {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ},
    IsWeakSecondDerivState W HW D → ∀ σ : ℝ, ∀ᵐ y, ∀ a b : Space, HW σ y a b = HW σ y b a

def WeakSecondDerivStateOfContDiffHolds : Prop :=
  ∀ (W : ℝ → Space → Space), ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) → ∀ {D : ℝ},
    (∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    IsWeakSecondDerivState W (secondDerivField W) D

def VortGradMapSecondDerivFieldHolds : Prop :=
  ∀ (W : ℝ → Space → Space), ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → ∀ (σ : ℝ) (y : Space),
    vortGradMap (secondDerivField W σ y) = fderiv ℝ (fun x => curlVec (fderiv ℝ (W σ) x)) y

def zeroFlowWeights {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) : PieceWeights C nE nM :=
  { m with
    epsP := fun β => { m.epsP β with speed := fun y => (1 / 2 + |(m.epsP β).frame|) * ‖y‖ }
    muP := fun β => { m.muP β with speed := fun y => (1 / 2 + |(m.muP β).frame|) * ‖y‖ } }

def ZeroFlowAdmissibleHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    {w₀ epsSup epsGradSup ratio : ℝ},
    IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    (zeroFlowWeights m).IsAdmissible P h w (fun _ _ => 0) w₀ epsSup epsGradSup ratio

end CoerciveWeak

end Breakdown
