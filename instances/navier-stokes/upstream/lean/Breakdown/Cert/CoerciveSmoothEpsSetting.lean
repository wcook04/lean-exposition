import Breakdown.Cert.CoerciveSmoothEpsAssembly

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

structure EpsSetting {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)
    (W : ℝ → Space → Space) (w₀ epsSup epsGradSup ratio : ℝ) (v : ℝ → Space → Space) : Prop where
  admissible : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio
  valid : b.IsValid m W
  flow_smooth : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)
  flow_periodic : IsTimePeriodic W
  flow_div : ∀ σ y, divergenceAt (W σ) y = 0
  flow_decay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)
  weight_bounded : ∃ B, ∀ y, w y ≤ B
  smooth : IsSmoothPerturbation P v

def epsIntegrand {C : Type} (m : ModeWeights C) (v f : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  (Complex.I * (m.epsW (m.classOf ι) y : ℂ) * cdot (curlOfGrad (modeGrad ι (gradField v) σ y))
    (curlOfGrad (modeGrad ι (gradField f) σ y))).re

def epsModeTerm {C : Type} (m : ModeWeights C) (v f : ℝ → Space → Space) (ι : ℤ × ℤ) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, epsIntegrand m v f ι σ y

theorem epsPairing_eq_tsum {C : Type} (m : ModeWeights C) (v f : ℝ → Space → Space) :
    epsPairing (fun ι y => m.epsW (m.classOf ι) y) v f = ∑' ι, epsModeTerm m v f ι := rfl

def negSumSecondPartialsOfField (v : ℝ → Space → Space) : ℝ → Space → Space :=
  fun σ y => -secondDerivTrace (secondDerivField v σ y)

def epsGradTerm {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  m.epsGrad ι y * vortGradAmp (secondDerivField v) ι σ y * vortAmp (gradField v) ι σ y

theorem neg_sum_five_nonpos {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    -a - b - c - d - e ≤ 0 := by linarith

theorem modeEpsRest_nonpos {C : Type} (m : ModeWeights C) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : modeEpsRest m W v G H ι σ y ≤ 0 := by
  unfold modeEpsRest ModeWeights.eps ModeWeights.epsGrad velAmp gradAmp vortAmp vortGradAmp
  exact neg_sum_five_nonpos (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

theorem modeEpsPos_nonneg {C : Type} (m : ModeWeights C) (P : ℝ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : 0 ≤ modeEpsPos m P G ι σ y := by
  unfold modeEpsPos ModeWeights.eps
  positivity

theorem epsGradTerm_nonneg {C : Type} (m : ModeWeights C) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : 0 ≤ epsGradTerm m v ι σ y := by
  unfold epsGradTerm ModeWeights.epsGrad vortGradAmp vortAmp
  positivity

end SmoothEpsInternal

end Coercive

end Breakdown
