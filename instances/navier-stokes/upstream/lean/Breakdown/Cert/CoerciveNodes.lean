import Breakdown.Cert.CoerciveStatement
import Breakdown.Cert.ExtendedCoerciveDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

def MultiplierDensityHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) {k : ℕ} (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤),
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
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityNeg P b w v G H W σ y

def PieceMultiplierDensityHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ} (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤),
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
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityNeg P h w v G H W σ y

def ModeAzimuthalGainHolds : Prop :=
  ∀ (P : ℝ) (Γ : Set Symmetry) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (ι : ℤ × ℤ) (hk : 2 ≤ |ι.2|),
    ∀ᵐ z : ℝ × Space,
      ((|ι.2| : ℝ) - 1) ^ 2 / cylRadius z.2 ^ 2 * cnormSq (modeVel ι v z.1 z.2)
          ≤ cnormSq (modeGrad ι G z.1 z.2) ∧
        ((|ι.2| : ℝ) - 2) ^ 2 / cylRadius z.2 ^ 2 * cnormSq (modeGrad ι G z.1 z.2)
          ≤ cnormSq (modeSecondDeriv ι H z.1 z.2)

def StretchMeanBoundHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (Γ : Set Symmetry) (W : ℝ → Space → Space) (hb : b.IsValid m W)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hlen : ∀ y, 0 < m.len y) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g),
    ∀ᵐ y : Space,
      ENNReal.ofReal (-∫ σ in Set.Icc (0 : ℝ) 1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          stretchForm W v G σ (axialRot φ y))
        ≤ ENNReal.ofReal (2 * Real.pi) * ∑' ι : ℤ × ℤ, ENNReal.ofReal (m.stretchCharge b v G ι 0 y)

def reVec (x : Fin 3 → ℂ) : Space := ∑ i : Fin 3, (x i).re • unitVector i

def imVec (x : Fin 3 → ℂ) : Space := ∑ i : Fin 3, (x i).im • unitVector i

def reMat (g : Fin 3 × Fin 3 → ℂ) : Space →L[ℝ] Space :=
  ∑ j : Fin 3, (innerSL ℝ (unitVector j)).smulRight (∑ i : Fin 3, (g (i, j)).re • unitVector i)

def imMat (g : Fin 3 × Fin 3 → ℂ) : Space →L[ℝ] Space :=
  ∑ j : Fin 3, (innerSL ℝ (unitVector j)).smulRight (∑ i : Fin 3, (g (i, j)).im • unitVector i)

def rotC (ψ : ℝ) (x : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => ∑ j : Fin 3, ((axialRot ψ (unitVector j) i : ℝ) : ℂ) * x j

def rotCMat (ψ : ℝ) (g : Fin 3 × Fin 3 → ℂ) : Fin 3 × Fin 3 → ℂ :=
  fun ij => ∑ a : Fin 3, ∑ c : Fin 3,
    ((axialRot ψ (unitVector a) ij.1 : ℝ) : ℂ) * g (a, c) * ((axialRot (-ψ) (unitVector ij.2) c : ℝ) : ℂ)

def smoothRight (P : ℝ) (W v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  (1 / P) • deriv (fun s => v s y) σ + (1 / 2 : ℝ) • v σ y + (1 / 2 : ℝ) • fderiv ℝ (v σ) y y
    - secondDerivTrace (secondDerivField v σ y) + fderiv ℝ (v σ) y (W σ y) + fderiv ℝ (W σ) y (v σ y)

def IsSolenoidalPartOf (F Q : ℝ → Space → Space) : Prop :=
  AEStronglyMeasurable (fun z : ℝ × Space => Q z.1 z.2) volume ∧ IsTimePeriodic Q ∧
    periodLIntegral (fun σ y => ‖Q σ y‖ ^ 2) < ⊤ ∧
    (∀ q, IsPeriodicTestPotential q →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (Q σ y) (gradientAt (q σ) y) = 0) ∧
    ∀ ψ, IsPeriodicTestField ψ →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (Q σ y) (ψ σ y) =
        ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (F σ y) (ψ σ y)

def AxialRotationHolds : Prop :=
  (∀ φ, ∃ R : Space ≃ₗᵢ[ℝ] Space, ∀ y, R y = axialRot φ y) ∧
    (∀ φ ψ y, axialRot (φ + ψ) y = axialRot φ (axialRot ψ y)) ∧
    (∀ y, axialRot 0 y = y) ∧
    (∀ φ y, axialRot (φ + 2 * Real.pi) y = axialRot φ y) ∧
    ∀ φ y, cylRadius (axialRot φ y) = cylRadius y ∧ axialRot φ y 2 = y 2

def TorusSquareSumHolds : Prop :=
  ∀ g : ℝ → ℝ → ℝ,
    AEStronglyMeasurable (fun z : ℝ × ℝ => g z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) →
    (∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (g τ φ ^ 2)) < ⊤ →
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (‖modeAverage ι (fun τ φ (_ : Unit) => g τ φ) ()‖ ^ 2) =
      ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ τ in Set.Icc (0 : ℝ) 1, ∫⁻ φ in Set.Icc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (g τ φ ^ 2)

def ModeSquareSumHolds : Prop :=
  (∀ X : ℝ → Space → Space, AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume →
      IsTimePeriodic X → periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ →
      periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) =
        ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι X σ y))) ∧
    (∀ G : ℝ → Space → (Space →L[ℝ] Space), AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume →
      IsTimePeriodic G → periodLIntegral (fun σ y => matSq (G σ y)) < ⊤ →
      periodLIntegral (fun σ y => matSq (G σ y)) =
        ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι G σ y))) ∧
    (∀ H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space),
      AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume →
      IsTimePeriodic H → periodLIntegral (fun σ y => secondDerivSq (H σ y)) < ⊤ →
      periodLIntegral (fun σ y => secondDerivSq (H σ y)) =
        ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeSecondDeriv ι H σ y))) ∧
    ∀ X Y : ℝ → Space → Space, AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume →
      AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume →
      IsTimePeriodic X → IsTimePeriodic Y →
      periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ → periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) < ⊤ →
      HasSum (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdot (modeVel ι X σ y) (modeVel ι Y σ y)).re)
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (Y σ y))

def ModeDerivativeHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → ∀ ι : ℤ × ℤ,
    (∀ᵐ σ, IsWeakGradient (fun y => reVec (modeVel ι v σ y)) (fun y => reMat (modeGrad ι G σ y)) ∧
      IsWeakGradient (fun y => imVec (modeVel ι v σ y)) (fun y => imMat (modeGrad ι G σ y))) ∧
    (∀ᵐ σ, ∀ l : Fin 3,
      IsWeakGradient (fun y => reVec (fun i => modeGrad ι G σ y (i, l)))
          (fun y => reMat (fun ij => modeSecondDeriv ι H σ y (ij.1, ij.2, l))) ∧
        IsWeakGradient (fun y => imVec (fun i => modeGrad ι G σ y (i, l)))
          (fun y => imMat (fun ij => modeSecondDeriv ι H σ y (ij.1, ij.2, l)))) ∧
    ∀ᵐ z : ℝ × Space, ∑ i : Fin 3, modeGrad ι G z.1 z.2 (i, i) = 0

def ModeRotationHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → ∀ (ι : ℤ × ℤ) (ψ : ℝ),
    (∀ᵐ z : ℝ × Space, modeVel ι v z.1 (axialRot ψ z.2) =
      fun i => Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * rotC ψ (modeVel ι v z.1 z.2) i) ∧
    ∀ᵐ z : ℝ × Space, modeGrad ι G z.1 (axialRot ψ z.2) =
      fun ij => Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * rotCMat ψ (modeGrad ι G z.1 z.2) ij

def SolenoidalModeHolds : Prop :=
  ∀ F : ℝ → Space → Space, AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume →
    IsTimePeriodic F → periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
    ∃ Q, IsSolenoidalPartOf F Q ∧ periodNorm Q ≤ periodNorm F ∧
      periodNorm (fun σ y => (2 : ℝ) • Q σ y - F σ y) = periodNorm F ∧
      (∀ Q', IsSolenoidalPartOf F Q' → ∀ᵐ z : ℝ × Space, Q' z.1 z.2 = Q z.1 z.2) ∧
      ∀ τ φ, IsSolenoidalPartOf (fun σ y => axialRot (-φ) (F (σ + τ) (axialRot φ y)))
        (fun σ y => axialRot (-φ) (Q (σ + τ) (axialRot φ y)))

def EnergyIdentityHolds : Prop :=
  ∀ (P : ℝ) (W v : ℝ → Space → Space), 0 < P → ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) →
    IsTimePeriodic W → (∀ σ y, divergenceAt (W σ) y = 0) → IsPeriodicTestField v →
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)) =
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
        + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchForm W v (gradField v) σ y)

def CurlWeightIdentityHolds : Prop :=
  ∀ (φ : Space → ℝ) (u : Space → Space), ContDiff ℝ 2 φ → ContDiff ℝ ∞ u → HasCompactSupport u →
    (∀ y, divergenceAt u y = 0) →
    ∫ y, φ y * ‖curlVec (fderiv ℝ u y)‖ ^ 2 =
      (∫ y, φ y * matSq (fderiv ℝ u y)) - ∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun x => fderiv ℝ φ x) y (unitVector i) (unitVector j) * u y i * u y j

def modeValues (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space)
    (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  f (Real.sqrt (cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)))
    (Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y))))
    (Real.sqrt (cnormSq (modeGrad ι (gradField v) σ y)))
    (Real.sqrt (cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y))))
    (Real.sqrt (cnormSq (modeVel ι v σ y)))

def IsDensityLowerBound (X : ℝ) (D : ℝ → Space → ℤ × ℤ → ℝ) : Prop :=
  (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (D σ y ι)) + ENNReal.ofReal (-X)
    ≤ ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-D σ y ι)

def epsPairing (wt : ℤ × ℤ → Space → ℝ) (v f : ℝ → Space → Space) : ℝ :=
  ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
    (Complex.I * (wt ι y : ℂ) * cdot (curlOfGrad (modeGrad ι (gradField v) σ y))
      (curlOfGrad (modeGrad ι (gradField f) σ y))).re

def muPairing (wt : ℤ × ℤ → Space → ℝ) (v Q : ℝ → Space → Space) : ℝ :=
  ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
    (Complex.I * (wt ι y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι Q σ y)).re

def vorticityEnergy (v : ℝ → Space → Space) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
    + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2)

def modeEpsDensity {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (ι : ℤ × ℤ) (y : Space)
    (xc xo x1 x0 : ℝ) : ℝ :=
  -m.shareHat ι y * xc ^ 2 + (m.coefA P b ι y - 1 / 4) * xo ^ 2
    - (Real.sqrt 2 * m.eps ι y * b.meanVort y + m.epsNb ι y * (b.wave1 y + (1 / 2) * b.waveVort y)) * x1 ^ 2
    - (1 / 2) * m.epsNb ι y * b.wave2 y / m.len2 y * x0 ^ 2
    - Real.sqrt 2 * m.eps ι y * b.meanVortGrad y * x1 * x0

def modeMuDensity {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (ι : ℤ × ℤ) (y : Space)
    (x1 x0 : ℝ) : ℝ :=
  -m.share4 y * ModeWeights.ind (0 < m.muNb ι y) * x1 ^ 2
    + (m.coefB P b ι y + ModeWeights.secondDerivNorm (m.convZ (m.classOf ι)) y
      + (1 / 2) * m.epsNb ι y * b.wave2 y / m.len2 y) * x0 ^ 2
    - (m.mu ι y * b.perpSpeed (m.classOf ι) y + m.muGrad ι y) * x1 * x0

open Classical in
def pieceEpsDensity {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (β : Fin nE) (ι : ℤ × ℤ) (y : Space) (xc xo x1 x0 : ℝ) : ℝ :=
  -((m.epsP β).share1 y * ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι)
      * ModeWeights.ind (0 < (m.epsP β).wt y + PieceWeights.wtGrad (m.epsP β).wt y)
    + (m.epsP β).share2 y * ModeWeights.ind (0 < (m.epsP β).wt y)
      * PieceWeights.outward h (m.epsP β).modes h.ampW ι y / (m.epsP β).scale y) * xc ^ 2
  + (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) *
      ((m.epsP β).wt y * |PieceWeights.frameFreq P (m.epsP β).frame ι|
        - ((m.epsP β).wt y * (m.epsP β).speed y + PieceWeights.wtGrad (m.epsP β).wt y) ^ 2
          / (4 * (m.epsP β).share1 y)
        - (m.epsP β).wt y ^ 2 * (m.epsP β).scale y * PieceWeights.inward h (m.epsP β).modes h.ampW ι y
            / (4 * (m.epsP β).share2 y)
        - (m.epsP β).wt y * (|(m.epsP β).frame| + (1 / 2) * (1 + (m.epsP β).t0 y) * h.supVort y
          + (1 / 2) * (m.epsP β).len y * h.supGradVort y
          + (1 / 2) * (m.epsP β).t1 y * PieceWeights.inward h (m.epsP β).modes h.ampGradW ι y
          + (1 / 2) * (m.epsP β).t2 y * PieceWeights.inward h (m.epsP β).modes h.ampGradVort ι y
          + (1 / 2) * (m.epsP β).t3 y * PieceWeights.inward h (m.epsP β).modes h.ampVort ι y))
    - (m.epsP β).wt y * PieceWeights.outward h (m.epsP β).modes h.ampGradW ι y / (2 * (m.epsP β).t1 y)) * xo ^ 2
  - (m.epsP β).wt y * (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * h.supVort y
      / (2 * (m.epsP β).t0 y) + PieceWeights.outward h (m.epsP β).modes h.ampVort ι y / (2 * (m.epsP β).t3 y))
    * x1 ^ 2
  - (m.epsP β).wt y * (ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * h.supGradVort y
      / (2 * (m.epsP β).len y)
      + PieceWeights.outward h (m.epsP β).modes h.ampGradVort ι y / (2 * (m.epsP β).t2 y)) * x0 ^ 2

open Classical in
def pieceMuDensity {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (β : Fin nM) (ι : ℤ × ℤ) (y : Space) (x1 x0 : ℝ) : ℝ :=
  -(ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
        * ModeWeights.ind (0 < (m.muP β).wt y + PieceWeights.wtGrad (m.muP β).wt y) * (m.muP β).share y
      + (m.muP β).wt y * PieceWeights.outward h (m.muP β).modes h.ampW ι y / (2 * (m.muP β).t4 y)) * x1 ^ 2
  + (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) *
        ((1 - m.cμ) * (m.muP β).wt y * |PieceWeights.frameFreq P (m.muP β).frame ι|
          - ((m.muP β).wt y * (m.muP β).speed y + PieceWeights.wtGrad (m.muP β).wt y) ^ 2
            / (4 * (m.muP β).share y)
          - (m.muP β).wt y * |(m.muP β).frame|
          - (1 / 2) * (m.muP β).t4 y * (m.muP β).wt y * PieceWeights.inward h (m.muP β).modes h.ampW ι y
          - (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2
          - PieceWeights.harmonicSum h y * (PieceWeights.harmonicSum h y
              - PieceWeights.inward h (m.muP β).modes h.ampGradW ι y) / (2 * (m.muP β).eta))
      - PieceWeights.harmonicSum h y * PieceWeights.outward h (m.muP β).modes h.ampGradW ι y
          / (2 * (m.muP β).eta)) * x0 ^ 2

def pieceSeminormPart {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (β : Fin nM)
    (v : ℝ → Space → Space) : ℝ≥0∞ :=
  ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
    ENNReal.ofReal (|PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
      * (m.muP β).wt y * cnormSq (modeVel ι v σ y))

def modeEpsPos {C : Type} (m : ModeWeights C) (P : ℝ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  m.eps ι y * |m.dop P ι y| * vortAmp G ι σ y ^ 2

def modeEpsRest {C : Type} (m : ModeWeights C) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  -((m.eps ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.epsGrad ι y)
      * vortGradAmp H ι σ y * vortAmp G ι σ y)
    - m.eps ι y * ((1 / 2) * ‖curlVec (fderiv ℝ (meanField W) y)‖ + |m.rate (m.classOf ι) y|)
      * vortAmp G ι σ y ^ 2
    - m.eps ι y * ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖ * velAmp v ι σ y
      * vortAmp G ι σ y
    - m.eps ι y * ‖curlVec (fderiv ℝ (meanField W) y)‖ * gradAmp G ι σ y * vortAmp G ι σ y
    - m.eps ι y * vortAmp G ι σ y * ∑ α ∈ m.waves,
      (velAmp W α σ y * vortGradAmp H (ι - α) σ y + gradAmp (gradField W) α σ y * vortAmp G (ι - α) σ y
        + vortGradAmp (secondDerivField W) α σ y * velAmp v (ι - α) σ y
        + vortAmp (gradField W) α σ y * gradAmp G (ι - α) σ y)

def modeMuPos {C : Type} (m : ModeWeights C) (P : ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : ℝ :=
  (1 - m.cμ) * m.mu ι y * |m.dop P ι y| * velAmp v ι σ y ^ 2

def modeMuRest {C : Type} (m : ModeWeights C) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  -((m.mu ι y * ‖relativeVelocity W (m.rate (m.classOf ι)) y‖ + m.muGrad ι y)
      * gradAmp G ι σ y * velAmp v ι σ y)
    - m.mu ι y * |m.rate (m.classOf ι) y| * velAmp v ι σ y ^ 2
    - m.mu ι y * velAmp v ι σ y * ∑ α ∈ m.waves, velAmp W α σ y * gradAmp G (ι - α) σ y
    - ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0)
      * ((‖fderiv ℝ (meanField W) y‖ ^ 2 * velAmp v ι σ y ^ 2
          + (∑ α ∈ m.waves, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2) / m.eta (m.classOf ι)
        + (1 / 2) * m.eta (m.classOf ι) * m.mu ι y ^ 2 * velAmp v ι σ y ^ 2)

def modePos {C : Type} (m : ModeWeights C) (P : ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  modeEpsPos m P G ι σ y + modeMuPos m P v ι σ y

def modeRest {C : Type} (m : ModeWeights C) (w : Space → ℝ) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)
    + modeEpsRest m W v G H ι σ y + modeMuRest m W v G ι σ y

def BaseDensityHolds : Prop :=
  ∀ {C : Type} (cl : ℤ × ℤ → C) (convD convZ : C → Space → ℝ) (c : ℝ) (w : Space → ℝ) (w₀ : ℝ),
    Finite C → 0 < w₀ → (∀ y, w₀ ≤ w y) → (∃ B, ∀ y, w y ≤ B) → Measurable w → IsAxisymmetric w →
    (∀ d, ContDiff ℝ 2 (convD d)) → (∀ d, ContDiff ℝ 2 (convZ d)) →
    (∀ d, IsAxisymmetric (convD d)) → (∀ d, IsAxisymmetric (convZ d)) →
    (∃ B, ∀ d y, ∀ j ≤ 2, ‖y‖ ^ j * ‖iteratedFDeriv ℝ j (convD d) y‖ ≤ B) →
    (∃ B, ∀ d y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j (convZ d) y‖ ≤ B) →
    ∀ v, IsPeriodicTestField v →
      IsDensityLowerBound (vorticityEnergy v - c * weightedEnergy w (gradField v) (secondDerivField v))
        (fun σ y ι => modeValues v ι σ y (baseDensity convD convZ (cl ι) c w y))

def ModePairingSplitHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (W : ℝ → Space → Space)
    {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsPeriodicTestField v → ∀ M Q, m.IsMultiplierField v (gradField v) (secondDerivField v) M →
      IsSolenoidalPartOf (smoothRight P W v) Q →
      periodPairing (smoothRight P W v) M =
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)))
          + epsPairing (fun ι y => m.epsW (m.classOf ι) y) v (smoothRight P W v)
          + muPairing (fun ι y => m.muW (m.classOf ι) y) v Q

def ModeEpsEstimateHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (W : ℝ → Space → Space)
    {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsPeriodicTestField v →
      IsSplitLowerBound (epsPairing (fun ι y => m.epsW (m.classOf ι) y) v (smoothRight P W v))
        (fun σ y ι => modeEpsPos m P (gradField v) ι σ y)
        (fun σ y ι => modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y) (fun _ _ => 0) (fun _ _ => 0)

def ModeMuEstimateHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (W : ℝ → Space → Space)
    {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsPeriodicTestField v → ∀ Q, IsSolenoidalPartOf (smoothRight P W v) Q →
      IsSplitLowerBound (muPairing (fun ι y => m.muW (m.classOf ι) y) v Q
          - m.cμ * (m.frequencySeminormSq P v).toReal)
        (fun σ y ι => modeMuPos m P v ι σ y)
        (fun σ y ι => modeMuRest m W v (gradField v) ι σ y) (fun _ _ => 0) (fun _ _ => 0)

def PiecePairingSplitHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsPeriodicTestField v → ∀ M Q, m.IsMultiplierField v (gradField v) (secondDerivField v) M →
      IsSolenoidalPartOf (smoothRight P W v) Q →
      periodPairing (smoothRight P W v) M =
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)))
          + ∑ β : Fin nE, epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v
              (smoothRight P W v)
          + ∑ β : Fin nM, muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Q

def PieceEpsEstimateHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsPeriodicTestField v → ∀ β : Fin nE,
      IsSplitLowerBound
        (epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v (smoothRight P W v))
        (fun σ y ι => pieceEpsPos m P (gradField v) β ι σ y)
        (fun σ y ι => pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y)
        (fun σ y => pieceEpsBlock m W v (gradField v) (secondDerivField v) β σ y) (fun _ _ => 0)

def PieceMuEstimateHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsPeriodicTestField v → ∀ Q, IsSolenoidalPartOf (smoothRight P W v) Q → ∀ β : Fin nM,
      IsSplitLowerBound
        (muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Q
          - m.cμ * (pieceSeminormPart m P β v).toReal)
        (fun σ y ι => pieceMuPos m P v β ι σ y)
        (fun σ y ι => pieceMuRestMode m h W v (gradField v) β ι σ y)
        (fun σ y => pieceMuBlock m W v (gradField v) β σ y) (fun _ _ => 0)

def ModeFieldExistsHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (Γ : Set Symmetry)
    {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → (∃ B, ∀ y, w y ≤ B) →
    ∀ v G H g, IsPerturbation Γ P v G H g →
      m.frequencySeminormSq P v < ⊤ ∧ ∃ M, m.IsMultiplierField v G H M ∧
        periodNorm M ≤ m.multiplierConstant w₀ epsSup epsGradSup ratio
          * Real.sqrt (m.c * weightedEnergy w G H + m.cμ * (m.frequencySeminormSq P v).toReal)

def SmoothModeDensityHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) {k : ℕ}
    (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (act i)) →
    (∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) →
    ∀ v, IsPeriodicTestField v → ∀ (κ : Fin k → ℝ) M,
      m.IsMultiplierField v (gradField v) (secondDerivField v) M →
      IsSplitLowerBound (m.multiplierGap P w act v (gradField v) (secondDerivField v) κ (fun σ y => smoothRight P W v σ y + ∑ i, κ i • act i σ y) M)
        (fun σ y ι => modePos m P v (gradField v) ι σ y)
        (fun σ y ι => modeRest m w W v (gradField v) (secondDerivField v) ι σ y) (fun _ _ => 0)
        (stretchForm W v (gradField v))

def ModeDensityOfFieldHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) {k : ℕ} (Γ : Set Symmetry)
    (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (act i)) →
    (∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) →
    ∀ v G H g, IsPerturbation Γ P v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide W act κ v G g F →
      ∀ M, m.IsMultiplierField v G H M →
      IsSplitLowerBound (m.multiplierGap P w act v G H κ F M)
        (fun σ y ι => modePos m P v G ι σ y) (fun σ y ι => modeRest m w W v G H ι σ y) (fun _ _ => 0)
        (stretchForm W v G)

def PieceFieldExistsHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio → (∃ B, ∀ y, w y ≤ B) →
    ∀ v G H g, IsPerturbation Γ P v G H g →
      m.seminormSq P v < ⊤ ∧ ∃ M, m.IsMultiplierField v G H M ∧
        periodNorm M ≤ Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt w₀) ^ 2 / m.c + ratio / m.cμ)
          * Real.sqrt (m.c * weightedEnergy w G H + m.cμ * (m.seminormSq P v).toReal)

def SmoothPieceDensityHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (act i)) →
    (∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) →
    ∀ v, IsPeriodicTestField v → ∀ (κ : Fin k → ℝ) M,
      m.IsMultiplierField v (gradField v) (secondDerivField v) M →
      IsSplitLowerBound (m.multiplierGap P w act v (gradField v) (secondDerivField v) κ (fun σ y => smoothRight P W v σ y + ∑ i, κ i • act i σ y) M)
        (fun σ y ι => piecePos m P v (gradField v) ι σ y)
        (fun σ y ι => pieceRest m h w W v (gradField v) (secondDerivField v) ι σ y)
        (fun σ y => pieceBlock m W v (gradField v) (secondDerivField v) σ y) (stretchForm W v (gradField v))

def PieceDensityOfFieldHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ} (Γ : Set Symmetry)
    (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (act i)) →
    (∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) →
    ∀ v G H g, IsPerturbation Γ P v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide W act κ v G g F →
      ∀ M, m.IsMultiplierField v G H M →
      IsSplitLowerBound (m.multiplierGap P w act v G H κ F M)
        (fun σ y ι => piecePos m P v G ι σ y) (fun σ y ι => pieceRest m h w W v G H ι σ y)
        (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G)

def ModeAbsorbStepHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (Γ : Set Symmetry)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v G H g, IsPerturbation Γ P v G H g → ∀ X : ℝ,
      IsSplitLowerBound X (fun σ y ι => modePos m P v G ι σ y) (fun σ y ι => modeRest m w W v G H ι σ y)
        (fun _ _ => 0) (stretchForm W v G) →
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityPos P b w v G H W σ y) + ENNReal.ofReal (-X)
        ≤ ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityNeg P b w v G H W σ y

def PieceAbsorbStepHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v G H g, IsPerturbation Γ P v G H g → ∀ X : ℝ,
      IsSplitLowerBound X (fun σ y ι => piecePos m P v G ι σ y) (fun σ y ι => pieceRest m h w W v G H ι σ y)
        (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G) →
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityPos P h w v G H W σ y) + ENNReal.ofReal (-X)
        ≤ ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, m.densityNeg P h w v G H W σ y

def SmoothPerturbationIsPerturbationHolds : Prop :=
  ∀ (P : ℝ) (v : ℝ → Space → Space), IsSmoothPerturbation P v →
    IsPerturbation ∅ P v (gradField v) (secondDerivField v) (transportPart P v)

def EnergyIdentitySmoothHolds : Prop :=
  ∀ (P : ℝ) (W v : ℝ → Space → Space), 0 < P → ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) →
    IsTimePeriodic W → (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    IsSmoothPerturbation P v →
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)) =
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
        + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchForm W v (gradField v) σ y)

def CurlWeightIdentityDecayHolds : Prop :=
  ∀ (φ : Space → ℝ) (u : Space → Space), ContDiff ℝ 2 φ →
    (∃ B, ∀ y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j φ y‖ ≤ B) →
    ContDiff ℝ 2 u → (∀ y, divergenceAt u y = 0) →
    (∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ u y))) < ⊤ →
    (∫⁻ y, ENNReal.ofReal (‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2)) < ⊤ →
    ∫ y, φ y * ‖curlVec (fderiv ℝ u y)‖ ^ 2 =
      (∫ y, φ y * matSq (fderiv ℝ u y)) - ∫ y, ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun x => fderiv ℝ φ x) y (unitVector i) (unitVector j) * u y i * u y j

def WeightedSumSecondPartialsPairingHolds : Prop :=
  ∀ (a : Space → ℝ) (K : NNReal) (p q : Space → Space), LipschitzWith K a → ContDiff ℝ 2 p → ContDiff ℝ 2 q →
    Integrable (fun y => a y * (inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ p x) y)) (q y)
      - inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ q x) y)) (p y))) →
    Integrable (fun y => ‖fderiv ℝ a y‖ * (‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖)) →
    Integrable (fun y => |a y| * (‖fderiv ℝ p y‖ * ‖q y‖ + ‖fderiv ℝ q y‖ * ‖p y‖) / (1 + ‖y‖)) →
    ∫ y, a y * (inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ p x) y)) (q y)
      - inner ℝ (secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ q x) y)) (p y)) =
      -∫ y, ∑ l : Fin 3, fderiv ℝ a y (unitVector l)
        * (inner ℝ (fderiv ℝ p y (unitVector l)) (q y) - inner ℝ (fderiv ℝ q y (unitVector l)) (p y))

def BaseDensitySmoothHolds : Prop :=
  ∀ {C : Type} (P : ℝ) (cl : ℤ × ℤ → C) (convD convZ : C → Space → ℝ) (c : ℝ) (w : Space → ℝ) (w₀ : ℝ),
    Finite C → 0 < w₀ → (∀ y, w₀ ≤ w y) → (∃ B, ∀ y, w y ≤ B) → Measurable w → IsAxisymmetric w →
    (∀ d, ContDiff ℝ 2 (convD d)) → (∀ d, ContDiff ℝ 2 (convZ d)) →
    (∀ d, IsAxisymmetric (convD d)) → (∀ d, IsAxisymmetric (convZ d)) →
    (∃ B, ∀ d y, ∀ j ≤ 2, ‖y‖ ^ j * ‖iteratedFDeriv ℝ j (convD d) y‖ ≤ B) →
    (∃ B, ∀ d y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j (convZ d) y‖ ≤ B) →
    ∀ v, IsSmoothPerturbation P v →
      IsDensityLowerBound (vorticityEnergy v - c * weightedEnergy w (gradField v) (secondDerivField v))
        (fun σ y ι => modeValues v ι σ y (baseDensity convD convZ (cl ι) c w y))

def ModePairingSplitSmoothHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (W : ℝ → Space → Space)
    {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsSmoothPerturbation P v → ∀ M Q, m.IsMultiplierField v (gradField v) (secondDerivField v) M →
      IsSolenoidalPartOf (smoothRight P W v) Q →
      periodPairing (smoothRight P W v) M =
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)))
          + epsPairing (fun ι y => m.epsW (m.classOf ι) y) v (smoothRight P W v)
          + muPairing (fun ι y => m.muW (m.classOf ι) y) v Q

def ModeEpsEstimateSmoothHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (W : ℝ → Space → Space)
    {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsSmoothPerturbation P v →
      IsSplitLowerBound (epsPairing (fun ι y => m.epsW (m.classOf ι) y) v (smoothRight P W v))
        (fun σ y ι => modeEpsPos m P (gradField v) ι σ y)
        (fun σ y ι => modeEpsRest m W v (gradField v) (secondDerivField v) ι σ y) (fun _ _ => 0) (fun _ _ => 0)

def ModeMuEstimateSmoothHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) (W : ℝ → Space → Space)
    {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsSmoothPerturbation P v → ∀ Q, IsSolenoidalPartOf (smoothRight P W v) Q →
      IsSplitLowerBound (muPairing (fun ι y => m.muW (m.classOf ι) y) v Q
          - m.cμ * (m.frequencySeminormSq P v).toReal)
        (fun σ y ι => modeMuPos m P v ι σ y)
        (fun σ y ι => modeMuRest m W v (gradField v) ι σ y) (fun _ _ => 0) (fun _ _ => 0)

def PiecePairingSplitSmoothHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsSmoothPerturbation P v → ∀ M Q, m.IsMultiplierField v (gradField v) (secondDerivField v) M →
      IsSolenoidalPartOf (smoothRight P W v) Q →
      periodPairing (smoothRight P W v) M =
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)))
          + ∑ β : Fin nE, epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v
              (smoothRight P W v)
          + ∑ β : Fin nM, muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Q

def PieceEpsEstimateSmoothHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsSmoothPerturbation P v → ∀ β : Fin nE,
      IsSplitLowerBound
        (epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v (smoothRight P W v))
        (fun σ y ι => pieceEpsPos m P (gradField v) β ι σ y)
        (fun σ y ι => pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y)
        (fun σ y => pieceEpsBlock m W v (gradField v) (secondDerivField v) β σ y) (fun _ _ => 0)

def PieceMuEstimateSmoothHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, IsSmoothPerturbation P v → ∀ Q, IsSolenoidalPartOf (smoothRight P W v) Q → ∀ β : Fin nM,
      IsSplitLowerBound
        (muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Q
          - m.cμ * (pieceSeminormPart m P β v).toReal)
        (fun σ y ι => pieceMuPos m P v β ι σ y)
        (fun σ y ι => pieceMuRestMode m h W v (gradField v) β ι σ y)
        (fun σ y => pieceMuBlock m W v (gradField v) β σ y) (fun _ _ => 0)

def ModeDensitySmoothHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) {k : ℕ}
    (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (act i)) →
    (∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) →
    ∀ v, IsSmoothPerturbation P v → ∀ (κ : Fin k → ℝ) M,
      m.IsMultiplierField v (gradField v) (secondDerivField v) M →
      IsSplitLowerBound (m.multiplierGap P w act v (gradField v) (secondDerivField v) κ (fun σ y => smoothRight P W v σ y + ∑ i, κ i • act i σ y) M)
        (fun σ y ι => modePos m P v (gradField v) ι σ y)
        (fun σ y ι => modeRest m w W v (gradField v) (secondDerivField v) ι σ y) (fun _ _ => 0)
        (stretchForm W v (gradField v))

def PieceDensitySmoothHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (act i)) →
    (∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) →
    ∀ v, IsSmoothPerturbation P v → ∀ (κ : Fin k → ℝ) M,
      m.IsMultiplierField v (gradField v) (secondDerivField v) M →
      IsSplitLowerBound (m.multiplierGap P w act v (gradField v) (secondDerivField v) κ (fun σ y => smoothRight P W v σ y + ∑ i, κ i • act i σ y) M)
        (fun σ y ι => piecePos m P v (gradField v) ι σ y)
        (fun σ y ι => pieceRest m h w W v (gradField v) (secondDerivField v) ι σ y)
        (fun σ y => pieceBlock m W v (gradField v) (secondDerivField v) σ y) (stretchForm W v (gradField v))

def ModeDensityPassageHolds : Prop :=
  ∀ {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ) {k : ℕ} (Γ : Set Symmetry)
    (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P b w w₀ epsSup epsGradSup ratio → b.IsValid m W →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (act i)) →
    (∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) →
    ∀ v G H g, IsPerturbation Γ P v G H g →
    ∀ u : ℕ → ℝ → Space → Space, IsSmoothApproximation P v G H g u →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide W act κ v G g F →
      ∀ M, m.IsMultiplierField v G H M →
      IsSplitLowerBound (m.multiplierGap P w act v G H κ F M)
        (fun σ y ι => modePos m P v G ι σ y) (fun σ y ι => modeRest m w W v G H ι σ y) (fun _ _ => 0)
        (stretchForm W v G)

def PieceDensityPassageHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ} (Γ : Set Symmetry)
    (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio →
    ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2) → IsTimePeriodic W →
    (∀ σ y, divergenceAt (W σ) y = 0) →
    (∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1)) →
    (∃ B, ∀ y, w y ≤ B) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (act i)) →
    (∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) →
    ∀ v G H g, IsPerturbation Γ P v G H g →
    ∀ u : ℕ → ℝ → Space → Space, IsSmoothApproximation P v G H g u →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide W act κ v G g F →
      ∀ M, m.IsMultiplierField v G H M →
      IsSplitLowerBound (m.multiplierGap P w act v G H κ F M)
        (fun σ y ι => piecePos m P v G ι σ y) (fun σ y ι => pieceRest m h w W v G H ι σ y)
        (fun σ y => pieceBlock m W v G H σ y) (stretchForm W v G)

end Coercive

end Breakdown
