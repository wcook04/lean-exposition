import Breakdown.Cert.ExtendedStatement

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

def secondDerivSq (H : Space →L[ℝ] Space →L[ℝ] Space) : ℝ :=
  ∑ j : Fin 3, ∑ l : Fin 3, ‖H (unitVector j) (unitVector l)‖ ^ 2

def baseDensity {C : Type} (convD convZ : C → Space → ℝ) (cl : C) (c : ℝ) (w : Space → ℝ) (y : Space)
    (x2 xc x1 xo x0 : ℝ) : ℝ :=
  (convD cl y - c) * x2 ^ 2 + (1 - convD cl y) * xc ^ 2 + (1 / 4 - convZ cl y) * xo ^ 2
    + (convZ cl y - ModeWeights.secondDerivNorm (convD cl) y - c * w y) * x1 ^ 2
    - ModeWeights.secondDerivNorm (convZ cl) y * x0 ^ 2

def velAmp (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  Real.sqrt (cnormSq (modeVel ι v σ y))

def gradAmp (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  Real.sqrt (cnormSq (modeGrad ι G σ y))

def vortAmp (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G σ y)))

def secondDerivAmp (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  Real.sqrt (cnormSq (modeSecondDeriv ι H σ y))

def vortGradAmp (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι H σ y)))

def modeVals (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space)
    (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ :=
  f (secondDerivAmp H ι σ y) (vortGradAmp H ι σ y) (gradAmp G ι σ y) (vortAmp G ι σ y) (velAmp v ι σ y)

def IsSplitLowerBound (X : ℝ) (Pos Rest : ℝ → Space → ℤ × ℤ → ℝ) (Blk J : ℝ → Space → ℝ) : Prop :=
  (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y))) < ⊤ ∧
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ((∑' ι : ℤ × ℤ, ENNReal.ofReal (Pos σ y ι))
        + (∑' ι : ℤ × ℤ, ENNReal.ofReal (Rest σ y ι)) + ENNReal.ofReal (Blk σ y) + ENNReal.ofReal (J σ y)))
        + ENNReal.ofReal (-X)
      ≤ ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y) + ENNReal.ofReal (-J σ y))

open Classical in
def edgeSum (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X g : ℤ × ℤ → ℝ) (ι : ℤ × ℤ) : ℝ :=
  if ι ∈ T then ∑ β ∈ h.harmonics, (if ι - β ∈ T then 0 else X β * g (ι - β))
  else if -ι ∈ T then ∑ β ∈ h.harmonics, (if -ι - β ∈ T then 0 else X β * g (ι + β)) else 0

def pieceNorm (T : Set (ℤ × ℤ)) (g : ℤ × ℤ → ℝ) : ℝ :=
  Real.sqrt (∑' κ : ℤ × ℤ, ModeWeights.ind (PieceWeights.inPiece T κ) * g κ ^ 2)

def frameSpeedSup (W : ℝ → Space → Space) (a : ℝ) (y : Space) : ℝ :=
  ⨆ p : ℝ × ℝ, ‖W p.1 (axialRot p.2 y) + (1 / 2 : ℝ) • axialRot p.2 y
    - a • (-(axialRot p.2 y 1) • unitVector 0 + axialRot p.2 y 0 • unitVector 1)‖

def vortSup (W : ℝ → Space → Space) (y : Space) : ℝ :=
  ⨆ p : ℝ × ℝ, ‖curlVec (fderiv ℝ (W p.1) (axialRot p.2 y))‖

def vortGradSup (W : ℝ → Space → Space) (y : Space) : ℝ :=
  ⨆ p : ℝ × ℝ, ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (W p.1) x)) (axialRot p.2 y)‖

open Classical in
def pieceEpsPos {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (β : Fin nE) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * (m.epsP β).wt y
    * |PieceWeights.frameFreq P (m.epsP β).frame ι| * vortAmp G ι σ y ^ 2

def pieceEpsRestMode {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (β : Fin nE) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  -((m.epsP β).wt y * vortAmp G ι σ y
    * (edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) (fun κ => vortGradAmp H κ σ y) ι
      + edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) (fun κ => vortAmp G κ σ y) ι
      + edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y) (fun κ => velAmp v κ σ y) ι
      + edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) (fun κ => gradAmp G κ σ y) ι))

def pieceEpsBlock {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (β : Fin nE) (σ : ℝ) (y : Space) : ℝ :=
  -(((m.epsP β).wt y * frameSpeedSup W (m.epsP β).frame y + PieceWeights.wtGrad (m.epsP β).wt y)
      * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y))
    - (m.epsP β).wt y * ((1 / 2) * vortSup W y + |(m.epsP β).frame|)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) ^ 2
    - (m.epsP β).wt y * vortGradSup W y * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y)
    - (m.epsP β).wt y * vortSup W y * pieceNorm (m.epsP β).modes (fun κ => gradAmp G κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y)

open Classical in
def pieceMuPos {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (v : ℝ → Space → Space)
    (β : Fin nM) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (1 - m.cμ) * (m.muP β).wt y
    * |PieceWeights.frameFreq P (m.muP β).frame ι| * velAmp v ι σ y ^ 2

open Classical in
def pieceMuRestMode {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (β : Fin nM) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : ℝ :=
  -((m.muP β).wt y * velAmp v ι σ y
      * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι)
    - ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * ((∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2 / (2 * (m.muP β).eta)
        + (1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2 * velAmp v ι σ y ^ 2)

def pieceMuBlock {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (β : Fin nM) (σ : ℝ) (y : Space) : ℝ :=
  -(((m.muP β).wt y * frameSpeedSup W (m.muP β).frame y + PieceWeights.wtGrad (m.muP β).wt y)
      * pieceNorm (m.muP β).modes (fun κ => gradAmp G κ σ y)
      * pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y))
    - (m.muP β).wt y * |(m.muP β).frame| * pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y) ^ 2

def piecePos {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  ∑ β : Fin nE, pieceEpsPos m P G β ι σ y + ∑ β : Fin nM, pieceMuPos m P v β ι σ y

def pieceRest {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds) (w : Space → ℝ)
    (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y)
    + ∑ β : Fin nE, pieceEpsRestMode m h W v G H β ι σ y + ∑ β : Fin nM, pieceMuRestMode m h W v G β ι σ y

def pieceBlock {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (σ : ℝ) (y : Space) : ℝ :=
  ∑ β : Fin nE, pieceEpsBlock m W v G H β σ y + ∑ β : Fin nM, pieceMuBlock m W v G β σ y

def transportPart (P : ℝ) (v : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  (1 / P) • deriv (fun s => v s y) σ + (1 / 2 : ℝ) • v σ y + (1 / 2 : ℝ) • fderiv ℝ (v σ) y y

structure IsSmoothPerturbation (P : ℝ) (v : ℝ → Space → Space) : Prop where
  smooth : ContDiff ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)
  periodic : IsTimePeriodic v
  divergence_free : ∀ σ y, divergenceAt (v σ) y = 0
  sixth_power : ∀ σ, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6) < ⊤
  weighted_finite : periodLIntegral (fun σ y => ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤
  derivatives_finite : ∀ j : ℕ, 1 ≤ j →
    periodLIntegral (fun σ y => ‖iteratedFDeriv ℝ j (v σ) y‖ ^ 2) < ⊤
  time_weighted_finite :
    periodLIntegral (fun σ y => ‖deriv (fun s => v s y) σ‖ ^ 2 / (1 + ‖y‖) ^ 2) < ⊤
  time_derivatives_finite : ∀ j : ℕ, 1 ≤ j →
    periodLIntegral (fun σ y => ‖iteratedFDeriv ℝ j (fun x => deriv (fun s => v s x) σ) y‖ ^ 2) < ⊤
  transport_finite : ∀ j : ℕ,
    periodLIntegral (fun σ y => ‖iteratedFDeriv ℝ j (transportPart P v σ) y‖ ^ 2) < ⊤

def IsSmoothApproximation (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space)
    (u : ℕ → ℝ → Space → Space) : Prop :=
  (∀ n, IsSmoothPerturbation P (u n)) ∧
    Filter.Tendsto (fun n => periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y)))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => periodLIntegral (fun σ y => secondDerivSq (secondDerivField (u n) σ y - H σ y)))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖u n σ y - v σ y‖ ^ 2 / (1 + ‖y‖) ^ 2))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖transportPart P (u n) σ y - g σ y‖ ^ 2))
      Filter.atTop (nhds 0)

def SmoothApproximationHolds : Prop :=
  ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g →
    ∃ u : ℕ → ℝ → Space → Space, IsSmoothApproximation P v G H g u

end Coercive

namespace CoerciveWeak

open PieceWeights

structure IsWeakSecondDerivState (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) : Prop where
  smooth : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)
  periodic : IsTimePeriodic W
  divergence_free : ∀ σ y, divergenceAt (W σ) y = 0
  secondDeriv_measurable : AEStronglyMeasurable (fun z : ℝ × Space => HW z.1 z.2) volume
  secondDeriv_periodic : IsTimePeriodic HW
  secondDeriv_weak : ∀ σ, ∀ j : Fin 3,
    IsWeakGradient (fun y => fderiv ℝ (W σ) y (unitVector j)) (fun y => (HW σ y).flip (unitVector j))
  decay : ∀ σ y, ‖W σ y‖ ≤ D / (1 + ‖y‖) ∧ ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2 ∧
    ‖HW σ y‖ ≤ D / (1 + ‖y‖) ^ 3

theorem isWeakSecondDerivState_of_profile {k : ℕ} (d : ExtendedCertificateData k)
    (hsmooth : ContDiff ℝ 1 (fun z : (Fin k → ℝ) × ℝ × Space => d.profile z.1 z.2.1 z.2.2))
    (hper : ∀ q, IsTimePeriodic (d.profile q))
    (hdiv : ∀ q ∈ d.params, ∀ σ y, divergenceAt (d.profile q σ) y = 0)
    (hdecay : ∀ q ∈ d.params, ∀ σ y, ‖d.profile q σ y‖ ≤ d.decay / (1 + ‖y‖) ∧
      ‖fderiv ℝ (d.profile q σ) y‖ ≤ d.decay / (1 + ‖y‖) ^ 2 ∧
      ‖d.profileSecondDeriv q σ y‖ ≤ d.decay / (1 + ‖y‖) ^ 3)
    (hmeas : ∀ q ∈ d.params,
      AEStronglyMeasurable (fun z : ℝ × Space => d.profileSecondDeriv q z.1 z.2) volume)
    (hhper : ∀ q ∈ d.params, IsTimePeriodic (d.profileSecondDeriv q))
    (hweak : ∀ q ∈ d.params, ∀ σ, ∀ j : Fin 3,
      IsWeakGradient (fun y => fderiv ℝ (d.profile q σ) y (unitVector j))
        (fun y => (d.profileSecondDeriv q σ y).flip (unitVector j)))
    (q : Fin k → ℝ) (hq : q ∈ d.params) :
    IsWeakSecondDerivState (d.profile q) (d.profileSecondDeriv q) d.decay :=
  { smooth := hsmooth.comp (contDiff_const.prodMk contDiff_id)
    periodic := hper q
    divergence_free := hdiv q hq
    secondDeriv_measurable := hmeas q hq
    secondDeriv_periodic := hhper q hq
    secondDeriv_weak := hweak q hq
    decay := hdecay q hq }

def vortGradMap (A : Space →L[ℝ] Space →L[ℝ] Space) : Space →L[ℝ] Space :=
  ∑ m : Fin 3, (innerSL ℝ (unitVector m)).smulRight (∑ j : Fin 3, vortGrad A j m • unitVector j)

def stretchFormWith (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : ℝ :=
  -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (G σ y) i
      * ((fderiv ℝ (W σ) y (unitVector j) i + fderiv ℝ (W σ) y (unitVector i) j) / 2) * curlVec (G σ y) j)
    + ∑ j : Fin 3, (∑ m : Fin 3, v σ y m * vortGrad (HW σ y) j m) * curlVec (G σ y) j
    + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (HW σ y) j m * G σ y (unitVector j) i * v σ y l

theorem stretchFormWith_secondDerivField (W : ℝ → Space → Space) :
    stretchFormWith W (secondDerivField W) = stretchForm W := rfl

def densityPosWith {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ENNReal.ofReal (m.modeTerm P h w v G H ι σ y))
    + ENNReal.ofReal (stretchFormWith W HW v G σ y)

def densityNegWith {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ENNReal.ofReal (-m.modeTerm P h w v G H ι σ y))
    + ENNReal.ofReal (-stretchFormWith W HW v G σ y)

theorem densityPosWith_secondDerivField {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ)
    (h : HarmonicBounds) (w : Space → ℝ) (W : ℝ → Space → Space) :
    ∀ v G H σ y, densityPosWith m P h w v G H W (secondDerivField W) σ y = m.densityPos P h w v G H W σ y :=
  fun _ _ _ _ _ => rfl

theorem densityNegWith_secondDerivField {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ)
    (h : HarmonicBounds) (w : Space → ℝ) (W : ℝ → Space → Space) :
    ∀ v G H σ y, densityNegWith m P h w v G H W (secondDerivField W) σ y = m.densityNeg P h w v G H W σ y :=
  fun _ _ _ _ _ => rfl

structure IsAdmissibleWeak {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (w₀ epsSup epsGradSup ratio : ℝ) : Prop where
  finite_classes : Finite C
  c_pos : 0 < m.c
  c_lt_one : m.c < 1
  cμ_pos : 0 < m.cμ
  cμ_lt_one : m.cμ < 1
  period_pos : 0 < P
  weight_pos : 0 < w₀
  weight_lower : ∀ y, w₀ ≤ w y
  weight_measurable : Measurable w
  weight_axi : IsAxisymmetric w
  harmonics_neg : ∀ β ∈ h.harmonics, -β ∈ h.harmonics
  harmonics_zero : (0, 0) ∈ h.harmonics
  harmonics_span : ∀ σ y i, W σ y i = ∑ β ∈ h.harmonics, (modeVel β W σ y i).re
  ampW_ge : ∀ β ∈ h.harmonics, ∀ σ y, Real.sqrt (cnormSq (modeVel β W σ y)) ≤ h.ampW β y
  ampGradW_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (modeGrad β (gradField W) σ y)) ≤ h.ampGradW β y
  ampVort_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (curlOfGrad (modeGrad β (gradField W) σ y))) ≤ h.ampVort β y
  ampGradVort_ge : ∀ β ∈ h.harmonics, ∀ σ y,
    Real.sqrt (cnormSq (curlGradOfSecondDeriv (modeSecondDeriv β HW σ y))) ≤ h.ampGradVort β y
  supVort_ge : ∀ σ φ y, ‖curlVec (fderiv ℝ (W σ) (axialRot φ y))‖ ≤ h.supVort y
  supGradVort_ge : ∀ σ φ y,
    ‖vortGradMap (HW σ (axialRot φ y))‖ ≤ h.supGradVort y
  epsSpeed_ge : ∀ β σ φ y, ‖W σ (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y
    - (m.epsP β).frame • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖
      ≤ (m.epsP β).speed y
  muSpeed_ge : ∀ β σ φ y, ‖W σ (axialRot φ y) + (1 / 2 : ℝ) • axialRot φ y
    - (m.muP β).frame • (-(axialRot φ y 1) • unitVector 0 + axialRot φ y 0 • unitVector 1)‖
      ≤ (m.muP β).speed y
  eps_oneSided : ∀ β, ∃ Ωs > 0, ∀ ι ∈ (m.epsP β).modes, Ωs ≤ frameFreq P (m.epsP β).frame ι
  mu_oneSided : ∀ β, ∃ Ωs > 0, ∀ ι ∈ (m.muP β).modes, Ωs ≤ frameFreq P (m.muP β).frame ι
  mu_ratio : ∀ y ι, (∑ β : Fin nM, |sgn (m.muP β).modes ι| * (m.muP β).wt y) ^ 2
    ≤ ratio * ∑ β : Fin nM, |sgn (m.muP β).modes ι| * |frameFreq P (m.muP β).frame ι| * (m.muP β).wt y
  ratio_nonneg : 0 ≤ ratio
  eps_wt_nonneg : ∀ β y, 0 ≤ (m.epsP β).wt y
  mu_wt_nonneg : ∀ β y, 0 ≤ (m.muP β).wt y
  eps_increment : ∀ β, ∃ K, LipschitzWith K (m.epsP β).wt
  mu_increment : ∀ β, ∃ K, LipschitzWith K (m.muP β).wt
  eps_axi : ∀ β, IsAxisymmetric (m.epsP β).wt
  mu_axi : ∀ β, IsAxisymmetric (m.muP β).wt
  eps_sum_le : ∀ y, ∑ β : Fin nE, (m.epsP β).wt y ≤ epsSup
  eps_grad_sum_le : ∀ y, ∑ β : Fin nE, wtGrad (m.epsP β).wt y ≤ epsGradSup
  eps_decay : ∃ B, ∀ β y, ‖y‖ * (m.epsP β).wt y ≤ B
  mu_decay : ∃ B, ∀ β y, (m.muP β).wt y ≤ B ∧ ‖y‖ ^ 2 * (m.muP β).wt y ≤ B
    ∧ ‖y‖ * wtGrad (m.muP β).wt y ≤ B
  eps_free_pos : ∀ β y, 0 < (m.epsP β).share1 y ∧ 0 < (m.epsP β).share2 y ∧ 0 < (m.epsP β).len y
    ∧ 0 < (m.epsP β).t0 y ∧ 0 < (m.epsP β).t1 y ∧ 0 < (m.epsP β).t2 y ∧ 0 < (m.epsP β).t3 y
    ∧ 0 < (m.epsP β).scale y
  mu_free_pos : ∀ β y, 0 < (m.muP β).share y ∧ 0 < (m.muP β).t4 y
  mu_eta_pos : ∀ β, 0 < (m.muP β).eta
  eps_free_measurable : ∀ β, Measurable (m.epsP β).share1 ∧ Measurable (m.epsP β).share2
    ∧ Measurable (m.epsP β).len ∧ Measurable (m.epsP β).t0 ∧ Measurable (m.epsP β).t1
    ∧ Measurable (m.epsP β).t2 ∧ Measurable (m.epsP β).t3 ∧ Measurable (m.epsP β).scale
  mu_free_measurable : ∀ β, Measurable (m.muP β).share ∧ Measurable (m.muP β).t4
  eps_free_axi : ∀ β, IsAxisymmetric (m.epsP β).share1 ∧ IsAxisymmetric (m.epsP β).share2
    ∧ IsAxisymmetric (m.epsP β).len ∧ IsAxisymmetric (m.epsP β).t0 ∧ IsAxisymmetric (m.epsP β).t1
    ∧ IsAxisymmetric (m.epsP β).t2 ∧ IsAxisymmetric (m.epsP β).t3 ∧ IsAxisymmetric (m.epsP β).scale
  mu_free_axi : ∀ β, IsAxisymmetric (m.muP β).share ∧ IsAxisymmetric (m.muP β).t4
  convD_even : ∀ ι y, m.convD (m.classOf (-ι)) y = m.convD (m.classOf ι) y
  convZ_even : ∀ ι y, m.convZ (m.classOf (-ι)) y = m.convZ (m.classOf ι) y
  convD_smooth : ∀ c, ContDiff ℝ 2 (m.convD c)
  convZ_smooth : ∀ c, ContDiff ℝ 2 (m.convZ c)
  convD_nonneg : ∀ c y, 0 ≤ m.convD c y
  convD_axi : ∀ c, IsAxisymmetric (m.convD c)
  convZ_axi : ∀ c, IsAxisymmetric (m.convZ c)
  convD_decay : ∃ B, ∀ c y, ∀ j ≤ 2, ‖y‖ ^ j * ‖iteratedFDeriv ℝ j (m.convD c) y‖ ≤ B
  convZ_decay : ∃ B, ∀ c y, ∀ j ≤ 2, (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j (m.convZ c) y‖ ≤ B
  conv_le : ∀ ι y, m.convD (m.classOf ι) y ≤ 1 - m.shareHat h ι y


def PieceMultiplierDensityWeakHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    {k : ℕ} (Γ : Set Symmetry) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ)
    (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hW : IsWeakSecondDerivState W HW D)
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
        (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, densityPosWith m P h w v G H W HW σ y)
            + ENNReal.ofReal (-m.multiplierGap P w act v G H κ F M)
          ≤ ENNReal.ofReal (m.multiplierGap P w act v G H κ F M)
            + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, densityNegWith m P h w v G H W HW σ y

def vortGradSupWith (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) : ℝ :=
  ⨆ p : ℝ × ℝ, ‖vortGradMap (HW p.1 (axialRot p.2 y))‖

def pieceEpsRestModeWith {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (β : Fin nE) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  -((m.epsP β).wt y * Coercive.vortAmp G ι σ y
    * (Coercive.edgeSum h (m.epsP β).modes (fun α => Coercive.velAmp W α σ y)
        (fun κ => Coercive.vortGradAmp H κ σ y) ι
      + Coercive.edgeSum h (m.epsP β).modes (fun α => Coercive.gradAmp (gradField W) α σ y)
        (fun κ => Coercive.vortAmp G κ σ y) ι
      + Coercive.edgeSum h (m.epsP β).modes (fun α => Coercive.vortGradAmp HW α σ y)
        (fun κ => Coercive.velAmp v κ σ y) ι
      + Coercive.edgeSum h (m.epsP β).modes (fun α => Coercive.vortAmp (gradField W) α σ y)
        (fun κ => Coercive.gradAmp G κ σ y) ι))

theorem pieceEpsRestModeWith_secondDerivField {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM)
    (h : HarmonicBounds) (W : ℝ → Space → Space) :
    pieceEpsRestModeWith m h W (secondDerivField W) = Coercive.pieceEpsRestMode m h W := rfl

def pieceEpsBlockWith {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (β : Fin nE) (σ : ℝ) (y : Space) : ℝ :=
  -(((m.epsP β).wt y * Coercive.frameSpeedSup W (m.epsP β).frame y + wtGrad (m.epsP β).wt y)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortGradAmp H κ σ y)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp G κ σ y))
    - (m.epsP β).wt y * ((1 / 2) * Coercive.vortSup W y + |(m.epsP β).frame|)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp G κ σ y) ^ 2
    - (m.epsP β).wt y * vortGradSupWith HW y
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.velAmp v κ σ y)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp G κ σ y)
    - (m.epsP β).wt y * Coercive.vortSup W y
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.gradAmp G κ σ y)
      * Coercive.pieceNorm (m.epsP β).modes (fun κ => Coercive.vortAmp G κ σ y)

def pieceRestWith {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  Coercive.modeVals v G H ι σ y (Coercive.baseDensity m.convD m.convZ (m.classOf ι) m.c w y)
    + ∑ β : Fin nE, pieceEpsRestModeWith m h W HW v G H β ι σ y
    + ∑ β : Fin nM, Coercive.pieceMuRestMode m h W v G β ι σ y

def pieceBlockWith {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (σ : ℝ) (y : Space) : ℝ :=
  ∑ β : Fin nE, pieceEpsBlockWith m W HW v G H β σ y + ∑ β : Fin nM, Coercive.pieceMuBlock m W v G β σ y

theorem pieceRestWith_secondDerivField {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) :
    pieceRestWith m h w W (secondDerivField W) = Coercive.pieceRest m h w W := rfl

def PieceFieldExistsWeakHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) {w₀ epsSup epsGradSup ratio : ℝ},
    IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio → (∃ B, ∀ y, w y ≤ B) →
    ∀ v G H g, IsPerturbation Γ P v G H g →
      m.seminormSq P v < ⊤ ∧ ∃ M, m.IsMultiplierField v G H M ∧
        periodNorm M ≤ Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt w₀) ^ 2 / m.c + ratio / m.cμ)
          * Real.sqrt (m.c * weightedEnergy w G H + m.cμ * (m.seminormSq P v).toReal)

def PieceDensityPassageWeakHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ} (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) (act : Fin k → ℝ → Space → Space)
    {w₀ epsSup epsGradSup ratio : ℝ},
    IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    IsWeakSecondDerivState W HW D →
    (∃ B, ∀ y, w y ≤ B) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (act i)) →
    (∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) →
    ∀ v G H g, IsPerturbation Γ P v G H g →
    ∀ u : ℕ → ℝ → Space → Space, Coercive.IsSmoothApproximation P v G H g u →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide W act κ v G g F →
      ∀ M, m.IsMultiplierField v G H M →
      Coercive.IsSplitLowerBound (m.multiplierGap P w act v G H κ F M)
        (fun σ y ι => Coercive.piecePos m P v G ι σ y) (fun σ y ι => pieceRestWith m h w W HW v G H ι σ y)
        (fun σ y => pieceBlockWith m W HW v G H σ y) (stretchFormWith W HW v G)

def PieceAbsorbStepWeakHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) (Γ : Set Symmetry) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) {w₀ epsSup epsGradSup ratio : ℝ},
    IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    IsWeakSecondDerivState W HW D →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v G H g, IsPerturbation Γ P v G H g → ∀ X : ℝ,
      Coercive.IsSplitLowerBound X (fun σ y ι => Coercive.piecePos m P v G ι σ y)
        (fun σ y ι => pieceRestWith m h w W HW v G H ι σ y)
        (fun σ y => pieceBlockWith m W HW v G H σ y) (stretchFormWith W HW v G) →
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, densityPosWith m P h w v G H W HW σ y) + ENNReal.ofReal (-X)
        ≤ ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, densityNegWith m P h w v G H W HW σ y

theorem pieceMultiplierDensityWeak_of_nodes (hF : PieceFieldExistsWeakHolds)
    (hA : Coercive.SmoothApproximationHolds) (hP : PieceDensityPassageWeakHolds)
    (hY : PieceAbsorbStepWeakHolds) : PieceMultiplierDensityWeakHolds := by
  intro C nE nM m P h w k Γ W HW D act w₀ epsSup epsGradSup ratio hm hW hwb hactm hactp hact2
    v G H g hv κ F hFm hFp hF2 hR
  obtain ⟨hfin, M, hMF, hnorm⟩ := hF m P h w Γ W HW D hm hwb v G H g hv
  obtain ⟨u, hu⟩ := hA Γ P v G H g hv
  exact ⟨M, hMF, hfin, hnorm, hY m P h w Γ W HW D hm hW hwb v G H g hv _
    (hP m P h w Γ W HW D act hm hW hwb hactm hactp hact2 v G H g hv u hu κ F hFm hFp hF2 hR M hMF)⟩

section Extended

variable {k : ℕ}

def ExtendedCoerciveClause (d : ExtendedCertificateData k) : Prop :=
  ∀ q ∈ d.params, ∀ v G H g, IsPerturbation d.symmetries (d.period q) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide (d.model q) d.actuator κ v G g F →
      Real.sqrt (weightedEnergy d.weightFn G H + d.multiplierWeight ^ 2 * ∑ i, κ i ^ 2) ≤
        d.coerciveL2 * periodNorm F + d.rows F + d.coercivePin * vecNorm (fun i => pinValue (d.pin i) G)

theorem extendedCoerciveClause_of_isExtendedCertificate {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) : ExtendedCoerciveClause d :=
  hd.coercive

theorem rows_nonneg (d : ExtendedCertificateData k) (F : ℝ → Space → Space) : 0 ≤ d.rows F :=
  Real.sqrt_nonneg _

theorem zero_mem_params (d : ExtendedCertificateData k) (hr : ∀ j ∈ d.adjointSet, 0 ≤ d.radius j) :
    (0 : Fin k → ℝ) ∈ d.params := by
  simp only [ExtendedCertificateData.params, Set.mem_ofPred_eq]
  refine ⟨fun j hj => by simpa using hr j hj, ?_⟩
  have e : ∑ j ∈ d.adjointSetᶜ, (d.scale j * (0 : Fin k → ℝ) j) ^ 2 = 0 := by simp
  rw [e]
  positivity

theorem actuator_finite (d : ExtendedCertificateData k)
    (hnorm : ∑ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) ≤
      ENNReal.ofReal (d.actuatorBound ^ 2)) (i : Fin k) :
    periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) < ⊤ :=
  lt_of_le_of_lt ((Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i)).trans hnorm)
    ENNReal.ofReal_lt_top

structure RowMultiplierInequality (d : ExtendedCertificateData k) (c cμ t a : ℝ) : Prop where
  c_pos : 0 < c
  cμ_nonneg : 0 ≤ cμ
  t_nonneg : 0 ≤ t
  a_nonneg : 0 ≤ a
  bound : ∀ q ∈ d.params, ∀ v G H g, IsPerturbation d.symmetries (d.period q) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide (d.model q) d.actuator κ v G g F →
      ∃ (M : ℝ → Space → Space) (n : ℝ),
        AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume ∧
        periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤ ∧ 0 ≤ n ∧
        periodNorm M ≤ a * Real.sqrt (c * weightedEnergy d.weightFn G H + cμ * n ^ 2) ∧
        c * (weightedEnergy d.weightFn G H + d.multiplierWeight ^ 2 * ∑ i, κ i ^ 2) + cμ * n ^ 2 ≤
          periodPairing F M + c * d.rows F ^ 2 + t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2

theorem extendedCoerciveClause_of_rowMultiplierInequality {d : ExtendedCertificateData k}
    {c cμ t a : ℝ} (h : RowMultiplierInequality d c cμ t a) (hL2 : a / Real.sqrt c ≤ d.coerciveL2)
    (hPin : Real.sqrt (t / c) ≤ d.coercivePin) : ExtendedCoerciveClause d := by
  intro q hq v G H g hv κ F hFm hFp hF2 hR
  obtain ⟨M, n, hMm, hM2, hn, hMnorm, hineq⟩ := h.bound q hq v G H g hv κ F hFm hFp hF2 hR
  have hpair : periodPairing F M ≤ periodNorm F * periodNorm M :=
    (le_abs_self _).trans (periodPairing_abs_le hFm hMm hF2 hM2)
  have hineq' : c * (weightedEnergy d.weightFn G H + d.multiplierWeight ^ 2 * ∑ i, κ i ^ 2) + cμ * n ^ 2 ≤
      periodPairing F M + c * 1 ^ 2 * d.rows F ^ 2 + t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2 := by
    rw [one_pow, mul_one]
    exact hineq
  have hbase := coercive_scalar_core h.c_pos h.cμ_nonneg h.t_nonneg h.a_nonneg zero_le_one
    (ENNReal.toReal_nonneg : 0 ≤ weightedEnergy d.weightFn G H)
    (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg (κ i))))
    (Real.sqrt_nonneg _) (rows_nonneg d F) (Real.sqrt_nonneg _) hMnorm hpair hineq'
  refine hbase.trans ?_
  have hNF : 0 ≤ periodNorm F := Real.sqrt_nonneg _
  have hh0 : 0 ≤ vecNorm (fun i => pinValue (d.pin i) G) := Real.sqrt_nonneg _
  rw [one_mul]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hL2 hNF) le_rfl)
    (mul_le_mul_of_nonneg_right hPin hh0)

def RowRestClause (d : ExtendedCertificateData k) {C : Type} {nE nM : ℕ}
    (m : (Fin k → ℝ) → PieceWeights C nE nM) (hs : (Fin k → ℝ) → HarmonicBounds)
    (HW : (Fin k → ℝ) → ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (c t : ℝ) : Prop :=
  ∀ q ∈ d.params, ∀ v G H g, IsPerturbation d.symmetries (d.period q) v G H g →
    ∀ (κ : Fin k → ℝ) (F : ℝ → Space → Space),
      AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume → IsTimePeriodic F →
      periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ →
      IsRightSide (d.model q) d.actuator κ v G g F →
      ∀ M, (m q).IsMultiplierField v G H M →
        (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
            densityNegWith (m q) (d.period q) (hs q) d.weightFn v G H (d.model q) (HW q) σ y) < ⊤ ∧
        ENNReal.ofReal (c * d.multiplierWeight ^ 2 * ∑ i, κ i ^ 2
            - ∑ i, κ i * periodPairing (d.actuator i) M
            - c * d.rows F ^ 2 - t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2)
          + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
            densityNegWith (m q) (d.period q) (hs q) d.weightFn v G H (d.model q) (HW q) σ y
        ≤ (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
            densityPosWith (m q) (d.period q) (hs q) d.weightFn v G H (d.model q) (HW q) σ y)
          + ENNReal.ofReal (-(c * d.multiplierWeight ^ 2 * ∑ i, κ i ^ 2
            - ∑ i, κ i * periodPairing (d.actuator i) M
            - c * d.rows F ^ 2 - t * vecNorm (fun i => pinValue (d.pin i) G) ^ 2))

theorem rowMultiplierInequality_of_pieceDensity (hD : PieceMultiplierDensityWeakHolds)
    {d : ExtendedCertificateData k}
    (hrad : ∀ j ∈ d.adjointSet, 0 ≤ d.radius j)
    (hwup : ∀ y, d.weightFn y ≤ d.weightMax)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => d.actuator i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (d.actuator i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖d.actuator i σ y‖ ^ 2) < ⊤)
    (HW : (Fin k → ℝ) → ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : (Fin k → ℝ) → ℝ)
    (hmodel : ∀ q ∈ d.params, IsWeakSecondDerivState (d.model q) (HW q) (D q))
    {C : Type} {nE nM : ℕ} (m : (Fin k → ℝ) → PieceWeights C nE nM)
    (hs : (Fin k → ℝ) → HarmonicBounds)
    {c cμ t epsSup epsGradSup ratio : ℝ}
    (hc : ∀ q ∈ d.params, (m q).c = c) (hcμ : ∀ q ∈ d.params, (m q).cμ = cμ) (ht : 0 ≤ t)
    (hm : ∀ q ∈ d.params, IsAdmissibleWeak (m q) (d.period q) (hs q) d.weightFn (d.model q) (HW q)
      d.weight epsSup epsGradSup ratio)
    (hrest : RowRestClause d m hs HW c t) :
    RowMultiplierInequality d c cμ t
      (Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt d.weight) ^ 2 / c + ratio / cμ)) := by
  have h0 := zero_mem_params d hrad
  have hc0 : 0 < c := hc 0 h0 ▸ (hm 0 h0).c_pos
  have hcμ0 : 0 < cμ := hcμ 0 h0 ▸ (hm 0 h0).cμ_pos
  refine ⟨hc0, hcμ0.le, ht, Real.sqrt_nonneg _, ?_⟩
  intro q hq v G H g hv κ F hFm hFp hF2 hR
  obtain ⟨M, hMF, hfin, hnorm, hdens⟩ := hD (m q) (d.period q) (hs q) d.weightFn d.symmetries
    (d.model q) (HW q) (D q) d.actuator (hm q hq) (hmodel q hq) ⟨d.weightMax, hwup⟩ hactm hactp hact2
    v G H g hv κ F hFm hFp hF2 hR
  obtain ⟨hneg, hbm⟩ := hrest q hq v G H g hv κ F hFm hFp hF2 hR M hMF
  set n2 := ((m q).seminormSq (d.period q) v).toReal with hn2
  have hn20 : 0 ≤ n2 := ENNReal.toReal_nonneg
  refine ⟨M, Real.sqrt n2, hMF.1, hMF.2.2.1, Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [Real.sq_sqrt hn20]
    rw [← hc q hq, ← hcμ q hq]
    exact hnorm
  · rw [Real.sq_sqrt hn20]
    have key := ModeWeights.le_of_ennreal_bounds hneg hdens hbm
    unfold PieceWeights.multiplierGap at key
    rw [hc q hq, hcμ q hq] at key
    linarith

end Extended

end CoerciveWeak

end Breakdown
