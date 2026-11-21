import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.ExtendedStatement
import Breakdown.Cert.ExtendedCoerciveDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

open PieceWeights

def EnergyIdentitySmoothWeakHolds : Prop :=
  ∀ (P : ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) (v : ℝ → Space → Space), 0 < P → IsWeakSecondDerivState W HW D →
    Coercive.IsSmoothPerturbation P v →
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (Coercive.smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)) =
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)
        + (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 + stretchFormWith W HW v (gradField v) σ y)

def PiecePairingSplitSmoothWeakHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) {w₀ epsSup epsGradSup ratio : ℝ},
    IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    IsWeakSecondDerivState W HW D →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, Coercive.IsSmoothPerturbation P v → ∀ M Q, m.IsMultiplierField v (gradField v) (secondDerivField v) M →
      Coercive.IsSolenoidalPartOf (Coercive.smoothRight P W v) Q →
      periodPairing (Coercive.smoothRight P W v) M =
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
            inner ℝ (Coercive.smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)))
          + ∑ β : Fin nE, Coercive.epsPairing (fun ι y => sgn (m.epsP β).modes ι * (m.epsP β).wt y) v
              (Coercive.smoothRight P W v)
          + ∑ β : Fin nM, Coercive.muPairing (fun ι y => sgn (m.muP β).modes ι * (m.muP β).wt y) v Q

def PieceEpsEstimateSmoothWeakHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) {w₀ epsSup epsGradSup ratio : ℝ},
    IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    IsWeakSecondDerivState W HW D →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, Coercive.IsSmoothPerturbation P v → ∀ β : Fin nE,
      Coercive.IsSplitLowerBound
        (Coercive.epsPairing (fun ι y => sgn (m.epsP β).modes ι * (m.epsP β).wt y) v
          (Coercive.smoothRight P W v))
        (fun σ y ι => Coercive.pieceEpsPos m P (gradField v) β ι σ y)
        (fun σ y ι => pieceEpsRestModeWith m h W HW v (gradField v) (secondDerivField v) β ι σ y)
        (fun σ y => pieceEpsBlockWith m W HW v (gradField v) (secondDerivField v) β σ y) (fun _ _ => 0)

def PieceMuEstimateSmoothWeakHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) {w₀ epsSup epsGradSup ratio : ℝ},
    IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    IsWeakSecondDerivState W HW D →
    (∃ B, ∀ y, w y ≤ B) →
    ∀ v, Coercive.IsSmoothPerturbation P v → ∀ Q, Coercive.IsSolenoidalPartOf (Coercive.smoothRight P W v) Q →
      ∀ β : Fin nM,
      Coercive.IsSplitLowerBound
        (Coercive.muPairing (fun ι y => sgn (m.muP β).modes ι * (m.muP β).wt y) v Q
          - m.cμ * (Coercive.pieceSeminormPart m P β v).toReal)
        (fun σ y ι => Coercive.pieceMuPos m P v β ι σ y)
        (fun σ y ι => Coercive.pieceMuRestMode m h W v (gradField v) β ι σ y)
        (fun σ y => Coercive.pieceMuBlock m W v (gradField v) β σ y) (fun _ _ => 0)

def PieceDensitySmoothWeakHolds : Prop :=
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ} (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (D : ℝ) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ},
    IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    IsWeakSecondDerivState W HW D →
    (∃ B, ∀ y, w y ≤ B) →
    (∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume) →
    (∀ i, IsTimePeriodic (act i)) →
    (∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤) →
    ∀ v, Coercive.IsSmoothPerturbation P v → ∀ (κ : Fin k → ℝ) M,
      m.IsMultiplierField v (gradField v) (secondDerivField v) M →
      Coercive.IsSplitLowerBound (m.multiplierGap P w act v (gradField v) (secondDerivField v) κ
          (fun σ y => Coercive.smoothRight P W v σ y + ∑ i, κ i • act i σ y) M)
        (fun σ y ι => Coercive.piecePos m P v (gradField v) ι σ y)
        (fun σ y ι => pieceRestWith m h w W HW v (gradField v) (secondDerivField v) ι σ y)
        (fun σ y => pieceBlockWith m W HW v (gradField v) (secondDerivField v) σ y)
        (stretchFormWith W HW v (gradField v))

section Extended

variable {k : ℕ}

theorem isExtendedCertificate_of_clause {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (hc : ExtendedCoerciveClause d) : IsExtendedCertificate d :=
  { hd with coercive := hc }

end Extended

end CoerciveWeak

end Breakdown
