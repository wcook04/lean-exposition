import Breakdown.CertCell.AssemblyStatements

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

section PotentialParts

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def trueCoupling (α : ℤ × ℤ) (p : ℝ × ℝ) : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i j => modelTriple
    (fun a b => (labelGrad D.azimuthOrder α (gradField D.given) p (a, b)
      + labelGrad D.azimuthOrder α (gradField D.given) p (b, a)) / 2)
    (fun a b => curlGradOfSecondDeriv (labelHess D.azimuthOrder α D.givenHess p) (a, b))
    (velOf (Pi.single j 1)) (gradOf (Pi.single j 1)) (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1)))

open Classical in
def restrictTo (S : Set (ℤ × ℤ)) (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ :=
  fun ι p => if ι ∈ S then X ι p else 0

def trueProfiles (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) :
    ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ :=
  fun ι p => bandProfile D ι v G p

def otherProfiles (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ :=
  fun ι p => trueProfiles D v G ι p - upperProfiles D R K P x ι p

def tailProfiles (K : Fin D.mesh.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) :
    ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ :=
  restrictTo (D.mesh.resolved K : Set (ℤ × ℤ)) (fun ι p => tailProfile D R K ι v G p)

def deactivatedSet (K : Fin D.mesh.count) : Set (ℤ × ℤ) :=
  {ι | ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K}

def trueStretch (K : Fin D.mesh.count) (H : Finset (ℤ × ℤ)) (X Y : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑' ι : ℤ × ℤ, ∑ α ∈ H, ∫ p in (D.mesh.box K).rect,
    p.1 * (sesq12 (trueCoupling D α p) (X ι p) (Y (ι - α) p)).re

def modelPair (K : Fin D.mesh.count) (M : ℤ × ℤ → ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ) (S T : Finset (ℤ × ℤ))
    (X Y : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ ι ∈ S, ∑ ι' ∈ T, ∫ p in (D.mesh.box K).rect, p.1 * (sesq12 (M (ι - ι') p) (X ι p) (Y ι' p)).re

def leafPair (K : Fin D.mesh.count) (X Y : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ ι ∈ D.mesh.resolved K, ∫ p in (D.mesh.box K).rect,
    p.1 * (sesq12 ((R.leaves K).localMatrix ι p) (X ι p) (Y ι p)).re

def alAmount (K : Fin D.mesh.count) (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ ι ∈ D.mesh.resolved K, ∫ p in (D.mesh.box K).rect, (D.mesh.box K).lineWeight p.1 *
    ((R.leaves K).curlAbsorb ι * curlSq (strainOfVec (X ι p)) + (R.leaves K).strainAbsorb ι * sumSq (strainOfVec (X ι p))
      + (R.leaves K).velocityAbsorb ι * vecSq (velOf (X ι p)))

def boxPairAmount (K : Fin D.mesh.count) (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ ι ∈ D.mesh.resolved K, ∫ p in (D.mesh.box K).rect,
    p.1 * (R.leaves K).boxPairPenalty ι (strainOfVec (X ι p)) (velOf (X ι p))

def formAmount (K : Fin D.mesh.count) (S : Finset (ℤ × ℤ)) (f : (Fin 3 → ℂ) → (Fin 3 × Fin 3 → ℂ) → ℝ)
    (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ ι ∈ S, ∫ p in (D.mesh.box K).rect, p.1 * f (velOf (X ι p)) (gradOf (X ι p))

def deactPartners (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) : Finset (ℤ × ℤ) :=
  ((D.mesh.resolved K ×ˢ P.harmonicLabels).image (fun x => x.1 - x.2)).filter
    (fun ι => ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K)

def labelFormAmount (K : Fin D.mesh.count) (S : Finset (ℤ × ℤ))
    (f : ℤ × ℤ → (Fin 3 → ℂ) → (Fin 3 × Fin 3 → ℂ) → ℝ) (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ ι ∈ S, ∫ p in (D.mesh.box K).rect, p.1 * f ι (velOf (X ι p)) (gradOf (X ι p))

def extraChargeDensity (K : Fin D.mesh.count) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  (R.entryCharges K ι).curlCharge p * modeCurlSq D ι G p + (R.entryCharges K ι).gradCharge p * modeStrainSq D ι G p
    + (R.entryCharges K ι).velCharge p * modeVelSq D ι v p

open Classical in
def chargeSurplus (K : Fin D.mesh.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑' ι : ℤ × ℤ, if ι ∈ D.mesh.resolved K then 0 else
    ∫ p in (D.mesh.box K).rect, extraChargeDensity D R K ι v G p * p.1

open Classical in
def stretchChargeAmount (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑' ι : ℤ × ℤ, if ι ∈ D.mesh.resolved K then 0 else ∫ p in (D.mesh.box K).rect,
    (D.labelDensity q v G H ι p
      - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
          (R.entryCharges K ι) D.azimuthOrder ι v G H p
      - extraChargeDensity D R K ι v G p) * p.1

def groupPartnerAmount (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K))
    (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ i, formAmount D K (P.groupPartners i) (groupCharge P i) X / P.groupBalance i

def groupOwnAmount (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K))
    (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) : ℝ :=
  ∑ i, P.groupBalance i *
    formAmount D K (D.mesh.resolved K ∩ P.groupModes i) (groupCharge P i) X

variable (A : AssemblyEntry D R) (P : CouplingEntries D R)

def StretchExpansion : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    stretchAmount D K v G = trueStretch D K (P.potential K).harmonicLabels (trueProfiles D v G) (trueProfiles D v G)

def LowTailSplit : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    ∀ ι ∈ D.mesh.resolved K, ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect),
      trueProfiles D v G ι p
        = lowAt D R K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) ι p + tailProfile D R K ι v G p

def StretchSplit : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    trueStretch D K (P.potential K).harmonicLabels (trueProfiles D v G) (trueProfiles D v G)
      = trueStretch D K (P.potential K).harmonicLabels
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
        + 2 * trueStretch D K (P.potential K).harmonicLabels
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (restrictTo (D.mesh.resolved K : Set (ℤ × ℤ))
            (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G))
        + 2 * trueStretch D K (P.potential K).harmonicLabels
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (restrictTo (D.mesh.band K : Set (ℤ × ℤ)) (trueProfiles D v G))
        + 2 * trueStretch D K (P.potential K).harmonicLabels
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (restrictTo (deactivatedSet D K) (trueProfiles D v G))
        + trueStretch D K (P.potential K).harmonicLabels
          (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
          (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)

def LeafSplit : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    leafPair D R K (trueProfiles D v G) (trueProfiles D v G) + boxAmount D R K v G
        - leafPair D R K (lowAt D R K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
            (lowAt D R K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
      ≤ resolvedAmount D K q v G H - (energyBudget D R K v G H Pg + tailCredit D R K G H)

def SharpStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    -alAmount D R K (lowAt D R K (bandPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)))
        - alAmount D R K (tailProfiles D R K v G)
        + boxPairAmount D R K (restrictTo (D.mesh.resolved K : Set (ℤ × ℤ))
            (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G))
      ≤ leafPair D R K (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
          (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
        + trueStretch D K (P.potential K).harmonicLabels
          (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
          (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
        + stretchChargeAmount D R K q v G H

def ModelStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    couplingPair D R K (P.potential K)
          (upperPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (upperPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
        + 2 * couplingPair D R K (P.potential K)
          (upperPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (bandPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
        + 2 * modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.resolved K)
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (tailProfiles D R K v G)
        + bandLinear D K (A.blocks K).potentialSource (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
            (fun ι => bandProfile D ι v G)
        + 2 * modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (deactPartners D R K (P.potential K))
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)) (trueProfiles D v G)
        - formAmount D K (deactPartners D R K (P.potential K)) (epsPartnerCharge (P.potential K)) (trueProfiles D v G)
        - labelFormAmount D K (deactPartners D R K (P.potential K)) (longPartnerCharge (P.potential K)) (trueProfiles D v G)
        - highPartnerAmount D K (P.potential K) (deactPartners D R K (P.potential K)) (trueProfiles D v G)
        - formAmount D K (D.mesh.resolved K) (epsOwnCharge (P.potential K))
            (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
        - formAmount D K (D.mesh.resolved K) (epsPartnerCharge (P.potential K))
            (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
        - formAmount D K (D.mesh.band K) (epsPartnerCharge (P.potential K))
            (trueProfiles D v G)
        - labelFormAmount D K (D.mesh.resolved K) (longOwnCharge (P.potential K))
            (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
        - labelFormAmount D K (D.mesh.resolved K) (longPartnerCharge (P.potential K))
            (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
        - labelFormAmount D K (D.mesh.band K) (longPartnerCharge (P.potential K)) (trueProfiles D v G)
        - highOwnAmount D K (P.potential K) (D.mesh.resolved K)
            (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
        - highPartnerAmount D K (P.potential K) (D.mesh.resolved K) (tailProfiles D R K v G)
        - highPartnerAmount D K (P.potential K) (D.mesh.band K) (trueProfiles D v G)
      ≤ trueStretch D K (P.potential K).harmonicLabels
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
        + 2 * trueStretch D K (P.potential K).harmonicLabels
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (restrictTo (D.mesh.resolved K : Set (ℤ × ℤ))
            (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G))
        + 2 * trueStretch D K (P.potential K).harmonicLabels
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (restrictTo (D.mesh.band K : Set (ℤ × ℤ)) (trueProfiles D v G))
        + 2 * trueStretch D K (P.potential K).harmonicLabels
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (restrictTo (deactivatedSet D K) (trueProfiles D v G))

def TailCrossStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    -quadFormValue (P.potential K).portForm (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
        - ∑ ι ∈ D.mesh.resolved K, ((P.potential K).strainBalance ι * tailStrainSq D R K ι G
            + (P.potential K).velBalance ι * tailVelSq D R K ι v)
      ≤ 2 * modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.resolved K)
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (tailProfiles D R K v G)
        + 2 * leafPair D R K (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (tailProfiles D R K v G)

def GroupStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    -groupOwnAmount D R K (P.potential K)
        (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
        - groupPartnerAmount D R K (P.potential K) (trueProfiles D v G)
      ≤ 2 * modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (deactPartners D R K (P.potential K))
          (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)) (trueProfiles D v G)

def ChargeStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    bandQuad D K (A.blocks K).bandWeight (fun ι => bandProfile D ι v G)
        + rowLeakAmount D K (A.blocks K) v G + pairingLeakAmount D K (A.blocks K) G
        + groupPartnerAmount D R K (P.potential K) (trueProfiles D v G)
        + formAmount D K (D.mesh.band K) (epsPartnerCharge (P.potential K))
            (trueProfiles D v G)
        + labelFormAmount D K (D.mesh.band K) (longPartnerCharge (P.potential K)) (trueProfiles D v G)
        + formAmount D K (deactPartners D R K (P.potential K)) (epsPartnerCharge (P.potential K)) (trueProfiles D v G)
        + labelFormAmount D K (deactPartners D R K (P.potential K)) (longPartnerCharge (P.potential K)) (trueProfiles D v G)
        + highPartnerAmount D K (P.potential K) (deactPartners D R K (P.potential K)) (trueProfiles D v G)
        + highPartnerAmount D K (P.potential K) (D.mesh.band K) (trueProfiles D v G)
        + bandAllowance D K (A.blocks K).bandCurlAllowance (A.blocks K).bandVelAllowance v G
        + creditAmount D R K v
        + pairSlackAmount D R K (D.mesh.band K) G + pairSlackAmount D R K (deactSlackLabels D R K) G
      ≤ chargeSurplus D R K v G

def TailHighStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg →
    highPartnerAmount D K (P.potential K) (D.mesh.resolved K) (tailProfiles D R K v G)
      ≤ ∑ ι ∈ D.mesh.resolved K, (rHatMax D K * (2 * (P.potential K).highStrain / (P.potential K).youngCurl
            + 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngVel) * tailStrainSq D R K ι G
          + rHatMax D K * (3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngStrain) * tailVelSq D R K ι v)

def EpsResolvedStage : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    formAmount D K (D.mesh.resolved K) (epsPartnerCharge (P.potential K))
        (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
      + labelFormAmount D K (D.mesh.resolved K) (longPartnerCharge (P.potential K))
        (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
      ≤ boxPairAmount D R K (restrictTo (D.mesh.resolved K : Set (ℤ × ℤ))
          (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G))

def SplitIdentities : Prop :=
  ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
    offChargeAmount D R K q v G H = stretchChargeAmount D R K q v G H + chargeSurplus D R K v G ∧
    leafPair D R K (trueProfiles D v G) (trueProfiles D v G)
        - leafPair D R K (lowAt D R K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
            (lowAt D R K (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
      = 2 * leafPair D R K (upperProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
          (tailProfiles D R K v G)
        + leafPair D R K (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
          (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
        - leafPair D R K (lowAt D R K (bandPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)))
          (lowAt D R K (bandPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))) ∧
    alAmount D R K (tailProfiles D R K v G)
      = ∑ ι ∈ D.mesh.resolved K, ((R.leaves K).curlAbsorb ι * tailCurlSq D R K ι G
          + (R.leaves K).strainAbsorb ι * tailStrainSq D R K ι G + (R.leaves K).velocityAbsorb ι * tailVelSq D R K ι v)

end PotentialParts

section Holds

def LowTailSplitHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D),
    AssemblyRegular D R → TrueFieldRegular D → CellCalculusConditions D R → LowTailSplit D R

def LeafSplitHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D),
    AssemblyRegular D R → TrueFieldRegular D → CellPiecesFinite D R → CellCalculusConditions D R → LeafSplit D R

def StretchExpansionHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P S →
      StretchExpansion D R P

def StretchSplitHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P S → LowTailSplit D R →
      StretchSplit D R P

def SharpStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → CellPiecesFinite D R →
      PotentialConditions D R A P S → LowTailSplit D R → SharpStage D R P

def EpsResolvedStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P S →
      LowTailSplit D R → EpsResolvedStage D R P

def ModelStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P S →
      LowTailSplit D R → ModelStage D R A P

def TailCrossStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P S →
      LowTailSplit D R → TailCrossStage D R P

def GroupStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P S → GroupStage D R P

def ChargeStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P S →
      ChargeStage D R A P

def TailHighStageHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P S → TailHighStage D R P

def SplitIdentitiesHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → CellPiecesFinite D R →
      PotentialConditions D R A P S → LowTailSplit D R → SplitIdentities D R P

def PotentialAssemblyHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R)
    (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), CellStatesIn D R S → AssemblyRegular D R → TrueFieldRegular D → CellPiecesFinite D R →
    PotentialConditions D R A P S →
    StretchExpansion D R P → StretchSplit D R P → LeafSplit D R →
    SharpStage D R P → ModelStage D R A P → TailCrossStage D R P → GroupStage D R P →
    ChargeStage D R A P → TailHighStage D R P → EpsResolvedStage D R P → SplitIdentities D R P →
    PotentialStage D R A


theorem potentialStage_of_parts (hLT : LowTailSplitHolds) (hLS : LeafSplitHolds)
    (hSE : StretchExpansionHolds) (hSS : StretchSplitHolds) (hSh : SharpStageHolds) (hEps : EpsResolvedStageHolds)
    (hMo : ModelStageHolds) (hTC : TailCrossStageHolds) (hGr : GroupStageHolds) (hCh : ChargeStageHolds)
    (hTH : TailHighStageHolds) (hSI : SplitIdentitiesHolds) (hAs : PotentialAssemblyHolds) : PotentialStageHolds := by
  intro k C nE nM D R A P S hr ht hf hs h
  have hl := hLT D R hr ht h.cell_conditions
  exact hAs D R A P S hs hr ht hf h (hSE D R A P S hs hr ht h) (hSS D R A P S hs hr ht h hl)
    (hLS D R hr ht hf h.cell_conditions)
    (hSh D R A P S hs hr ht hf h hl) (hMo D R A P S hs hr ht h hl) (hTC D R A P S hs hr ht h hl)
    (hGr D R A P S hs hr ht h) (hCh D R A P S hs hr ht h) (hTH D R A P S hs hr ht h) (hEps D R A P S hs hr ht h hl)
    (hSI D R A P S hs hr ht hf h hl)

end Holds

end Assembly

end CertCell

end Breakdown
