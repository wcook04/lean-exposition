import Breakdown.FracCell.SharpBoundCore

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace SharpParts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

def lowGrad (n : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ :=
  if n ∈ S.resolved then K.lowStrainAt c.order n S.degHigh x.2.1 p else 0

def lowVel (n : ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  if n ∈ S.resolved then K.lowVelocityAt c.order n S.degHigh x.1 p else 0

def sharpGrad (n : ℤ) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ :=
  fun a b => gradMode c.order n x.2.1 a b p - lowGrad c K S x n p a b

def sharpVel (n : ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun a => modeVec c.order n x.1 p.1 p.2 a - lowVel c K S x n p a

def pairWave (n n' : ℤ) (p : ℝ × ℝ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ)
    (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) : ℂ :=
  waveForm (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
    (CellScalars.curlGradMode c (n' - n) p) s v s' v'

def modeEnergy : ℝ :=
  ∑' n : ℤ, ∫ p in K.rect, p.1 * ((c.innerWeight - c.coercivity) * secondModeSq c.order n x.2.2.1 p
    + (c.splitVisc - c.innerWeight) * curlGradModeSq c.order n x.2.2.1 p)

def densityAt (α : ℝ) (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  CellScalars.densityForm c α p (fun a b => gradMode c.order n x.2.1 a b p)

def densitySum (α : ℝ) : ℝ :=
  ∑' n : ℤ, ∫ p in K.rect, p.1 * densityAt c x α n p

def lowMatrixDensity (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  sesqValue (S.localMatrix n p) (pairVec (lowGrad c K S x n p) (lowVel c K S x n p))

def lowMatrixSum : ℝ :=
  ∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * lowMatrixDensity c K S x n p

def matrixCrossDensity (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  (∑ i, ∑ j, ((starRingEnd ℂ) (pairVec (lowGrad c K S x n p) (lowVel c K S x n p) i) * S.localMatrix n p i j
        * pairVec (sharpGrad c K S x n p) (sharpVel c K S x n p) j
      + (starRingEnd ℂ) (pairVec (sharpGrad c K S x n p) (sharpVel c K S x n p) i) * S.localMatrix n p i j
        * pairVec (lowGrad c K S x n p) (lowVel c K S x n p) j)).re

def matrixCross : ℝ :=
  ∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * matrixCrossDensity c K S x n p

open Classical in
def crossOn (T : Set ℤ) : ℝ :=
  ∑ n ∈ S.resolved, ∑' n' : ℤ, ∫ p in K.rect, p.1 *
    (if n' ∈ T then
      pairWave c n n' p (lowGrad c K S x n p) (lowVel c K S x n p) (sharpGrad c K S x n' p) (sharpVel c K S x n' p)
        + pairWave c n' n p (sharpGrad c K S x n' p) (sharpVel c K S x n' p) (lowGrad c K S x n p) (lowVel c K S x n p)
      else 0).re

def sharpSharp : ℝ :=
  ∫ p in K.rect, p.1 * (∑' n : ℤ, ∑' n' : ℤ,
    pairWave c n n' p (sharpGrad c K S x n p) (sharpVel c K S x n p) (sharpGrad c K S x n' p) (sharpVel c K S x n' p)).re

def linearSharp (ζ : Fin k → ℝ) : ℝ :=
  ∑' n : ℤ, ∫ p in K.rect, p.1 * (∑ i : Fin k,
    (((x.2.2.2.1 i : ℝ) : ℂ) * entryPairing (sharpGrad c K S x n p) (fun a b => modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b)
      + ((2 * ζ i : ℝ) : ℂ) * entryPairing (sharpGrad c K S x n p) (fun a b => modeMat c.order n (c.modelPinField i) p.1 p.2 a b))).re

def supDensity (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  supremumLoss (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength
    (sharpGrad c K S x n p) (sharpVel c K S x n p)

def supSum : ℝ :=
  ∑' n : ℤ, ∫ p in K.rect, p.1 * supDensity c K S x n p

def penaltyDensity (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  if n ∈ S.resolved ∪ S.band then 0 else S.penalty (sharpGrad c K S x n p) (sharpVel c K S x n p)

def penaltySum : ℝ :=
  ∑' n : ℤ, ∫ p in K.rect, p.1 * penaltyDensity c K S x n p

def classDensity (Cl : CellClasses) (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  if n ∈ S.resolved ∪ S.band then 0 else
    ∑ i, Cl.classLoss S.splitLength i p (sharpGrad c K S x n p) (sharpVel c K S x n p) / Cl.shareWeight i

def classSum (Cl : CellClasses) : ℝ :=
  ∑' n : ℤ, ∫ p in K.rect, p.1 * classDensity c K S x Cl n p

def rowChargeDensity (Cl : CellClasses) (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  if n ∈ S.resolved ∪ S.band then 0 else
    ∑ i, 2 * Cl.rowWeight i * (Cl.velocityDev i p ^ 2 * curlSq (fun a b => gradMode c.order n x.2.1 a b p)
      + Cl.curlDev i p ^ 2 * vecSq (modeVec c.order n x.1 p.1 p.2))

def absorbDensity (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  S.curlAbsorb n * curlSq (sharpGrad c K S x n p) + S.strainAbsorb n * sumSq (sharpGrad c K S x n p)
    + (if n ∈ S.resolved then S.velocityAbsorb n * vecSq (sharpVel c K S x n p) else 0)

def absorbSum : ℝ :=
  ∑' n : ℤ, ∫ p in K.rect, K.lineWeight p.1 * absorbDensity c K S x n p

def weightedSharp (B : CellBases) {slots : ℕ} (R : CellRows N slots k) : ℝ :=
  (∑ n ∈ R.yModes, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
      if n ∉ S.resolved ∨ S.degHigh < max j l then
        S.symWeight n j l * symSq (sharpStrainCoef c K B x n j l) + S.antiWeight n j l * antiSq (sharpStrainCoef c K B x n j l)
      else 0)
    + (∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
      if S.degHigh ≤ max j l then S.velWeight n j l * vecSq (sharpVelocityCoef c K B x n j l) else 0)
    + ∑' jl : ℕ × ℕ, if S.degNear < max jl.1 jl.2 then
        (∑ n ∈ R.yModes, if n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2 then
            S.symWeight n jl.1 jl.2 * symSq (sharpStrainCoef c K B x n jl.1 jl.2)
              + S.antiWeight n jl.1 jl.2 * antiSq (sharpStrainCoef c K B x n jl.1 jl.2)
          else 0)
        + ∑ n ∈ S.resolved, if S.degHigh ≤ max jl.1 jl.2 then
            S.velWeight n jl.1 jl.2 * vecSq (sharpVelocityCoef c K B x n jl.1 jl.2) else 0
      else 0

end SharpParts

open SharpParts

def ModeExpansionStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      modeEnergy c K x + densitySum c K x α
          + (CellScalars.localPairForm c K S x.1 x.2.1 - lowMatrixSum c K S x)
          + crossOn c K S x (↑(S.resolved ∪ S.band)) + crossOn c K S x (↑(S.resolved ∪ S.band))ᶜ
          + sharpSharp c K S x + CellScalars.linearTerm c K S x.2.2.2.1 ζ x.2.1 + linearSharp c K S x ζ
        ≤ (∫ p in K.rect, p.1 * ((∑' n : ℤ, modeLocalDensity c α x n p) + modeCoupling c x p
              + ∑ i, x.2.2.2.1 i * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p))
          + (∑ i, 2 * ζ i * ∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelPinField i) p)

def SharpDensityStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      lowMatrixSum c K S x + matrixCross c K S x + supSum c K S x + penaltySum c K S x - absorbSum c K S x
        ≤ densitySum c K x α

def SharpSupremumStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      -supSum c K S x ≤ sharpSharp c K S x

def SharpCrossStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
      CellScalars.sharpForm c K S R B (fun _ => 0) x.2.2.2.1 ζ x.1 x.2.1
          (sharpStrainCoef c K B x) (sharpVelocityCoef c K B x)
        ≤ weightedSharp c K S x B R + crossOn c K S x (↑(S.resolved ∪ S.band)) + linearSharp c K S x ζ
          + matrixCross c K S x

def ClassCrossStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      -CellScalars.classTerm c K S Cl x.1 x.2.1 - classSum c K S x Cl
        ≤ crossOn c K S x (↑(S.resolved ∪ S.band))ᶜ

def PenaltyChargeStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      classSum c K S x Cl + CellScalars.unresolvedRowCharge c K S Cl x ≤ penaltySum c K S x

def ChargeRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * classDensity c K S x Cl n p) K.rect) ∧
      (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * rowChargeDensity c S x Cl n p) K.rect) ∧
      (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * penaltyDensity c K S x n p) K.rect) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * classDensity c K S x Cl n p) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * rowChargeDensity c S x Cl n p) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * penaltyDensity c K S x n p) ∧
      CellScalars.unresolvedRowCharge c K S Cl x = ∑' n : ℤ, ∫ p in K.rect, p.1 * rowChargeDensity c S x Cl n p

def DensityRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * densityAt c x α n p) K.rect) ∧
      (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * supDensity c K S x n p) K.rect) ∧
      (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * penaltyDensity c K S x n p) K.rect) ∧
      (∀ n, IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * absorbDensity c K S x n p) K.rect) ∧
      (∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * lowMatrixDensity c K S x n p) K.rect) ∧
      (∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * matrixCrossDensity c K S x n p) K.rect) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * densityAt c x α n p) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * supDensity c K S x n p) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * penaltyDensity c K S x n p) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, K.lineWeight p.1 * absorbDensity c K S x n p)

def SharpFieldStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ n, ∀ᵐ p ∂(volume.restrict K.rect), IsTraceFree (sharpGrad c K S x n p)) ∧
      (∀ n ∉ S.resolved, ∀ᵐ p ∂(volume.restrict K.rect),
        turnVec (azimuth c.order n) (modeVec c.order n x.1 p.1 p.2) = fun a => (p.1 : ℂ) * gradMode c.order n x.2.1 a 1 p)

def SharpEnergyTailStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      CellScalars.energyTerm c K S x.2.1 x.2.2.1 + weightedSharp c K S x B R + absorbSum c K S x
        ≤ modeEnergy c K x

end CellAnalysis

end CellCert

end Breakdown
