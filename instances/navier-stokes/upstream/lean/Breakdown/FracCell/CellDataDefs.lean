import Breakdown.FracCell.Defs
import Breakdown.FracCell.AssemblyDefs
import Breakdown.FracCell.ExteriorDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

def measure : Measure (ℝ × ℝ) :=
  (volume.restrict K.rect).withDensity (fun p => ENNReal.ofReal (K.lineWeight p.1))

end CellBox

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

def polyFn (d d' : ℕ) : Set (ℝ × ℝ → ℂ) :=
  {P | ∃ c : Fin (d + 1) → Fin (d' + 1) → ℂ, ∀ p : ℝ × ℝ,
    P p = ∑ j, ∑ l, c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ))}

def scaledPolyFn (f : ℝ × ℝ → ℝ) (d d' : ℕ) : Set (ℝ × ℝ → ℂ) :=
  {P | ∃ P₀ ∈ polyFn d d', ∀ p, P p = (f p : ℂ) * P₀ p}

namespace CellBox

variable (K : CellBox)

def pairOn (m : ℝ × ℝ → ℝ) (F P : ℝ × ℝ → ℂ) : ℂ :=
  ∫ p in K.rect, (m p : ℂ) * F p * (starRingEnd ℂ) (P p)

def normSqOn (m : ℝ × ℝ → ℝ) (F : ℝ × ℝ → ℂ) : ℝ :=
  ∫ p in K.rect, m p * ‖F p‖ ^ 2

def testSupremum (m : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ → ℂ)) (g : ℝ × ℝ → ℂ) : ℝ :=
  sSup {t | ∃ P ∈ V, 0 < K.normSqOn m P ∧ t = ‖K.pairOn m g P‖ ^ 2 / K.normSqOn m P}

def lineWeightFn : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1

open Classical in
def proj (d d' : ℕ) (F : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  if h : ∃ P ∈ polyFn d d', ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0
  then h.choose else 0

def radialEnergy (Q q : ℕ) (F dF : ℝ × ℝ → ℂ) : ℝ :=
  K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
      (radialDeriv (K.proj Q Q F))
    + (if K.r₁ = 0 then 0 else
        K.testSupremum (fun p => (p.1 - K.r₁) * (1 - K.refR p.1 ^ 2)) (polyFn (Q - 2) Q) dF)
    + K.testSupremum (fun p => p.1) (scaledPolyFn K.lineWeightFn (Q - 1) q) (fun p => (K.refR p.1 : ℂ) * dF p)

def heightEnergy (Q q : ℕ) (F dF : ℝ × ℝ → ℂ) : ℝ :=
  K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
      (heightDeriv (K.proj Q Q F))
    + (if K.r₁ = 0 then 0 else
        K.testSupremum (fun p => (p.1 - K.r₁) * (1 - K.refZ p.2 ^ 2)) (polyFn (Q - 1) (Q - 1)) dF)
    + K.testSupremum (fun p => p.1) (polyFn q Q) (fun p => (K.refZ p.2 : ℂ) * dF p)

def angularEnergy (Q : ℕ) (F : ℝ × ℝ → ℂ) : ℝ :=
  if K.r₁ = 0 then
    K.testSupremum (fun p => p.1) (scaledPolyFn (fun p => p.1) Q Q) (fun p => F p / (p.1 : ℂ))
  else
    K.r₂⁻¹ * K.normSqOn (fun _ => 1) (K.proj Q Q F)
      + K.testSupremum (fun p => (K.r₂ - p.1) / (p.1 * K.r₂)) (scaledPolyFn (fun p => p.1) (Q - 1) Q) F

end CellBox

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

def radialGradMode (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) : ℂ :=
  modeThird m n H a b 0 p

def heightGradMode (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) : ℂ :=
  modeThird m n H a b 2 p

def angularGradMode (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) * modeThird m n H a b 1 p

def secondModeSq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ‖modeThird m n H a b c p‖ ^ 2

def curlGradModeSq (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ c : Fin 3, ‖curlComp (fun a b => modeThird m n H a b c p) i‖ ^ 2

namespace CellBox

variable (K : CellBox)

def strainEnergy (m : ℕ) (n : ℤ) (Q q : ℕ) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    (K.radialEnergy Q q (gradMode m n G a b) (radialGradMode m n H a b)
      + K.heightEnergy Q q (gradMode m n G a b) (heightGradMode m n H a b)
      + K.angularEnergy Q (angularGradMode m n H a b))

def vorticityEnergy (m : ℕ) (n : ℤ) (Q q : ℕ) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑ i : Fin 3,
    (K.radialEnergy Q q (fun p => curlComp (fun a b => gradMode m n G a b p) i)
        (fun p => curlComp (fun a b => radialGradMode m n H a b p) i)
      + K.heightEnergy Q q (fun p => curlComp (fun a b => gradMode m n G a b p) i)
        (fun p => curlComp (fun a b => heightGradMode m n H a b p) i)
      + K.angularEnergy Q (fun p => curlComp (fun a b => angularGradMode m n H a b p) i))

def tailGradWeight (Q : ℕ) (F dFr dFz : ℝ × ℝ → ℂ) : ℝ :=
  K.innerRadius *
    (K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
        (fun p => dFr p - radialDeriv (K.proj Q Q F) p)
      + K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
        (fun p => dFz p - heightDeriv (K.proj Q Q F) p))

def tailNormSq (Q : ℕ) (F : ℝ × ℝ → ℂ) : ℝ :=
  K.normSqOn K.lineWeightFn (fun p => F p - K.proj Q Q F p)

end CellBox

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

def fullGradWeight (dFr dFz : ℝ × ℝ → ℂ) : ℝ :=
  K.innerRadius *
    (K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)) dFr
      + K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)) dFz)

open Classical in
def projR (d : ℕ) (F : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun p =>
  if h : ∃ c : Fin (d + 1) → ℂ, ∀ t : Fin (d + 1),
      ∫ r in Set.Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) *
        (F (r, p.2) - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0
  then ∑ j, h.choose j * (p.1 : ℂ) ^ (j : ℕ) else 0

def topPart (Q : ℕ) (sr sz : ℝ × ℝ → ℂ) : ℝ :=
  (K.normSqOn K.lineWeightFn (K.proj Q Q sr) - K.normSqOn K.lineWeightFn (K.proj (Q - 2) Q sr))
    + (K.normSqOn K.lineWeightFn (K.proj (Q - 1) Q sz) - K.normSqOn K.lineWeightFn (K.proj (Q - 1) (Q - 2) sz))

def velocityTail (Q : ℕ) (F : ℝ × ℝ → ℂ) : ℝ :=
  K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
      (radialDeriv (fun p => F p - K.projR (Q - 1) F p))
    + K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
      (heightDeriv (fun p => K.projR (Q - 1) F p - K.proj (Q - 1) (Q - 1) F p))

end CellBox

def ResolvedEnergyStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (Q q : ℕ), 3 ≤ q → q + 2 ≤ Q →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H → ∀ n : ℤ, (K.IsAxis → n = 0) →
        K.strainEnergy m n Q q G H
            + ∑ a : Fin 3, ∑ b : Fin 3,
                (K.tailGradWeight Q (gradMode m n G a b) (radialGradMode m n H a b) (heightGradMode m n H a b)
                  + K.angularWeight n * K.tailNormSq Q (angularGradMode m n H a b))
          ≤ ∫ p in K.rect, p.1 * secondModeSq m n H p ∧
        K.vorticityEnergy m n Q q G H
            + ∑ i : Fin 3,
                (K.tailGradWeight Q (fun p => curlComp (fun a b => gradMode m n G a b p) i)
                    (fun p => curlComp (fun a b => radialGradMode m n H a b p) i)
                    (fun p => curlComp (fun a b => heightGradMode m n H a b p) i)
                  + K.angularWeight n * K.tailNormSq Q (fun p => curlComp (fun a b => angularGradMode m n H a b p) i))
          ≤ ∫ p in K.rect, p.1 * curlGradModeSq m n H p

def UnresolvedEnergyStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ),
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H → ∀ n : ℤ,
        ∑ a : Fin 3, ∑ b : Fin 3,
            (K.fullGradWeight (radialGradMode m n H a b) (heightGradMode m n H a b)
              + K.angularWeight n * K.normSqOn K.lineWeightFn (angularGradMode m n H a b))
          ≤ ∫ p in K.rect, p.1 * secondModeSq m n H p

def VelocityTailStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (Q : ℕ), 5 ≤ Q →
    ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsSecondOrderField m v G H → ∀ n : ℤ, ∀ bn : ℝ, 0 ≤ bn →
        bn * ∑ a : Fin 3, K.velocityTail Q (fun p => modeVec m n v p.1 p.2 a)
          ≤ bn * ∑ a : Fin 3, K.topPart Q (gradMode m n G a 0) (gradMode m n G a 2)
            + bn * ∑ a : Fin 3, ∑ b : Fin 3, K.tailNormSq Q (gradMode m n G a b)

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

namespace CellBases

variable (B : CellBases)

end CellBases

def IsTraceFree (s : Fin 3 → Fin 3 → ℂ) : Prop := ∑ a : Fin 3, s a a = 0

def symSq (s : Fin 3 → Fin 3 → ℂ) : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, ‖(s a b + s b a) / 2‖ ^ 2

def antiSq (s : Fin 3 → Fin 3 → ℂ) : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, ‖(s a b - s b a) / 2‖ ^ 2

def sesqValue (A : Matrix (Fin 12) (Fin 12) ℂ) (U : Fin 12 → ℂ) : ℝ :=
  (∑ i, ∑ j, (starRingEnd ℂ) (U i) * A i j * U j).re

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

def turnVec (k : ℝ) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(k : ℂ) * Complex.I * v 0 - v 1, (k : ℂ) * Complex.I * v 1 + v 0, (k : ℂ) * Complex.I * v 2]

def supremumLoss (lam g₀ g' ℓ : ℝ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : ℝ :=
  lam * curlSq s + Exterior.traceFreeConst * g₀ * Real.sqrt (sumSq s) * Real.sqrt (vecSq v)
    + (1 / 2) * Exterior.traceFreeConst * g' * (ℓ * sumSq s + vecSq v / ℓ)

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

def densityForm (α : ℝ) (p : ℝ × ℝ) (s : Fin 3 → Fin 3 → ℂ) : ℝ :=
  (1 - 3 / (4 * α) - c.curlWeight) * curlSq s + (c.curlWeight - c.coercivity * sampleWeight c p) * sumSq s

def pairLoss (n : ℤ) (p : ℝ × ℝ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : ℝ :=
  sesqValue (S.localMatrix n p) (pairVec s v)
    - supremumLoss (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength s v

def penalty (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : ℝ :=
  S.penaltyStrain * sumSq s + S.penaltyCurl * curlSq s + S.penaltyVelocity * vecSq v

end CellScalars

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

structure IsCellScalars (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) : Prop where
  resolved_symm : ∀ n, n ∈ S.resolved ↔ -n ∈ S.resolved
  band_symm : ∀ n, n ∈ S.band ↔ -n ∈ S.band
  zero_resolved : (0 : ℤ) ∈ S.resolved
  disjoint : Disjoint S.resolved S.band
  axis_resolved : K.IsAxis → S.resolved = {0}
  unresolved_large : ∀ n ∉ S.resolved, (3 : ℝ) ≤ modeNumber c.order n
  splitLength_pos : 0 < S.splitLength
  strain_le : ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ∀ θ : ℝ, ∀ u : Space,
    inner ℝ (c.modelStrain (cylPoint p.1 θ p.2) u) u ≤ S.strainBound p * ‖u‖ ^ 2
  data_regular : (∀ n ∈ S.resolved, (∀ i j, Measurable (fun p => S.localMatrix n p i j)) ∧
      ∃ C : ℝ, ∀ p ∈ K.rect, ∀ i j, ‖S.localMatrix n p i j‖ ≤ C) ∧
    (Measurable S.strainBound ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |S.strainBound p| ≤ C) ∧
    (Measurable S.meanGradBound ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |S.meanGradBound p| ≤ C) ∧
    (Measurable S.waveGradBound ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |S.waveGradBound p| ≤ C)
  grad_bounds_nonneg : ∀ p, 0 ≤ S.meanGradBound p ∧ 0 ≤ S.waveGradBound p
  energyWeight_pos : ∀ n, 0 < S.energyWeight n
  energyWeight_le : ∀ n, S.energyWeight n ≤ c.innerWeight - c.coercivity
  vorticityWeight_nonneg : ∀ n, 0 ≤ S.vorticityWeight n
  vorticityWeight_le : ∀ n, S.vorticityWeight n ≤ c.splitVisc - c.innerWeight
  weights_symm : ∀ n, S.energyWeight (-n) = S.energyWeight n ∧ S.vorticityWeight (-n) = S.vorticityWeight n ∧
    S.curlAbsorb (-n) = S.curlAbsorb n ∧ S.strainAbsorb (-n) = S.strainAbsorb n ∧
    S.velocityAbsorb (-n) = S.velocityAbsorb n ∧ S.tailShift (-n) = S.tailShift n
  localMatrix_selfAdjoint : ∀ n p, (S.localMatrix n p).IsHermitian
  localMatrix_le : ∀ n ∈ S.resolved, ∀ p ∈ K.rect, ∀ (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ),
    sesqValue (S.localMatrix n p) (pairVec s v) ≤ CellScalars.densityForm c α p s
  resolved_pointwise : ∀ n ∈ S.resolved, ∀ p ∈ K.rect, p.1 ≠ 0 → ∀ (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ), IsTraceFree s →
    0 ≤ CellScalars.rHat K p * CellScalars.pairLoss S n p s v + S.curlAbsorb n * curlSq s
      + S.strainAbsorb n * sumSq s + S.velocityAbsorb n * vecSq v
  unresolved_pointwise : ∀ n ∉ S.resolved, ∀ p ∈ K.rect, p.1 ≠ 0 → ∀ (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ), IsTraceFree s →
    turnVec (azimuth c.order n) v = (fun a => (p.1 : ℂ) * s a 1) →
    0 ≤ CellScalars.rHat K p * (CellScalars.densityForm c α p s
          - supremumLoss (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength s v
          - (if n ∈ S.band then 0 else S.penalty s v))
      + S.curlAbsorb n * curlSq s + S.strainAbsorb n * sumSq s
  tailShift_nonneg : ∀ n, 0 ≤ S.tailShift n
  tailShift_zero : ∀ n ∉ S.resolved, S.tailShift n = 0
  weightFloor_pos : 0 < S.weightFloor
  sym_weight : ∀ n j l, (n ∉ S.resolved ∨ S.degHigh < max j l) →
    S.weightFloor ≤ S.symWeight n j l ∧
      S.symWeight n j l ≤ S.energyWeight n * (CellScalars.tailLam K j l
        + CellBox.angularWeight K n * (max (modeNumber c.order n - 2) 0) ^ 2) - S.strainAbsorb n - S.tailShift n
  anti_weight : ∀ n j l, (n ∉ S.resolved ∨ S.degHigh < max j l) →
    S.weightFloor ≤ S.antiWeight n j l ∧
      S.antiWeight n j l ≤ (S.energyWeight n + 2 * S.vorticityWeight n) * (CellScalars.tailLam K j l
        + CellBox.angularWeight K n * (max (modeNumber c.order n - 1) 0) ^ 2)
        - 2 * S.curlAbsorb n - S.strainAbsorb n - S.tailShift n
  vel_weight : ∀ n ∈ S.resolved, ∀ j l, S.degHigh ≤ max j l →
    S.weightFloor ≤ S.velWeight n j l ∧
      S.velWeight n j l ≤ S.tailShift n * (if S.degHigh ≤ j then radialEigen K j else heightEigen K l)
        - S.velocityAbsorb n
  degrees : 3 ≤ S.degLow ∧ S.degLow + 2 ≤ S.degHigh ∧ S.degHigh + 1 ≤ S.degNear

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

namespace CellClasses

variable (Cl : CellClasses)

def classLoss (ℓ : ℝ) (i : Fin Cl.count) (p : ℝ × ℝ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) : ℝ :=
  Cl.strainDev i p * curlSq s + (1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p * (ℓ * sumSq s + vecSq v / ℓ)

end CellClasses

namespace CellBox

variable (K : CellBox)

def lowStrain (m : ℕ) (n : ℤ) (Q : ℕ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) : ℝ × ℝ → ℂ :=
  K.proj Q Q (gradMode m n G a b)

def lowVelocity (m : ℕ) (n : ℤ) (Q : ℕ) (v : Space → Space) (a : Fin 3) : ℝ × ℝ → ℂ :=
  K.proj (Q - 1) (Q - 1) (fun p => modeVec m n v p.1 p.2 a)

end CellBox

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

namespace CellBox

variable (K : CellBox)

def lowStrainAt (m : ℕ) (n : ℤ) (Q : ℕ) (G : Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) : Fin 3 → Fin 3 → ℂ :=
  fun a b => K.lowStrain m n Q G a b p

def lowVelocityAt (m : ℕ) (n : ℤ) (Q : ℕ) (v : Space → Space) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun a => K.lowVelocity m n Q v a p

end CellBox

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (Cl : CellClasses)

def pairIntegrand (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (n n' : ℤ) (p : ℝ × ℝ) : ℂ :=
  waveForm (strainMode c (n - n') p) (curlGradMode c (n - n') p) (curlGradMode c (n' - n) p)
      (K.lowStrainAt c.order n S.degHigh G p) (K.lowVelocityAt c.order n S.degHigh v p)
      (K.lowStrainAt c.order n' S.degHigh G p) (K.lowVelocityAt c.order n' S.degHigh v p)
    + (if n = n' then (sesqValue (S.localMatrix n p)
        (pairVec (K.lowStrainAt c.order n S.degHigh G p) (K.lowVelocityAt c.order n S.degHigh v p)) : ℂ) else 0)

def localPairForm (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) : ℝ :=
  (∑ n ∈ S.resolved, ∑ n' ∈ S.resolved,
    ∫ p in K.rect, ((K.lineWeight p.1 * rHat K p : ℝ) : ℂ) * pairIntegrand c K S v G n n' p).re

open Classical in
def classTerm (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ n ∈ S.resolved, ∑ i : Fin Cl.count,
    (if n ∈ Cl.resolvedPart i then Cl.shareWeight i *
      ∫ p in K.rect, p.1 * Cl.classLoss S.splitLength i p (K.lowStrainAt c.order n S.degHigh G p)
        (K.lowVelocityAt c.order n S.degHigh v p) else 0)

def energyTerm (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑ n ∈ S.resolved,
    (S.energyWeight n * K.strainEnergy c.order n S.degHigh S.degLow G H
      + S.vorticityWeight n * K.vorticityEnergy c.order n S.degHigh S.degLow G H
      - S.tailShift n * ∑ a : Fin 3, K.topPart S.degHigh (gradMode c.order n G a 0) (gradMode c.order n G a 2))

def linearTerm (κ ζ : Fin k → ℝ) (G : Space → (Space →L[ℝ] Space)) : ℝ :=
  2 * (∑ n ∈ S.resolved, ∑ i : Fin k,
      ∫ p in K.rect, ((K.lineWeight p.1 * rHat K p : ℝ) : ℂ) *
        (((κ i / 2 : ℝ) : ℂ) * entryPairing (K.lowStrainAt c.order n S.degHigh G p)
            (fun a b => modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b)
          + ((ζ i : ℝ) : ℂ) * entryPairing (K.lowStrainAt c.order n S.degHigh G p)
            (fun a b => modeMat c.order n (c.modelPinField i) p.1 p.2 a b))).re

def localCellForm (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  energyTerm c K S G H - classTerm c K S Cl v G + localPairForm c K S v G + linearTerm c K S κ ζ G

end CellScalars

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

def yStrain (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (n : ℤ) (p : ℝ × ℝ) :
    Fin 3 → Fin 3 → ℂ := fun a b =>
  ((rHat K p : ℝ) : ℂ) *
    ((if n ∈ S.resolved ∪ S.band then ∑ n' ∈ S.resolved, waveActionStrain (strainMode c (n - n') p) (curlGradMode c (n - n') p)
        (K.lowStrainAt c.order n' S.degHigh G p) (K.lowVelocityAt c.order n' S.degHigh v p) a b else 0)
      + (if n ∈ S.resolved then splitStrain (matAct (S.localMatrix n p)
          (pairVec (K.lowStrainAt c.order n S.degHigh G p) (K.lowVelocityAt c.order n S.degHigh v p))) a b else 0)
      + ∑ i : Fin k, (((κ i / 2 : ℝ) : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
          + ((ζ i : ℝ) : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b))

def yVelocity (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (n : ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := fun b =>
  ((rHat K p : ℝ) : ℂ) *
    ((if n ∈ S.resolved ∪ S.band then ∑ n' ∈ S.resolved, waveActionVelocity (curlGradMode c (n' - n) p) (K.lowStrainAt c.order n' S.degHigh G p) b else 0)
      + (if n ∈ S.resolved then splitVelocity (matAct (S.localMatrix n p)
          (pairVec (K.lowStrainAt c.order n S.degHigh G p) (K.lowVelocityAt c.order n S.degHigh v p))) b else 0))

def yFolded (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (n : ℤ) (p : ℝ × ℝ) :
    Fin 3 → Fin 3 → ℂ :=
  if n ∈ S.resolved then yStrain c K S κ ζ v G n p
  else foldVelocity (azimuth c.order n) p.1 (yStrain c K S κ ζ v G n p) (yVelocity c K S v G n p)

def symCoefSq (C : Fin 3 → Fin 3 → ℂ) : ℝ := symSq C

def weightedCoefSum (B : CellBases) (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    {slots : ℕ} (R : CellRows N slots k) (sel : ℕ → ℕ → Prop) [DecidableRel sel] : ℝ :=
  (∑ n ∈ R.yModes, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
    if sel j l ∧ (n ∉ S.resolved ∨ S.degHigh < max j l) then
      symSq (fun a b => B.coef K (fun p => yFolded c K S κ ζ v G n p a b) j l) / S.symWeight n j l
        + antiSq (fun a b => B.coef K (fun p => yFolded c K S κ ζ v G n p a b) j l) / S.antiWeight n j l
    else 0)
  + ∑ n ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
    if sel j l ∧ S.degHigh ≤ max j l then
      vecSq (fun a => B.coef K (fun p => yVelocity c K S v G n p a) j l) / S.velWeight n j l
    else 0

def nearWeighted (B : CellBases) (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    {slots : ℕ} (R : CellRows N slots k) : ℝ :=
  weightedCoefSum c K S B κ ζ v G R (fun _ _ => True)

def farWeighted (B : CellBases) (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    {slots : ℕ} (R : CellRows N slots k) : ℝ :=
  ∑' jl : ℕ × ℕ,
    (if S.degNear < max jl.1 jl.2 then
      (∑ n ∈ R.yModes, if (n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2) then
        symSq (fun a b => B.coef K (fun p => yFolded c K S κ ζ v G n p a b) jl.1 jl.2) / S.symWeight n jl.1 jl.2
          + antiSq (fun a b => B.coef K (fun p => yFolded c K S κ ζ v G n p a b) jl.1 jl.2) / S.antiWeight n jl.1 jl.2
        else 0)
      + ∑ n ∈ S.resolved,
          vecSq (fun a => B.coef K (fun p => yVelocity c K S v G n p a) jl.1 jl.2) / S.velWeight n jl.1 jl.2
    else 0)

end CellScalars

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

namespace CellScalars

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)

def mirrorSign (y : Space) (a : Fin 3) : ℝ := if cylHeight y < 0 ∧ a = 2 then -1 else 1

def lowVelocityField (v : Space → Space) (y : Space) : Space :=
  cartOfFrame (cylAngle y) (fun a => mirrorSign y a * (∑ n ∈ S.resolved,
    K.lowVelocity c.order n S.degHigh v a (cylRadius y, |cylHeight y|) *
      Complex.exp ((azimuth c.order n * cylAngle y : ℝ) * Complex.I)).re)

def lowGradField (G : Space → (Space →L[ℝ] Space)) (y : Space) : Space →L[ℝ] Space :=
  cartOpOfFrame (cylAngle y) (fun a b => mirrorSign y a * mirrorSign y b * (∑ n ∈ S.resolved,
    K.lowStrain c.order n S.degHigh G a b (cylRadius y, |cylHeight y|) *
      Complex.exp ((azimuth c.order n * cylAngle y : ℝ) * Complex.I)).re)

def highCouplingField (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (y : Space) : Space :=
  crossVec (curlOf (G y - lowGradField c K S G y)) (c.modelVelocity y)
    + crossVec (c.modelCurl y) (v y - lowVelocityField c K S v y)

variable {slots : ℕ} (R : CellRows N slots k)

def vecPair (x y : Fin 3 → ℂ) : ℂ := ∑ a : Fin 3, x a * (starRingEnd ℂ) (y a)

def rowYPair (B : CellBases) (κ ζ : Fin k → ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (a : Fin N) : ℝ :=
  ((∑ n' ∈ S.resolved ∪ S.band, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
    if (n' ∉ S.resolved ∨ S.degHigh < max j l) then
      sigmaWeightedPair (fun i q => B.coef K (fun p => rowCouplingFolded c K S R a n' p i q) j l)
        (fun i q => B.coef K (fun p => yFolded c K S κ ζ v G n' p i q) j l)
        (S.symWeight n' j l) (S.antiWeight n' j l)
    else 0)
  + ∑ n' ∈ S.resolved, ∑ j ∈ Finset.range (S.degNear + 1), ∑ l ∈ Finset.range (S.degNear + 1),
    if S.degHigh ≤ max j l then
      vecPair (fun i => B.coef K (fun p => yVelocity c K S v G n' p i) j l)
        (fun i => B.coef K (fun p => rowCouplingVelocity c K R a n' p i) j l) / (S.velWeight n' j l : ℂ)
    else 0).re

def rowSquareFar (B : CellBases) (μ : Fin N → ℝ) : ℝ :=
  ∑' jl : ℕ × ℕ, if S.degNear < max jl.1 jl.2 then
    (∑ n' ∈ S.resolved ∪ S.band,
      (sigmaWeightedPair
        (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingFolded c K S R a n' p i q) jl.1 jl.2)
        (fun i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingFolded c K S R a n' p i q) jl.1 jl.2)
        (S.symWeight n' jl.1 jl.2) (S.antiWeight n' jl.1 jl.2)).re)
    + ∑ n' ∈ S.resolved,
      vecSq (fun i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => rowCouplingVelocity c K R a n' p i) jl.1 jl.2)
        / S.velWeight n' jl.1 jl.2
  else 0

def lowRowValue (α : ℝ) (x : FieldTuple k) (a : Fin N) : ℝ :=
  (l2Pair (fun y => c.modelFieldOf α x.1 x.2.1 x.2.2.1 x.2.2.2.1 y + x.2.2.2.2 y) (c.row a)
    - l2Pair (highCouplingField c K S x.1 x.2.1) (c.row a)) / (4 * Real.pi)

def lowCoef (B : CellBases) (x : FieldTuple k) (i : ℤ × Fin 3 × Fin 4 × ℕ × ℕ) : ℂ :=
  if h : i.2.2.1.val < 3 then
    B.coef K (fun p => K.lowStrainAt c.order i.1 S.degHigh x.2.1 p i.2.1 ⟨i.2.2.1.val, h⟩) i.2.2.2.1 i.2.2.2.2
  else B.coef K (fun p => K.lowVelocityAt c.order i.1 S.degHigh x.1 p i.2.1) i.2.2.2.1 i.2.2.2.2

def farVector (B : CellBases) (x : FieldTuple k) (ζ : Fin k → ℝ) :
    (ℤ × Fin 3 × Fin 4 × ℕ × ℕ) ⊕ (Fin k ⊕ Fin k) → ℂ :=
  Sum.elim (lowCoef c K S B x) (Sum.elim (fun i => ((x.2.2.2.1 i : ℝ) : ℂ)) (fun i => ((ζ i : ℝ) : ℂ)))

def farFormValue (B : CellBases) (x : FieldTuple k) (ζ : Fin k → ℝ) : ℝ :=
  (∑ i ∈ R.farSupport.disjSum Finset.univ, ∑ i' ∈ R.farSupport.disjSum Finset.univ,
    (starRingEnd ℂ) (farVector c K S B x ζ i) * R.farKernel i i' * farVector c K S B x ζ i').re

def rowResidual (α : ℝ) (B : CellBases) (x : FieldTuple k) (ζ : Fin k → ℝ) (a : Fin N) : ℝ :=
  lowRowValue c K S α x a - rowYPair c K S R B x.2.2.2.1 ζ x.1 x.2.1 a

def cellForm (α : ℝ) (B : CellBases) (Cl : CellClasses) (x : FieldTuple k) (ζ : Fin k → ℝ) : ℝ :=
  localCellForm c K S Cl x.2.2.2.1 ζ x.1 x.2.1 x.2.2.1
    - nearWeighted c K S B x.2.2.2.1 ζ x.1 x.2.1 R
    - farFormValue c K S R B x ζ / R.farShare
    + ∑ b : Fin R.reducerCount, (∑ a ∈ R.rowSet, R.reducer b a * rowResidual c K S R α B x ζ a) ^ 2

end CellScalars

end CellAnalysis


namespace CellAnalysis

open SteadyCert Assembly

structure IsCellData (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)
    (Cl : CellClasses) {slots : ℕ} (R : CellRows N slots k) : Prop where
  box : IsCellBox K
  scalars : IsCellScalars α c K S
  bases : IsCellBases K B
  weight_axisymmetric : ∀ p ∈ K.rect, ∀ θ : ℝ, c.weight (cylPoint p.1 θ p.2) = CellScalars.sampleWeight c p
  model_mirror : ∀ y ∈ K.solid, cylHeight y ≠ 0 → c.modelVelocity (mirror y) = mirror (c.modelVelocity y) ∧
    c.modelCurl (mirror y) = -mirror (c.modelCurl y) ∧
    (∀ u, c.modelStrain (mirror y) u = mirror (c.modelStrain y (mirror u))) ∧
    (∀ u, c.modelCurlGrad (mirror y) u = -mirror (c.modelCurlGrad y (mirror u))) ∧
    ∀ i, (∀ u, c.modelActuatorGrad i (mirror y) u = mirror (c.modelActuatorGrad i y (mirror u))) ∧
      (∀ u, c.modelPinField i (mirror y) u = mirror (c.modelPinField i y (mirror u)))
  solid_in_region : K.solid ⊆ c.cellRegion
  model_strain_symm : ∀ y (u w : Space), inner ℝ (c.modelStrain y u) w = inner ℝ u (c.modelStrain y w)
  actuator_memLp : ∀ i, MemLp (c.modelActuator i) 2 volume
  mean_le : ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → OpBound (modeMat c.order 0 c.modelCurlGrad p.1 p.2) (S.meanGradBound p)
  wave_le : ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ∀ θ : ℝ, OpBound (fun a b => (frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) a b : ℂ)
    - modeMat c.order 0 c.modelCurlGrad p.1 p.2 a b) (S.waveGradBound p)
  curlGrad_traceFree : ∀ p ∈ K.rect, p.1 ≠ 0 → ∀ θ : ℝ, ∑ i : Fin 3, entry (c.modelCurlGrad (cylPoint p.1 θ p.2)) i i = 0
  class_regular : ∀ i, Measurable (Cl.strainDev i) ∧ Measurable (Cl.gradDev i) ∧ Measurable (Cl.velocityDev i) ∧
    Measurable (Cl.curlDev i) ∧ ∃ C : ℝ, ∀ p ∈ K.rect, |Cl.strainDev i p| ≤ C ∧ |Cl.gradDev i p| ≤ C ∧
      |Cl.velocityDev i p| ≤ C ∧ |Cl.curlDev i p| ≤ C
  yModes_contain : S.resolved ∪ S.band ⊆ R.yModes
  linear_modes : ∀ n ∉ R.yModes, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ∀ i,
    modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 = 0 ∧ modeMat c.order n (c.modelPinField i) p.1 p.2 = 0
  rows_in_cell : ∀ a ∈ R.rowSet, ∀ y ∉ K.solid, c.row a y = 0
  row_modes : ∀ a ∈ R.rowSet, ∀ n ∉ R.rowModes, ∀ p ∈ K.rect, CellScalars.rowMode c a n p = 0
  row_mode_of : ∀ a ∈ R.rowSet, ∀ n, n ≠ R.rowModeOf a → n ≠ -R.rowModeOf a → ∀ p ∈ K.rect,
    CellScalars.rowMode c a n p = 0
  row_mode_resolved : ∀ a ∈ R.rowSet, R.rowModeOf a ∈ S.resolved
  rowWeight_pos : ∀ a ∈ R.rowSet, 0 < c.rowWeight a
  class_modes_symm : ∀ i n, n ∈ Cl.modes i ↔ -n ∈ Cl.modes i
  class_disjoint : ∀ i j, i ≠ j → Disjoint (Cl.modes i) (Cl.modes j)
  class_cover : ∀ n ∈ S.resolved, ∀ n' ∉ S.resolved ∪ S.band,
    (∃ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 ∧ (modeVec c.order (n - n') c.modelVelocity p.1 p.2 ≠ 0 ∨
      modeVec c.order (n - n') c.modelCurl p.1 p.2 ≠ 0 ∨
      modeMat c.order (n - n') c.modelStrain p.1 p.2 ≠ 0 ∨ modeMat c.order (n - n') c.modelCurlGrad p.1 p.2 ≠ 0)) →
    ∃ i, n - n' ∈ Cl.modes i
  class_resolved : ∀ i, Cl.resolvedPart i ⊆ S.resolved
  class_resolved_cover : ∀ i, ∀ n ∈ S.resolved, (∃ n' ∉ S.resolved ∪ S.band, n - n' ∈ Cl.modes i) →
    n ∈ Cl.resolvedPart i
  class_weights_pos : ∀ i, 0 < Cl.shareWeight i ∧ 0 < Cl.rowWeight i
  class_bounds : ∀ i, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → ∀ θ : ℝ,
    OpBound (classField c.order (Cl.modes i) c.modelStrain p θ) (Cl.strainDev i p) ∧
    OpBound (classField c.order (Cl.modes i) c.modelCurlGrad p θ) (Cl.gradDev i p) ∧
    vecSq (classVec c.order (Cl.modes i) c.modelVelocity p θ) ≤ Cl.velocityDev i p ^ 2 ∧
    vecSq (classVec c.order (Cl.modes i) c.modelCurl p θ) ≤ Cl.curlDev i p ^ 2
  class_devs_nonneg : ∀ i p, 0 ≤ Cl.strainDev i p ∧ 0 ≤ Cl.gradDev i p ∧ 0 ≤ Cl.velocityDev i p ∧ 0 ≤ Cl.curlDev i p
  penalty_ge : ∀ p ∈ K.rect,
    (∑ i, (1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p * S.splitLength / Cl.shareWeight i) ≤ S.penaltyStrain ∧
    (∑ i, (Cl.strainDev i p / Cl.shareWeight i + 2 * Cl.rowWeight i * Cl.velocityDev i p ^ 2)) ≤ S.penaltyCurl ∧
    (∑ i, ((1 / 2) * Exterior.traceFreeConst * Cl.gradDev i p / (S.splitLength * Cl.shareWeight i)
      + 2 * Cl.rowWeight i * Cl.curlDev i p ^ 2)) ≤ S.penaltyVelocity
  farShare_mem : 0 < R.farShare ∧ R.farShare < 1
  multiplier_symm : R.multiplierMatrix.IsSymm
  multiplier_rows : ∀ a b, (a ∉ R.rowSet ∨ b ∉ R.rowSet) → R.multiplierMatrix a b = 0
  multiplier_bound : ∀ μ : Fin N → ℝ, (∀ a ∉ R.rowSet, μ a = 0) →
    (∑ a ∈ R.rowSet, μ a ^ 2 / (4 * Real.pi * c.rowWeight a)) + (∑ a ∈ R.rowSet, R.classRowWeight a * μ a ^ 2)
        + CellScalars.rowSquare c K S R B μ (fun _ _ => True)
        + CellScalars.rowSquareFar c K S R B μ / (1 - R.farShare)
      ≤ ∑ a ∈ R.rowSet, ∑ b ∈ R.rowSet, μ a * R.multiplierMatrix a b * μ b
  classRowWeight_ge : ∀ a ∈ R.rowSet,
    (∑ i, if R.rowModeOf a ∈ Cl.resolvedPart i then 1 / (4 * Real.pi * Cl.rowWeight i) else 0) ≤ R.classRowWeight a
  far_bound : ∀ x : FieldTuple k, IsAdmissible c x → ∀ ζ : Fin k → ℝ,
    CellScalars.farWeighted c K S B x.2.2.2.1 ζ x.1 x.2.1 R ≤ CellScalars.farFormValue c K S R B x ζ
  reducer_bound : ∀ w : Fin R.reducerCount → ℝ,
    (∑ a ∈ R.rowSet, ∑ b ∈ R.rowSet, (∑ i, R.reducer i a * w i) * R.multiplierMatrix a b * (∑ i, R.reducer i b * w i))
      ≤ ∑ i, w i ^ 2

end CellAnalysis

end CellCert

end Breakdown
