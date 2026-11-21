import Breakdown.FracCell.CellDataDefs
import Breakdown.FracCell.FormulaDataDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert Assembly CellAnalysis

def OrthoFamilyStatement : Prop :=
  ∀ (w : ℝ → ℝ) (a b : ℝ), a < b → Measurable w → (∀ x ∈ Set.Icc a b, 0 ≤ w x) →
    (∀ x ∈ Set.Ioo a b, 0 < w x) → ContinuousOn w (Set.Icc a b) →
    ∀ n, (orthoFamily w a b n).natDegree = n ∧ 0 < (orthoFamily w a b n).coeff n ∧
      ∀ n', polyPair w a b (orthoFamily w a b n) (orthoFamily w a b n') = if n = n' then 1 else 0

def ExtendBasesStatement : Prop :=
  ∀ (K : CellBox) (D : ℕ) (B₀ : CellBases), IsCellBox K → IsGivenBases K D B₀ →
    IsCellBases K (extendBases K D B₀) ∧
      (∀ j ≤ D, ∀ i, (extendBases K D B₀).radialCoef j i = B₀.radialCoef j i) ∧
      (∀ l ≤ D, ∀ i, (extendBases K D B₀).heightCoef l i = B₀.heightCoef l i)

open Classical in
def extendSegment (S : CellFormula.FaceSegment) (D : ℕ) : CellFormula.FaceSegment :=
  { S with testCoef := fun d i => if d ≤ D then S.testCoef d i else
      (orthoFamily (fun _ => 1) S.lo S.hi d).coeff i }

def ExtendSegmentStatement : Prop :=
  ∀ (S : CellFormula.FaceSegment) (D : ℕ), S.lo < S.hi → S.other ≠ S.level →
    (∀ d ≤ D, S.testCoef d d ≠ 0) →
    CellFormula.IsFaceSegment (extendSegment S D) ∧ ∀ d ≤ D, ∀ i, (extendSegment S D).testCoef d i = S.testCoef d i

namespace WeightData

variable (W : WeightData)

end WeightData

def WeightClausesStatement : Prop :=
  ∀ (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (W : WeightData),
    IsCellBox K → IsWeightForm c K S W → IsWeightTests α c K S W →
      (∀ n ∉ S.resolved, (3 : ℝ) ≤ modeNumber c.order n) ∧
      (∀ n, 0 < S.energyWeight n) ∧ (∀ n, S.energyWeight n ≤ c.innerWeight - c.coercivity) ∧
      (∀ n, 0 ≤ S.vorticityWeight n) ∧ (∀ n, S.vorticityWeight n ≤ c.splitVisc - c.innerWeight) ∧
      (∀ n, S.energyWeight (-n) = S.energyWeight n ∧ S.vorticityWeight (-n) = S.vorticityWeight n ∧
        S.curlAbsorb (-n) = S.curlAbsorb n ∧ S.strainAbsorb (-n) = S.strainAbsorb n ∧
        S.velocityAbsorb (-n) = S.velocityAbsorb n ∧ S.tailShift (-n) = S.tailShift n) ∧
      (∀ n, 0 ≤ S.tailShift n) ∧ (∀ n ∉ S.resolved, S.tailShift n = 0) ∧
      (∀ n j l, (n ∉ S.resolved ∨ S.degHigh < max j l) →
        S.weightFloor ≤ S.symWeight n j l ∧
          S.symWeight n j l ≤ S.energyWeight n * (CellScalars.tailLam K j l
            + CellBox.angularWeight K n * (max (modeNumber c.order n - 2) 0) ^ 2) - S.strainAbsorb n - S.tailShift n) ∧
      (∀ n j l, (n ∉ S.resolved ∨ S.degHigh < max j l) →
        S.weightFloor ≤ S.antiWeight n j l ∧
          S.antiWeight n j l ≤ (S.energyWeight n + 2 * S.vorticityWeight n) * (CellScalars.tailLam K j l
            + CellBox.angularWeight K n * (max (modeNumber c.order n - 1) 0) ^ 2)
            - 2 * S.curlAbsorb n - S.strainAbsorb n - S.tailShift n) ∧
      (∀ n ∈ S.resolved, ∀ j l, S.degHigh ≤ max j l →
        S.weightFloor ≤ S.velWeight n j l ∧
          S.velWeight n j l ≤ S.tailShift n * (if S.degHigh ≤ j then radialEigen K j else heightEigen K l)
            - S.velocityAbsorb n)

def UnresolvedPointwiseStatement : Prop :=
  ∀ (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (W : WeightData),
    IsCellBox K → IsWeightForm c K S W → IsWeightTests α c K S W →
    ∀ n ∉ S.resolved, ∀ p ∈ K.rect, p.1 ≠ 0 → ∀ (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ), IsTraceFree s →
      turnVec (azimuth c.order n) v = (fun a => (p.1 : ℂ) * s a 1) →
      0 ≤ CellScalars.rHat K p * (CellScalars.densityForm c α p s
            - supremumLoss (S.strainBound p) (S.meanGradBound p) (S.waveGradBound p) S.splitLength s v
            - (if n ∈ S.band then 0 else S.penalty s v))
        + S.curlAbsorb n * curlSq s + S.strainAbsorb n * sumSq s

def ResolvedPointwiseStatement : Prop :=
  ∀ (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (W : WeightData) (aS lowConst : ℝ),
    IsCellBox K → IsWeightForm c K S W → IsWeightTests α c K S W → IsResolvedTests α c S W aS lowConst →
      (∀ n ∈ S.resolved, ∀ p ∈ K.rect, ∀ (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ),
        sesqValue (S.localMatrix n p) (pairVec s v) ≤ CellScalars.densityForm c α p s) ∧
      ∀ n ∈ S.resolved, ∀ p ∈ K.rect, p.1 ≠ 0 → ∀ (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ), IsTraceFree s →
        0 ≤ CellScalars.rHat K p * CellScalars.pairLoss S n p s v + S.curlAbsorb n * curlSq s
          + S.strainAbsorb n * sumSq s + S.velocityAbsorb n * vecSq v

structure ModelModes {k N : ℕ} (c : FracCellData k N) (K : CellBox) where
  support : Finset ℤ
  vanish : ∀ d ∉ support, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 → modeVec c.order d c.modelVelocity p.1 p.2 = 0 ∧
    modeVec c.order d c.modelCurl p.1 p.2 = 0 ∧ modeMat c.order d c.modelStrain p.1 p.2 = 0 ∧
    modeMat c.order d c.modelCurlGrad p.1 p.2 = 0

def ClassCoverStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (Cl : CellClasses) (M : ModelModes c K),
    (∀ d ∈ M.support, (∃ n ∈ S.resolved, n - d ∉ S.resolved ∪ S.band) → ∃ i, d ∈ Cl.modes i) →
    ∀ n ∈ S.resolved, ∀ n' ∉ S.resolved ∪ S.band,
      (∃ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 ∧ (modeVec c.order (n - n') c.modelVelocity p.1 p.2 ≠ 0 ∨
        modeVec c.order (n - n') c.modelCurl p.1 p.2 ≠ 0 ∨
        modeMat c.order (n - n') c.modelStrain p.1 p.2 ≠ 0 ∨ modeMat c.order (n - n') c.modelCurlGrad p.1 p.2 ≠ 0)) →
      ∃ i, n - n' ∈ Cl.modes i

end Reduction

end CellCert

end Breakdown
